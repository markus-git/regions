{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Annotation
    (
    -- * ...
      Put(..)
    , Annotation(..)
    , Strip
    , (:~~:)(..)
    -- ** ...
    , AnnRep(..)
    , Ann(..)
    , strip'
    -- **
    , testAnn
    ) where

import Language.Diorite.Signatures
    (Signature, Erasure, SigRep(..), erase', testSig)
import qualified Language.Diorite.Signatures as S (Signature(..))

import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | "Put" predicate, asserts that region 'r' is allocated.
data Put r = Put r

-- | Signature annotated with regions.
data Annotation r a =
         Const a
       | Annotation r a :-> Annotation r a
       | Put r :=> Annotation r a
       | Annotation r a :^ r

infixr 2 :->, :=>
infixl 1 :^

-- | The original symbol's signature is found after stripping its annotations.
type family Strip (ann :: Annotation * *) :: Signature (Put *) * where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype sig :~~: ann = Erased (sig :~: Erasure (Strip ann))

infixr :~~:

--------------------------------------------------------------------------------
-- ** ...

type AnnRep :: Annotation * * -> *
data AnnRep ann where
    AnnConst :: Typeable a => AnnRep ('Const a)
    AnnPart  :: AnnRep a -> AnnRep sig -> AnnRep (a ':-> sig)
    AnnPred  :: Typeable r => Proxy ('Put r) -> AnnRep sig -> AnnRep ('Put r ':=> sig)
    AnnAt    :: AnnRep sig -> AnnRep (sig ':^ r)

class Ann ann where
    annotation :: AnnRep ann

instance Typeable a => Ann ('Const a) where
    annotation = AnnConst

instance (Ann a, Ann sig) => Ann (a ':-> sig) where
    annotation = AnnPart annotation annotation

instance (Typeable r, Ann sig) => Ann ('Put r ':=> sig) where
    annotation = AnnPred Proxy annotation

instance Ann sig => Ann (sig ':^ r) where
    annotation = AnnAt annotation

--------------------------------------------------------------------------------
-- ** Implementation of ...

strip' :: AnnRep ann -> SigRep (Strip ann)
strip' (AnnConst)    = SigConst
strip' (AnnPart a b) = SigPart (strip' a) (strip' b)
strip' (AnnPred p a) = SigPred p (strip' a)
strip' (AnnAt a)     = strip' a

--------------------------------------------------------------------------------
-- ** ...

testAnn :: SigRep a -> AnnRep b -> Maybe (a :~~: b)
testAnn sig ann | Just Refl <- testSig sig (erase' (strip' ann)) = Just (Erased Refl)
testAnn _ _ = Nothing

-- note: 'Erasure' being a type family seems to prevent a 'HasDict' instance.
-- (|~) :: Maybe (a :~~: b) -> (a ~ Erasure b => Maybe c) -> Maybe c
-- (|~) m a = do (Erased Refl) <- m;  a
-- infixr |~

--------------------------------------------------------------------------------
-- Fin.
