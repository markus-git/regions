{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Annotation
    (
    -- * ...
      Put(..)
    , Annotation(..)
    , Strip
    , Erasure
    , (:~~:)(..)
    -- ** ...
    , AnnRep(..)
    , Ann(..)
    , strip
    , erase
    , testAnn
    -- * ...
    , Rgn(..)
    , local
    ) where

import Language.Diorite.Syntax (Signature, SigRep, Qual, (:-), Minus, Beta)
import qualified Language.Diorite.Syntax as S

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

-- | ...
type family Strip (ann :: Annotation * *) :: Signature (Put *) * where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

-- | ...
type family Erasure (sig :: S.Signature (Put *) *) :: Signature (Put *) * where
    Erasure ('S.Const a) = 'S.Const a
    Erasure (a 'S.:-> b) = Erasure a 'S.:-> Erasure b
    Erasure (_ 'S.:=> a) = Erasure a

-- | Witness of equality under "Erasure".
newtype sig :~~: ann = Erased (sig :~: Erasure (Strip ann))

infixr :~~:

--------------------------------------------------------------------------------
-- ** ...
  
-- | ...
data AnnRep (ann :: Annotation * *) where
    AnnConst :: Typeable a => AnnRep ('Const a)
    AnnPart  :: AnnRep a -> AnnRep ann -> AnnRep (a ':-> ann)
    AnnPred  :: Typeable r => Proxy ('Put r) -> AnnRep ann -> AnnRep ('Put r ':=> ann)
    AnnAt    :: AnnRep ann -> AnnRep (ann ':^ r)

-- | ...
class Ann (ann :: Annotation * *) where
    annotation :: AnnRep ann

instance Typeable a => Ann ('Const a) where
    annotation = AnnConst

instance (Ann a, Ann ann) => Ann (a ':-> ann) where
    annotation = AnnPart annotation annotation

instance (Typeable r, Ann ann) => Ann ('Put r ':=> ann) where
    annotation = AnnPred Proxy annotation

instance Ann ann => Ann (ann ':^ r) where
    annotation = AnnAt annotation

-- | ...
strip :: AnnRep ann -> SigRep (Strip ann)
strip (AnnConst)    = S.SigConst
strip (AnnPart a b) = S.SigPart (strip a) (strip b)
strip (AnnPred p a) = S.SigPred p (strip a)
strip (AnnAt a)     = strip a

-- | ...
erase :: S.SigRep sig -> SigRep (Erasure sig)
erase (S.SigConst)    = S.SigConst
erase (S.SigPart a b) = S.SigPart (erase a) (erase b)
erase (S.SigPred _ a) = erase a

-- | ...
testAnn :: SigRep a -> AnnRep b -> Maybe (a :~~: b)
testAnn sig ann | Just Refl <- S.testSig sig (erase (strip ann)) = Just (Erased Refl)
testAnn _ _ = Nothing

{-
(|~) :: Maybe (a :~~: b) -> (a ~ Erasure b => Maybe c) -> Maybe c
(|~) m a = do (Erased Refl) <- m;  a
  -- note: 'Erasure' being a type family seems to prevent a 'HasDict' instance.

infixr |~
-}

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

data Rgn a where
    Local :: Rgn (('Put r 'S.:=> a) 'S.:-> a) -- Matched by ev. abs.
    At    :: Rgn (a 'S.:-> a)                 -- Only effect is in ann. type?

-- | ...
local :: forall sym qs r a . (Qual qs, qs :- 'Put r, Rgn S.:<: sym)
    => Proxy r
    -> Beta sym qs ('S.Const a)
    -> Beta sym (Minus qs ('Put r)) ('S.Const a)
local Proxy beta = lsym S.:$ S.elam (const (S.Spine beta))
  where
    lsym :: Beta sym 'S.None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    lsym = S.inj Local

--------------------------------------------------------------------------------
-- Fin.
