{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Labels
    (
    -- * ...
      Put(..)
    , Label(..)
    , Strip
    , (:~~:)(..)
    -- ** ...
    , LblRep(..)
    , Lbl(..)
    , strip
    -- **
--    , testLbl
    ) where

import Language.Diorite.Signatures (Signature, Erasure, SigRep(..), erase, testSig)
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
data Label r a =
         Const a
       | Label r a :-> Label r a
       | Put r :=> Label r a
       | Label r a :^ r

infixr 2 :->, :=>
infixl 1 :^

-- | The original symbol's signature is found after stripping its annotations.
type family Strip (sig :: Label * *) :: Signature (Put *) * where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype sig :~~: lbl = Stripped (sig :~: Strip lbl)

infixr :~~:

--------------------------------------------------------------------------------
-- ** ...

type LblRep :: Label * * -> *
data LblRep sig where
    LblConst :: Typeable a => LblRep ('Const a)
    LblPart  :: LblRep a -> LblRep sig -> LblRep (a ':-> sig)
    LblPred  :: Typeable r => Proxy ('Put r) -> LblRep sig -> LblRep ('Put r ':=> sig)
    LblAt    :: LblRep sig -> LblRep (sig ':^ r)

class Lbl sig where
    label :: LblRep sig

instance Typeable a => Lbl ('Const a) where
    label = LblConst

instance (Lbl a, Lbl sig) => Lbl (a ':-> sig) where
    label = LblPart label label

instance (Typeable r, Lbl sig) => Lbl ('Put r ':=> sig) where
    label = LblPred Proxy label

instance Lbl sig => Lbl (sig ':^ r) where
    label = LblAt label

--------------------------------------------------------------------------------
-- ** Implementation of ...

strip :: LblRep sig -> SigRep (Strip sig)
strip (LblConst)    = SigConst
strip (LblPart a b) = SigPart (strip a) (strip b)
strip (LblPred p a) = SigPred p (strip a)
strip (LblAt a)     = strip a

--------------------------------------------------------------------------------
-- ** ...

-- testLbl :: SigRep a -> LblRep b -> Maybe (a :~~: b)
-- testLbl sig lbl | Just Refl <- testSig sig (strip lbl) = Just (Refl)
-- testLbl _ _ = Nothing

-- note: 'Erasure' being a type family seems to prevent a 'HasDict' instance.
-- (|~) :: Maybe (a :~~: b) -> (a ~ Erasure b => Maybe c) -> Maybe c
-- (|~) m a = do (Erased Refl) <- m;  a
-- infixr |~

--------------------------------------------------------------------------------
-- Fin.
