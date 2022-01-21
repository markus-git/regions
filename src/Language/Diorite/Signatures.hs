{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}

module Language.Diorite.Signatures
    (
    -- * Signatures.
      Signature(..)
    , Result
    , Erasure
    , SigRep(..)
    , Sig(..)
    -- ** ...
    , result
    , erase
    -- ** ...
    , testSig
    , witSig
    , witTypeable
    ) where

import Data.Constraint (Dict(..), Constraint)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)

--------------------------------------------------------------------------------
-- * Signatures.
--------------------------------------------------------------------------------

-- | Signature of a symbol.
type Signature :: * -> * -> *
data Signature p a =
      Const a
    | Signature p a :-> Signature p a
    | p :=> Signature p a

infixr 2 :->, :=>

-- | Denotational result of a symbol's signature.
type Result :: forall p . Signature p * -> *
type family Result sig where
    Result ('Const a) = a
    Result (_ ':-> b) = Result b
    Result (_ ':=> a) = Result a

-- | The "erasure" of a symbol's signature removes all of its qualifiers.
type Erasure :: forall p . Signature p * -> Signature p *
type family Erasure sig  where
    Erasure ('Const a) = 'Const a
    Erasure (a ':-> b) = Erasure a ':-> Erasure b
    Erasure (_ ':=> a) = Erasure a

--------------------------------------------------------------------------------
-- ** Rep. of a valid signature.

-- | Witness of a symbol signature.
type SigRep :: forall p . Signature p * -> *
data SigRep sig where
    SigConst :: Typeable a => SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Typeable p => Proxy p -> SigRep sig -> SigRep (p ':=> sig)
-- note: 'Typeable' leaks through 'Sig' which is annoying...

-- | Valid symbol signatures.
type  Sig :: forall p . Signature p * -> Constraint
class Sig sig where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance (Typeable p, Sig sig) => Sig (p ':=> sig) where
    signature = SigPred Proxy signature

--------------------------------------------------------------------------------
-- ** ...

result :: SigRep sig -> SigRep ('Const (Result sig))
result (SigConst)    = SigConst
result (SigPart _ b) = result b
result (SigPred _ a) = result a

erase :: SigRep sig -> SigRep (Erasure sig)
erase (SigConst)    = SigConst
erase (SigPart a b) = SigPart (erase a) (erase b)
erase (SigPred _ a) = erase a

--------------------------------------------------------------------------------
-- ** ...

-- | Extract a witness of equality of two constant types.
testConst :: SigRep ('Const a) -> SigRep ('Const b) -> Maybe (a :~: b)
testConst SigConst SigConst = eqT

-- | Extract a witness of equality of two types.
testSig :: SigRep a -> SigRep b -> Maybe (a :~: b)
testSig a@(SigConst) b@(SigConst)
    | Just Refl <- testConst a b
    = Just Refl
testSig (SigPart a1 b1) (SigPart a2 b2)
    | Just Refl <- testSig a1 a2
    , Just Refl <- testSig b1 b2
    = Just Refl
testSig (SigPred (_ :: Proxy x) a1) (SigPred (_ :: Proxy y) a2)
    | Just Refl <- eqT :: Maybe (x :~: y)
    , Just Refl <- testSig a1 a2
    = Just Refl
testSig _ _ = Nothing
-- todo: I never use this function? If I could remove it I could maybe also get
-- rid of the 'Typeable' constraint for 'SigConst' and in turn 'Sig', that would
-- save the user from having to put 'Typeable' everywhere for symbols...

-- | Any rep. of a symbol signature is a valid symbol signature.
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred _ a) | Dict <- witSig a = Dict

-- | Any rep. of a constant symbol type is typeable.
witTypeable :: SigRep ('Const a) -> Dict (Typeable a)
witTypeable (SigConst) = Dict

--------------------------------------------------------------------------------
-- Fin.
