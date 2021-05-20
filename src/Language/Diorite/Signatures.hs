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

import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)

--------------------------------------------------------------------------------
-- * Signatures.
--------------------------------------------------------------------------------

-- | Signature of a symbol.
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

-- | Valid symbol signatures.
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

result :: SigRep sig -> Proxy (Result sig)
result (SigConst)    = Proxy
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
testSig a1@(SigConst) a2@(SigConst)
    | Just Refl <- testConst a1 a2
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

-- | Any witness of a symbol signature is a valid symbol signature.
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred _ a) | Dict <- witSig a = Dict

-- | Any witness of a constant symbol signature is typeable.
witTypeable :: SigRep ('Const a) -> Dict (Typeable a)
witTypeable (SigConst) = Dict

--------------------------------------------------------------------------------
-- Fin.
