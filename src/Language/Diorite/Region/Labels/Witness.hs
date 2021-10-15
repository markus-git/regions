{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE EmptyCase #-}

module Language.Diorite.Region.Labels.Witness where

import Language.Diorite.Qualifiers (type (:/~:), type (==))
--import Language.Diorite.Region.Labels

import Data.Proxy (Proxy(..))
import Data.Type.Equality (type (:~:)(..), gcastWith)
import Numeric.Natural (Natural)
import qualified Data.Type.Equality as T (type (==))
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

import GHC.TypeNats

import Prelude hiding (pred)

--------------------------------------------------------------------------------
-- Presburger seems to only work with the '==' type from 'Data.Type.Equality',
-- which I can't seem to use with Qualifiers. While I could say something like
--   (:/~:) === (a T.== b ~ 'False, a T.=== b ~ 'False, a Q.== b ~ 'False),
-- I feel like this approach is easier than rewriting Q & Q.Witness... but maybe
-- its better to simply use 'T.==' in the long run.
--
-- The difference between the two is the extra application rule for 'T.==',
-- which neither witnesses from Q nor these rely on ('Succ a' = 'a + 1' is
-- handled by the Presburger plugin).
--
-- todo: Try again with 'Data.Type.Equality.=='?

presburger :: forall a b c . Proxy a -> Proxy b
    -> (a == b) :~: c -> (a T.== b) :~: c
presburger _ _ Refl = Unsafe.unsafeCoerce (Refl @c)

equality :: forall a b c . Proxy a -> Proxy b
    -> (a T.== b) :~: c -> (a == b) :~: c
equality _ _ Refl = Unsafe.unsafeCoerce (Refl @c)
  
--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Representation of type-level naturals.
type NatRep :: Nat -> *
newtype NatRep a = Nat Natural

type N = NatRep

testNat :: forall (a :: Nat) (b :: Nat)
    . N a -> N b -> Either (a :~: b) (a :/~: b)
testNat (Nat a) (Nat b) = case a == b of
    True  -> Left (Unsafe.unsafeCoerce Refl)
    False -> Right (Unsafe.unsafeCoerce Refl)

type Succ n = n + 1

type Pred n = n - 1

zero :: N 0
zero = Nat 0

one :: N 1
one = Nat 1

plus :: N a -> N b -> N (a + b)
plus (Nat a) (Nat b) = Nat (a + b)

minus :: N a -> N b -> N (a - b)
minus (Nat a) (Nat b) = Nat (a - b)

succ :: N n -> N (Succ n)
succ n = plus n one

pred :: N n -> N (Pred n)
pred n = minus n one

--------------------------------------------------------------------------------

witPlusIdent :: a + 0 :~: a
witPlusIdent = Refl

witPlusComm :: N a -> a + b :~: b + a
witPlusComm _ = Refl

witPlusAssoc :: N a -> N b -> (a + b) + c :~: a + (b + c)
witPlusAssoc _ _ = Refl

witPlusCong :: a :~: b -> c :~: d -> a + c :~: b + d
witPlusCong Refl Refl = Refl

witMinusIdent :: a - 0 :~: a
witMinusIdent = Refl

witMinusNil :: a - a :~: 0
witMinusNil = Refl

witMinusCong :: a :~: b -> c :~: d -> a - c :~: b - d
witMinusCong Refl Refl = Refl

--------------------------------------------------------------------------------

witPlusEq :: a + b :~: a + c -> b :~: c
witPlusEq Refl = Refl

witPlusEq' :: forall a b c . N a -> N c -> a + b :~: c + b -> a :~: c
witPlusEq' a c Refl | Refl <- witPlusComm a, Refl <- witPlusComm c = witPlusEq @b @a @ c Refl

witPlusMinus :: (a + b) - b :~: a
witPlusMinus = Refl

witPlusMinus' :: forall a b . N a -> (a + b) - a :~: b
witPlusMinus' a | Refl <- witPlusComm a = witPlusMinus @b @a

witPlusEqZero :: N a -> a + b :~: 0 -> a :~: 0
witPlusEqZero _ Refl = Refl

witSuccCong :: a :~: b -> Succ a :~: Succ b
witSuccCong eq = witPlusCong eq (Refl @1)

witSuccInj :: Succ a :~: Succ b -> a :~: b
witSuccInj Refl = Refl

witSuccPlus :: N a -> a + Succ b :~: Succ (a + b)
witSuccPlus _ = Refl

witPredCong :: a :~: b -> Pred a :~: Pred b
witPredCong eq = witMinusCong eq (Refl @1)

witPredInj :: Pred a :~: Pred b -> a :~: b
witPredInj Refl = Refl

witPredSucc :: Pred (Succ a) :~: a
witPredSucc = Refl

witSuccPred :: forall a . a :/~: 0 -> Succ (Pred a) :~: a
witSuccPred neq | Refl <- pres = Refl
  where
    pres :: (a T.== 0) :~: 'False
    pres = presburger (Proxy @a) (Proxy @0) neq

witPredUnique :: Succ a :~: b -> a :~: Pred b
witPredUnique Refl = Refl

--------------------------------------------------------------------------------
-- ** ...

type SuccRep :: Nat -> *
data SuccRep a where
    Zero :: SuccRep 0
    Succ :: NatRep a -> SuccRep (Succ a)

testSucc :: forall a . N a -> SuccRep a
testSucc a = case testNat a (Nat 0 :: N 0) of
    Left  Refl -> Zero
    Right Refl | Refl <- witSuccPred @a Refl -> Succ (pred a)

withKnownNat :: forall a b . N a -> (KnownNat a => b) -> b
withKnownNat (Nat n) f = case someNatVal n of
    SomeNat (_ :: Proxy c) ->
        gcastWith (Unsafe.unsafeCoerce (Refl @a) :: a :~: c) f

withInduction :: forall p k
    . p 0 -> (forall n . N n -> p n -> p (Succ n)) -> N k -> p k
withInduction base step = go
  where
    go :: N m -> p m
    go sn = case testSucc sn of
      Zero   -> base
      Succ n -> withKnownNat n $ step n (go n)

--------------------------------------------------------------------------------
-- ** ...

type OrdRep :: Ordering -> *
data OrdRep ord where
    Lt :: OrdRep ('LT)
    Eq :: OrdRep ('EQ)
    Gt :: OrdRep ('GT)

compareNat :: N a -> N b -> OrdRep (CmpNat a b)
compareNat (Nat a) (Nat b) = case compare a b of
    LT -> Unsafe.unsafeCoerce Lt
    EQ -> Unsafe.unsafeCoerce Eq
    GT -> Unsafe.unsafeCoerce Gt

--------------------------------------------------------------------------------

witCmpCong :: a :~: b -> c :~: d -> CmpNat a c :~: CmpNat b d
witCmpCong Refl Refl = Refl

witCmpTrans :: N a -> N b -> N c -> OrdRep d
    -> CmpNat a b :~: d -> CmpNat b c :~: d -> CmpNat a c :~: d
witCmpTrans _ _ _ ord Refl Refl = case ord of
    Gt -> Refl
    Eq -> Refl
    Lt -> Refl

witCmpEQ :: N a -> N b -> CmpNat a b :~: 'EQ -> a :~: b
witCmpEQ _ _ Refl = Refl

witCmpNEQ :: forall a b . N a -> N b -> CmpNat a b :/~: 'EQ -> a :/~: b
witCmpNEQ a b Refl = case compareNat a b of
    Gt -> equality (Proxy @a) (Proxy @b) (witGt Refl)
    Lt -> equality (Proxy @a) (Proxy @b) (witLt Refl)
  where
    witGt :: CmpNat a b :~: 'GT -> (a T.== b) :~: 'False
    witGt Refl = Refl

    witLt :: CmpNat a b :~: 'LT -> (a T.== b) :~: 'False
    witLt Refl = Refl

witEQCmp :: N a -> N b -> a :~: b -> CmpNat a b :~: 'EQ
witEQCmp _ _ Refl = Refl

witNEQCmp :: forall a b . N a -> N b -> a :/~: b -> CmpNat a b :/~: 'EQ
witNEQCmp a b Refl = case compareNat a b of
    Gt -> equality (Proxy @a) (Proxy @b) (witGt Refl)
    Eq -> case witCmpEQ a b Refl of {}
    Lt -> equality (Proxy @a) (Proxy @b) (witLt Refl)
  where
    witGt :: CmpNat a b :~: 'GT -> (a T.== b) :~: 'False
    witGt Refl = Refl

    witLt :: CmpNat a b :~: 'LT -> (a T.== b) :~: 'False
    witLt Refl = Refl

witSuccGT :: CmpNat (Succ a) a :~: 'GT
witSuccGT = Refl

witSuccLT :: CmpNat a (Succ a) :~: 'LT
witSuccLT = Refl

--------------------------------------------------------------------------------
-- Fin.
