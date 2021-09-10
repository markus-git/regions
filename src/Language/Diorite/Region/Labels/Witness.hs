{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

{-# LANGUAGE TypeApplications #-}

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
-- * ...
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- ** ...

-- | Representation of type-level naturals.
type NatRep :: Nat -> *
newtype NatRep a = Nat Natural

type N = NatRep

testNat :: forall (a :: Nat) (b :: Nat)
    .  N a -> N b -> Either (a :~: b) (a :/~: b)
testNat (Nat a) (Nat b) = case a == b of
    True  -> Left  (Unsafe.unsafeCoerce Refl)
    False -> Right (Unsafe.unsafeCoerce Refl)

-- Presburger seems to only work with the built in '==' type, which I can't
-- seem to use with Qualifiers (todo: try again?). While I could say that
--   :/~: := (a T.== b ~ False, a Q.== b ~ False),
-- I feel like this approach is easier than rewriting Q & Q.Witness...
false :: forall a b . Proxy a -> Proxy b -> a :/~: b -> (a T.== b) :~: 'False
false _ _ (Refl :: a == b :~: 'False) = Unsafe.unsafeCoerce (Refl @'False)

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

witPlusMinus :: N a -> N b -> (a + b) - b :~: a
witPlusMinus _ _ = Refl

witPlusMinus' :: N a -> N b -> (a + b) - a :~: b
witPlusMinus' a b | Refl <- witPlusComm a = witPlusMinus b a

witPlusEqZero :: N a -> a + b :~: 0 -> a :~: 0
witPlusEqZero _ Refl = Refl

--------------------------------------------------------------------------------

witSuccCong :: a :~: b -> Succ a :~: Succ b
witSuccCong Refl = witPlusCong Refl (Refl :: 1 :~: 1)

witSuccInj :: Succ a :~: Succ b -> a :~: b
witSuccInj Refl = Refl

witSuccPlus :: N a -> a + Succ b :~: Succ (a + b)
witSuccPlus _ = Refl

witPredCong :: a :~: b -> Pred a :~: Pred b
witPredCong Refl = witMinusCong Refl (Refl :: 1 :~: 1)

witPredInj :: Pred a :~: Pred b -> a :~: b
witPredInj Refl = Refl

witPredSucc :: Pred (Succ a) :~: a
witPredSucc = Refl

witSuccPred :: forall a . a :/~: 0 -> Succ (Pred a) :~: a
witSuccPred neq | Refl <- false (Proxy @a) (Proxy @0) neq = Refl

witPredUnique :: Succ a :~: b -> a :~: Pred b
witPredUnique Refl = Refl

--------------------------------------------------------------------------------
-- ** ...

type ZoS :: Nat -> *
data ZoS a where
    Zero :: ZoS 0
    Succ :: NatRep a -> ZoS (Succ a)

testZoS :: forall a . N a -> ZoS a
testZoS a = case testNat a (Nat 0 :: N 0) of
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
    go sn = case testZoS sn of
      Zero   -> base
      Succ n -> withKnownNat n $ step n (go n)

--------------------------------------------------------------------------------
-- ** ...

type OrdRep :: Ordering -> *
data OrdRep ord where
    LtR :: OrdRep ('LT)
    EqR :: OrdRep ('EQ)
    GtR :: OrdRep ('GT)

compareNat :: NatRep a -> NatRep b -> OrdRep (CmpNat a b)
compareNat (Nat a) (Nat b) = case compare a b of
    LT -> Unsafe.unsafeCoerce LtR
    EQ -> Unsafe.unsafeCoerce EqR
    GT -> Unsafe.unsafeCoerce GtR

witCmpEq :: NatRep a -> NatRep b -> CmpNat a b :~: 'EQ -> a :~: b
witCmpEq _ _ Refl = Unsafe.unsafeCoerce Refl

--------------------------------------------------------------------------------
-- ** ...

witSuccGt :: forall (a :: Nat) . NatRep a -> CmpNat (Succ a) a :~: 'GT
witSuccGt _ = undefined

--------------------------------------------------------------------------------
-- ** ...

-- type NatOf :: Put Nat -> Nat
-- type family NatOf n where
--     NatOf ('Put n) = n

-- type Greatest :: Nat -> Qualifier (Put Nat) -> Bool
-- type family Greatest n qs where
--     Greatest _ ('None) = 'True
--     Greatest n (q ':. qs) = If (CmpNat n (NatOf q) == 'GT) (Greatest n qs) 'False

-- testGT :: forall (a :: Nat) (b :: Put Nat)
--     .  (KnownNat a, KnownNat (NatOf b))
--     => Proxy ('Put a) -> Proxy b
--     -> Either (CmpNat a (NatOf b) :~: 'GT) (CmpNat a (NatOf b) :/~: 'GT)
-- testGT _ _ =
--   let x = natVal (Proxy @(NatOf b)) in
--   case compare (natVal (Proxy @a)) x of
--       GT -> Left  (Unsafe.unsafeCoerce Refl)
--       _  -> Right (Unsafe.unsafeCoerce Refl)

-- -- forall q in qs . KnownNat q?
-- witThm1 :: forall (a :: Nat) (b :: Qualifier (Put Nat))
--     .  (KnownNat a)
--     => Proxy ('Put a) -> QualRep b
--     -> (Greatest a     b) :~: 'True
--     -> (Greatest (a+1) b) :~: 'True
-- witThm1 _ (QualNone) _ = Refl
-- witThm1 a (QualPred (b :: Proxy q) (bs :: QualRep qs)) Refl
--   | Refl :: Greatest a (q ':. qs) :~: 'True <- Refl
--   , Refl :: If (CmpNat a (NatOf q) == 'GT) (Greatest a qs) 'False :~: 'True <- Refl
--   = undefined
--   -- = case testGT a b of
--   --       Left  Refl -> _
--   --       Right x    -> case x of {}

--------------------------------------------------------------------------------
-- Fin.
