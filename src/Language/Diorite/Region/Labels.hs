{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE EmptyCase #-}

module Language.Diorite.Region.Labels where
  --   (
  --   -- * ...
  --     Put(..)
  --   , Label(..)
  --   , Strip
  --   , Dress
  --   , Plain
  --   , (:~~:)(..)
  --   -- ** ...
  --   , LblRep(..)
  --   , Lbl(..)
  -- --, strip
  --   , dress
  --   -- ** ...
  -- --, testLabel
  --   , witSDIso
  --   , witSPlain
  --   -- * ...
  --   , Place
  --   , Rgn(..)
  --   -- ** ...
  --   , local
  --   , atBeta
  --   , atEta
  --   -- ** ...
  --   , QualNat(..)
  --   , remove
  --   , union
  --   , Puts(..)
  --   , putCong
  --   , putUnique
  --   , putDiff
  --   , Greatest
  --   , thmGT
  --   , thmGTRem
  --   , thmGTAny
  --   , thmGTSucc
  --   , thmGTUnique
  --   ) where

import Language.Diorite.Signatures (Signature(..), Sig(..), Result)
import Language.Diorite.Qualifiers (Qualifier(..), Qual(..), Remove, Elem, QualRep(..), type (==), type (:/~:), If, Remove, Union) --, Elem, QualRep(..), Qual)
import Language.Diorite.Qualifiers.Witness (Q, witElemRemove)
import Language.Diorite.Syntax (Ev, Symbol, Beta(..), Eta(..), AST, ASTF, Sym(..), (:<:)(..))
import Language.Diorite.Decoration ((:&:)(..))
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Region.Labels.Witness
-- import qualified Language.Diorite.Signatures as S (Signature(..))

-- import Data.Constraint (Constraint)
import Data.Typeable (Typeable)
import Data.Type.Equality (type (:~:)(..))
import Data.Proxy (Proxy(..))
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

import GHC.TypeNats

import Prelude hiding (succ)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Kind for 'Put' predicates, which assert that a region 'r' is allocated.
data Put r = Put r

-- | Evidence that a region 'r' is allocated.
type Place :: forall r . r -> *
type Place r = Ev ('Put r)

-- | Term annotations for region labels.
type Rgn :: Signature (Put Nat) * -> *
data Rgn sig where
    -- ^ Binding of local region 'r'.
    Local :: (KnownNat r, Typeable a)
        => Rgn (('Put r ':=> 'Const a) ':-> 'Const a)
    -- ^ ...
    At :: (KnownNat r, Typeable a, Sig a, Sig sig)
        => Rgn ('Put r ':=> a ':-> sig)

instance Sym Rgn where
    symbol (Local) = signature
    symbol (At)    = signature

instance Render Rgn where
    renderSym (Local) = "local"
    renderSym (At)    = "at"

--------------------------------------------------------------------------------
-- ** ...

-- | Removes all predicates from a signature
type Strip :: Signature (Put Nat) * -> Signature (Put Nat) *
type family Strip sig where
    Strip ('Const a) = 'Const a
    Strip (a ':-> b) = Strip a ':-> Strip b
    Strip ('Put r ':=> a) = Strip a

--------------------------------------------------------------------------------
-- ** ...

-- | Introduce a local binding for place 'p', associated with region 'r'.
local :: forall (sym :: Symbol (Put Nat) *) qs r info a
    .  (Rgn :<: sym, Qual qs, Elem ('Put r) qs ~ 'True, KnownNat r, Typeable a)
    => Place r
    -> info a
    -> ASTF (sym :&: info) qs a
    -> ASTF (sym :&: info) (Remove ('Put r) qs) a
local p i ast = sym :$ (p :\\ Spine ast)
  where
    sym :: AST (sym :&: info) 'None (('Put r ':=> 'Const a) ':-> 'Const a)
    sym = Sym (inj Local :&: i)
-- note: Since our region inference rules only introduce bindings at terms with
--       a first-order type it should be fine to limit 'local' to 'ASTF' values.

-- | Annotate a value-expression with the place to store its result in.
atBeta :: forall r (sym :: Symbol (Put Nat) *) qs (info :: * -> *) a
    .  ((Rgn :&: info) :<: sym, Qual qs, Remove ('Put r) qs ~ qs, KnownNat r, Typeable a)
    => ASTF sym qs a
    -> info a
    -> Place r
    -> ASTF sym ('Put r ':. qs) a
atBeta ast i p = sym :# p :$ Spine ast
  where
    sym :: AST sym 'None ('Put r ':=> 'Const a ':-> 'Const a)
    sym = Sym (inj (At :&: i))

-- -- | Annotate a function with the place to store its closure in.
atEta :: forall r (sym :: Symbol (Put Nat) *) qs info sig
    .  ((Rgn :&: info) :<: sym, Remove ('Put r) qs ~ qs, KnownNat r, Typeable sig, Sig sig)
    => Eta sym qs sig
    -> info (Result sig)
    -> Place r
    -> AST sym ('Put r ':. qs) sig
atEta ast i p = sym :# p :$ ast
  where
    sym :: AST sym 'None ('Put r ':=> sig ':-> sig)
    sym = Sym (inj (At :&: i))
-- note: 'Spine' is for values, hence sep. 'Beta'/'Eta' variants of 'at'.

--------------------------------------------------------------------------------
-- ** ...

witPutCong :: forall a b . a :~: b -> 'Put a :~: 'Put b
witPutCong Refl = Refl

witPutUnique :: forall a b . 'Put a :~: 'Put b -> a :~: b
witPutUnique Refl = Refl

witPutDiff :: forall a b . N a -> N b -> a :/~: b -> 'Put a :/~: 'Put b
witPutDiff _ _ Refl = Unsafe.unsafeCoerce (Refl @('False))
-- todo: remove coerce?

type PutRep :: Qualifier (Put Nat) -> *
data PutRep qs where
  PutNone :: PutRep ('None)
  PutPred :: NatRep r -> PutRep qs -> PutRep ('Put r ':. qs)

type P = PutRep

remove :: NatRep p -> PutRep qs -> PutRep (Remove ('Put p) qs)
remove _ (PutNone)      = PutNone
remove p (PutPred q qs) =
    case testNat p q of
        Left  Refl -> qs
        Right Refl
            | Refl <- witPutDiff p q Refl
            -> PutPred q (remove p qs)

union :: PutRep ps -> PutRep qs -> PutRep (Union ps qs)
union (PutNone)      qs = qs
union (PutPred p ps) qs = PutPred p (union ps (remove p qs))

-- type Puts :: Qualifier (Put Nat) -> Constraint
-- class Puts qs where
--     puts :: QualNat qs

-- instance Puts ('None) where
--     puts = DictNone

-- instance (KnownNat r, Puts qs) => Puts ('Put r ':. qs) where
--     puts = DictPred (Nat (natVal (Proxy @r))) puts

--------------------------------------------------------------------------------
-- ** ...

type Greatest :: Nat -> Qualifier (Put Nat) -> Bool
type family Greatest r qs where
    Greatest _ ('None) = 'True
    Greatest r ('Put q ':. qs) = If (CmpNat r q == 'GT) (Greatest r qs) 'False

witGT :: forall a b cs . N a -> N b -> Q cs -> Greatest a ('Put b ':. cs) :~: 'True -> CmpNat a b :~: 'GT
witGT a b _ Refl = case compareNat a b of Gt -> Refl

witGTRem :: forall a b cs . N a -> N b -> Q cs -> Greatest a ('Put b ':. cs) :~: 'True -> Greatest a cs :~: 'True
witGTRem a b _ Refl = case compareNat a b of Gt -> Refl

witGTAny :: forall a b cs . N a -> N b -> Q cs -> P cs -> Greatest a cs :~: 'True -> Elem ('Put b) cs :~: 'True -> CmpNat a b :~: 'GT
witGTAny a b (QualPred c cs) (PutPred r ds) Refl Refl =
    let bp :: Proxy ('Put b) = Proxy in
    case compareNat b r of
        Gt | Refl <- witGTRem a r cs Refl
           , Refl <- witCmpNEQ b r Refl
           , Refl <- witPutDiff b r Refl
           , Refl <- withKnownNat b $ witElemRemove bp c (QualPred c cs) Refl
           -> witGTAny a b cs ds Refl Refl
        Eq | Refl <- witCmpEQ b r Refl
           -> witGT a r cs Refl
        Lt | Refl <- witGTRem a r cs Refl
           , Refl <- witCmpNEQ b r Refl
           , Refl <- witPutDiff b r Refl
           , Refl <- withKnownNat b $ witElemRemove bp c (QualPred c cs) Refl
           -> witGTAny a b cs ds Refl Refl

witGTSucc :: forall a b . N a -> Q b -> P b -> Greatest a b :~: 'True -> Greatest (Succ a) b :~: 'True
witGTSucc _ (QualNone) _ _ = Refl
witGTSucc a (QualPred _ bs) (PutPred r ds) Refl =
    case compareNat a r of
        Gt | Refl <- witSuccGT @a
           , Refl <- witCmpTrans (succ a) a r Gt Refl Refl
           , Refl <- witGTSucc a bs ds Refl
           -> Refl

witGTUnique :: forall a b . N a -> Q b -> P b -> Greatest a b :~: 'True -> Elem ('Put a) b :~: 'False
witGTUnique _ (QualNone) _ _ = Refl
witGTUnique a (QualPred _ bs) (PutPred r ds) Refl =
    case compareNat a r of
        Gt | Refl <- witCmpNEQ a r Refl
           , Refl <- witPutDiff a r Refl
           , Refl <- witGTUnique a bs ds Refl
           -> Refl

--------------------------------------------------------------------------------
-- Fin.
