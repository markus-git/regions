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

import Language.Diorite.Signatures (Signature(..), Sig(..), Result, SigRep)
import Language.Diorite.Qualifiers (Qualifier(..), Qual(..), Remove, Elem, QualRep(..)) --, type (:/~:), type (==), If, Remove, Union, Elem, QualRep(..), Qual)
-- import Language.Diorite.Qualifiers.Witness
import Language.Diorite.Syntax (Ev, Symbol, Beta(..), Eta(..), AST, ASTF, Sym(..), (:<:)(..))
import Language.Diorite.Decoration ((:&:)(..))
import Language.Diorite.Interpretation (Render(..))
-- import Language.Diorite.Region.Labels.Witness
-- import qualified Language.Diorite.Signatures as S (Signature(..))

-- import Data.Constraint (Constraint)
import Data.Typeable (Typeable)
-- import Data.Type.Equality (type (:~:)(..))
-- import Data.Proxy (Proxy(..))
-- import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

import GHC.TypeNats

-- import Prelude hiding (succ)

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

-- | ...
type LSym :: Symbol (Put Nat) * -> Signature (Put Nat) * -> *
data LSym sym sig where
    LSym :: (Strip l ~ sig) => sym l -> SigRep l -> TypeRep sym (Result sig)
        -> LSym sym sig

-- | ...
type Free :: * -> *
type family Free a
-- type instance Free _ = QualNone

-- | ...
class Sym sym => Lbl sym where
    type TypeRep sym :: * -> *
    labelSym :: sym sig -> LSym sym sig
    -- free :: TypeRep sym a -> Free a

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

-- -- | Annotate a value-expression with the place to store its result in.
-- atBeta :: forall r (sym :: Symbol (Put r) *) qs info (p :: r) a
--     .  (Rgn :<: sym, Qual qs, Remove ('Put p) qs ~ qs)
--     => ASTF (sym :&: info) qs a
--     -> info a
--     -> Place p
--     -> ASTF (sym :&: info) ('Put p ':. qs) a
-- atBeta ast i p = sym :# p :$ Spine ast
--   where
--     sym :: AST (sym :&: info) 'None ('Put p 'S.:=> 'S.Const a 'S.:-> 'S.Const a)
--     sym = Sym (inj At :&: i)

-- -- | Annotate a function with the place to store its closure in.
-- atEta :: forall r (sym :: Symbol (Put r) *) qs (info :: * -> *) (p :: r) sig
--     .  (Rgn :<: sym, Remove ('Put p) qs ~ qs)
--     => Eta (sym :&: info) qs sig
--     -> info (Result sig)
--     -> Place p
--     -> AST (sym :&: info) ('Put p ':. qs) sig
-- atEta ast i p = sym :# p :$ ast
--   where
--     sym :: AST (sym :&: info) 'None ('Put p 'S.:=> sig 'S.:-> sig)
--     sym = Sym (inj At :&: i)
-- -- note: 'Spine' is for values, hence sep. 'Beta'/'Eta' variants of 'at'.

--------------------------------------------------------------------------------
-- ** ...

-- type QualNat :: Qualifier (Put Nat) -> *
-- data QualNat qs where
--   DictNone :: QualNat ('None)
--   DictPred :: NatRep r -> QualNat qs -> QualNat ('Put r ':. qs)

-- remove :: NatRep p -> QualNat qs -> QualNat (Remove ('Put p) qs)
-- remove _ (DictNone)      = DictNone
-- remove p (DictPred q qs) =
--     case testNat p q of
--         Left  Refl -> qs
--         Right Refl
--             | Refl <- putDiff p q Refl
--             -> DictPred q (remove p qs)

-- union :: QualNat ps -> QualNat qs -> QualNat (Union ps qs)
-- union (DictNone)      qs = qs
-- union (DictPred p ps) qs = DictPred p (union ps (remove p qs))

-- type D = QualNat

-- type Puts :: Qualifier (Put Nat) -> Constraint
-- class Puts qs where
--     puts :: QualNat qs

-- instance Puts ('None) where
--     puts = DictNone

-- instance (KnownNat r, Puts qs) => Puts ('Put r ':. qs) where
--     puts = DictPred (Nat (natVal (Proxy @r))) puts

--------------------------------------------------------------------------------

-- putCong :: forall a b . a :~: b -> 'Put a :~: 'Put b
-- putCong Refl = Refl

-- putUnique :: forall a b . 'Put a :~: 'Put b -> a :~: b
-- putUnique Refl = Refl

-- putDiff :: forall a b . N a -> N b -> a :/~: b -> 'Put a :/~: 'Put b
-- putDiff _ _ Refl = Unsafe.unsafeCoerce (Refl @('False))
-- -- todo: Could maybe git rid of this coerce...

--------------------------------------------------------------------------------
-- ** ...

-- type Greatest :: Nat -> Qualifier (Put Nat) -> Bool
-- type family Greatest r qs where
--     Greatest _ ('None) = 'True
--     Greatest r ('Put q ':. qs) = If (CmpNat r q == 'GT) (Greatest r qs) 'False

-- thmGT :: forall a b cs . N a -> N b -> Q cs
--     -> Greatest a ('Put b ':. cs) :~: 'True
--     -> CmpNat a b :~: 'GT
-- thmGT a b _ Refl = case compareNat a b of Gt -> Refl

-- thmGTRem :: forall a b cs . N a -> N b -> Q cs
--     -> Greatest a ('Put b ':. cs) :~: 'True
--     -> Greatest a cs :~: 'True
-- thmGTRem a b _ Refl = case compareNat a b of Gt -> Refl

-- thmGTAny :: forall a b cs
--     .  N a -> N b -> Q cs -> D cs
--     -> Greatest a cs :~: 'True
--     -> Elem ('Put b) cs :~: 'True
--     -> CmpNat a b :~: 'GT
-- thmGTAny a b (QualPred c cs) (DictPred r ds) Refl Refl =
--     let bp :: Proxy ('Put b) = Proxy in
--     case compareNat b r of
--         Gt | Refl <- thmGTRem a r cs Refl
--            , Refl <- witCmpNEQ b r Refl
--            , Refl <- putDiff b r Refl
--            , Refl <- withKnownNat b $ witElemRemove bp c (QualPred c cs) Refl
--            -> thmGTAny a b cs ds Refl Refl
--         Eq | Refl <- witCmpEQ b r Refl
--            -> thmGT a r cs Refl
--         Lt | Refl <- thmGTRem a r cs Refl
--            , Refl <- witCmpNEQ b r Refl
--            , Refl <- putDiff b r Refl
--            , Refl <- withKnownNat b $ witElemRemove bp c (QualPred c cs) Refl
--            -> thmGTAny a b cs ds Refl Refl

-- thmGTSucc :: forall a b
--     .  N a -> Q b -> D b
--     -> Greatest a b :~: 'True
--     -> Greatest (Succ a) b :~: 'True
-- thmGTSucc _ (QualNone) _ _ = Refl
-- thmGTSucc a (QualPred _ bs) (DictPred r ds) Refl =
--     case compareNat a r of
--         Gt | Refl <- witSuccGT @a
--            , Refl <- witCmpTrans (succ a) a r Gt Refl Refl
--            , Refl <- thmGTSucc a bs ds Refl
--            -> Refl

-- thmGTUnique :: forall a b
--   .  N a -> Q b -> D b
--   -> Greatest a b :~: 'True
--   -> Elem ('Put a) b :~: 'False
-- thmGTUnique _ (QualNone) _ _ = Refl
-- thmGTUnique a (QualPred _ bs) (DictPred r ds) Refl =
--     case compareNat a r of
--         Gt | Refl <- witCmpNEQ a r Refl
--            , Refl <- putDiff a r Refl
--            , Refl <- thmGTUnique a bs ds Refl
--            -> Refl

--------------------------------------------------------------------------------
-- Fin.
