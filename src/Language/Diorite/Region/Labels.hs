{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE EmptyCase #-}

module Language.Diorite.Region.Labels
    (
    -- * ...
      Put(..)
    , Label(..)
    , Strip
    , Dress
    , Plain
    , (:~~:)(..)
    -- ** ...
    , LblRep(..)
    , Lbl(..)
  --, strip
    , dress
    -- ** ...
  --, testLabel
    , witSDIso
    , witSPlain
    -- * ...
    , Place
    , Rgn(..)
    -- ** ...
    , local
    , atBeta
    , atEta
    -- ** ...
    , QualNat(..)
    , remove
    , union
    , Puts(..)
    , putCong
    , putUnique
    , putDiff
    , Greatest
    , thmGT
    , thmGTRem
    , thmGTAny
    , thmGTSucc
    , thmGTUnique
    ) where

import Language.Diorite.Signatures (Signature, Result, SigRep(..), signature)
import Language.Diorite.Qualifiers (Qualifier(..), type (:/~:), type (==), If, Remove, Union, Elem, QualRep(..), Qual)
import Language.Diorite.Qualifiers.Witness
import Language.Diorite.Syntax
import Language.Diorite.Decoration ((:&:)(..))
import Language.Diorite.Interpretation
import Language.Diorite.Region.Labels.Witness
import qualified Language.Diorite.Signatures as S (Signature(..))

import Data.Constraint (Constraint)
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

-- | Signature with region labels.
data Label r a =
      Const a
    | Label r a :-> Label r a
    | Put r :=> Label r a
    | Label r a :^ r
-- todo: I put 'Put r' for ':=>' just so that I could use just 'r' for ':^' but
--       this really limits the kinds of predicates I can use.

infixr 2 :->, :=>
infixl 1 :^

-- | Strip any region labels from a signature.
type Strip :: forall r . Label r * -> Signature (Put r) *
type family Strip sig where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

-- | Promote a signature into a label without any annotations.
type Dress :: forall r . Signature (Put r) * -> Label r *
type family Dress sig where
    Dress ('S.Const a) = 'Const a
    Dress (a 'S.:-> b) = Dress a ':-> Dress b
    Dress (p 'S.:=> a) = p ':=> Dress a

-- | ...
type Plain :: forall r . Label r * -> Label r *
type family Plain l where
    Plain ('Const a) = 'Const a
    Plain (a ':-> b) = Plain a ':-> Plain b
    Plain (p ':=> a) = p ':=> Plain a
    Plain (a ':^ _)  = Plain a

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype lbl :~~: sig = Stripped (Strip lbl :~: sig)
infixr :~~:

--------------------------------------------------------------------------------
-- ** Rep of ...
  
type LblRep :: forall r . Label r * -> *
data LblRep lbl where
    LblConst :: Typeable a => LblRep ('Const a)
    LblPart  :: LblRep a -> LblRep lbl -> LblRep (a ':-> lbl)
    LblPred  :: Proxy p -> LblRep lbl -> LblRep (p ':=> lbl)
    LblAt    :: Proxy r -> LblRep lbl -> LblRep (lbl ':^ r)
-- todo: remove 'Typeable' for now, think I might have to do without them.

-- | ...
type  Lbl :: forall r . Label r * -> Constraint
class Lbl lbl where
    label :: LblRep lbl

instance Typeable a => Lbl ('Const a) where
    label = LblConst

instance (Lbl a, Lbl lbl) => Lbl (a ':-> lbl) where
    label = LblPart label label

instance (Lbl lbl) => Lbl ('Put r ':=> lbl) where
    label = LblPred Proxy label

instance (Lbl lbl) => Lbl (lbl ':^ r) where
    label = LblAt Proxy label

--------------------------------------------------------------------------------
-- ** Implementation of ...

-- strip :: forall r (lbl :: Label r *) . Typeable r => LblRep lbl -> SigRep (Strip lbl)
-- strip (LblConst)    = SigConst
-- strip (LblPart a b) = SigPart (strip a) (strip b)
-- strip (LblPred p a) = SigPred p (strip a)
-- strip (LblAt _ a)   = strip a

dress :: forall r (sig :: Signature (Put r) *) . SigRep sig -> LblRep (Dress sig)
dress (SigConst)      = LblConst
dress (SigPart a sig) = LblPart (dress a) (dress sig)
dress (SigPred p sig) = LblPred p (dress sig)

--------------------------------------------------------------------------------
-- ** ...

-- testLabel :: LblRep a -> LblRep b -> Maybe (a :~: b)
-- testLabel a@(LblConst) b@(LblConst)
--     | Just Refl <- testConst a b
--     = Just Refl
--   where
--     testConst :: LblRep ('Const a) -> LblRep ('Const b) -> Maybe (a :~: b)
--     testConst LblConst LblConst = eqT
-- testLabel (LblPart a1 b1) (LblPart a2 b2)
--     | Just Refl <- testLabel a1 a2
--     , Just Refl <- testLabel b1 b2
--     = Just Refl
-- testLabel (LblPred p1 a1) (LblPred p2 a2)
--     | Just Refl <- eqP p1 p2
--     , Just Refl <- testLabel a1 a2
--     = Just Refl
-- testLabel (LblAt r1 a1) (LblAt r2 a2)
--     | Just Refl <- eqP r1 r2
--     , Just Refl <- testLabel a1 a2
--     = Just Refl
-- testLabel _ _ = Nothing

--------------------------------------------------------------------------------

witSDIso :: SigRep sig -> Strip (Dress sig) :~: sig
witSDIso (SigConst) = Refl
witSDIso (SigPart a b) | Refl <- witSDIso a, Refl <- witSDIso b = Refl
witSDIso (SigPred _ a) | Refl <- witSDIso a = Refl

witSPlain :: LblRep a -> SigRep b -> Strip a :~: b -> Plain a :~: Dress b
witSPlain (LblConst) _ Refl = Refl
witSPlain (LblPart a b) (SigPart c d) Refl
    | Refl <- witSPlain a c Refl
    , Refl <- witSPlain b d Refl
    = Refl
witSPlain (LblPred _ a) (SigPred _ b) Refl
    | Refl <- witSPlain a b Refl
    = Refl
witSPlain (LblAt _ a) b Refl
    | Refl <- witSPlain a b Refl
    = Refl

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Evidence that a region 'r' is allocated.
type Place :: forall r . r -> *
type Place r = Ev ('Put r)

-- | Term annotations for region labels.
type Rgn :: forall r . Signature (Put r) * -> *
data Rgn sig where
    Local :: Rgn (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    At    :: Rgn ('Put r 'S.:=> a 'S.:-> sig)
-- todo: 'Put r' kind here really limits the choice of qualifiers.

instance Sym Rgn where
    symbol (Local) = signature
    symbol (At)    = signature

instance Render Rgn where
    renderSym (Local) = "Local"
    renderSym (At)    = "At"

--------------------------------------------------------------------------------
-- ** ...

-- | Introduce a local binding for place 'p', associated with region 'r'.
local :: forall r (sym :: Symbol (Put r) *) qs (p :: r) info a
    .  (Rgn :<: sym, Qual qs, Elem ('Put p) qs ~ 'True, Typeable p, Typeable r)
    => Place p
    -> info a
    -> ASTF (sym :&: info) qs a
    -> ASTF (sym :&: info) (Remove ('Put p) qs) a
local p i ast = sym :$ (p :\\ Spine ast)
  where
    sym :: AST (sym :&: info) 'None (('Put p 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    sym = Sym (inj Local :&: i)

-- note: Since our region inference rules only introduce bindings at terms with
--       a first-order type it should be fine to limit 'local' to 'ASTF' values.

-- | Annotate a value-expression with the place to store its result in.
atBeta :: forall r (sym :: Symbol (Put r) *) qs info (p :: r) a
    .  (Rgn :<: sym, Qual qs, Remove ('Put p) qs ~ qs)
    => ASTF (sym :&: info) qs a
    -> info a
    -> Place p
    -> ASTF (sym :&: info) ('Put p ':. qs) a
atBeta ast i p = sym :# p :$ Spine ast
  where
    sym :: AST (sym :&: info) 'None ('Put p 'S.:=> 'S.Const a 'S.:-> 'S.Const a)
    sym = Sym (inj At :&: i)
-- note: 'Spine' is for values, hence sep. 'Beta'/'Eta' variants of 'at'.

-- | Annotate a function with the place to store its closure in.
atEta :: forall r (sym :: Symbol (Put r) *) qs (info :: * -> *) (p :: r) sig
    .  (Rgn :<: sym, Remove ('Put p) qs ~ qs)
    => Eta (sym :&: info) qs sig
    -> info (Result sig)
    -> Place p
    -> AST (sym :&: info) ('Put p ':. qs) sig
atEta ast i p = sym :# p :$ ast
  where
    sym :: AST (sym :&: info) 'None ('Put p 'S.:=> sig 'S.:-> sig)
    sym = Sym (inj At :&: i)

--------------------------------------------------------------------------------
-- ** ...

type QualNat :: Qualifier (Put Nat) -> *
data QualNat qs where
  DictNone :: QualNat ('None)
  DictPred :: NatRep r -> QualNat qs -> QualNat ('Put r ':. qs)

remove :: NatRep p -> QualNat qs -> QualNat (Remove ('Put p) qs)
remove _ (DictNone)      = DictNone
remove p (DictPred q qs) =
    case testNat p q of
        Left  Refl -> qs
        Right Refl
            | Refl <- putDiff p q Refl
            -> DictPred q (remove p qs)

union :: QualNat ps -> QualNat qs -> QualNat (Union ps qs)
union (DictNone)      qs = qs
union (DictPred p ps) qs = DictPred p (union ps (remove p qs))

type D = QualNat

type Puts :: Qualifier (Put Nat) -> Constraint
class Puts qs where
    puts :: QualNat qs

instance Puts ('None) where
    puts = DictNone

instance (KnownNat r, Puts qs) => Puts ('Put r ':. qs) where
    puts = DictPred (Nat (natVal (Proxy @r))) puts

--------------------------------------------------------------------------------

putCong :: forall a b . a :~: b -> 'Put a :~: 'Put b
putCong Refl = Refl

putUnique :: forall a b . 'Put a :~: 'Put b -> a :~: b
putUnique Refl = Refl

putDiff :: forall a b . N a -> N b -> a :/~: b -> 'Put a :/~: 'Put b
putDiff _ _ Refl = Unsafe.unsafeCoerce (Refl @('False))
-- todo: Could maybe git rid of this coerce...

--------------------------------------------------------------------------------
-- ** ...

type Greatest :: Nat -> Qualifier (Put Nat) -> Bool
type family Greatest r qs where
    Greatest _ ('None) = 'True
    Greatest r ('Put q ':. qs) = If (CmpNat r q == 'GT) (Greatest r qs) 'False

thmGT :: forall a b cs . N a -> N b -> Q cs
    -> Greatest a ('Put b ':. cs) :~: 'True
    -> CmpNat a b :~: 'GT
thmGT a b _ Refl = case compareNat a b of Gt -> Refl

thmGTRem :: forall a b cs . N a -> N b -> Q cs
    -> Greatest a ('Put b ':. cs) :~: 'True
    -> Greatest a cs :~: 'True
thmGTRem a b _ Refl = case compareNat a b of Gt -> Refl

thmGTAny :: forall a b cs
    .  N a -> N b -> Q cs -> D cs
    -> Greatest a cs :~: 'True
    -> Elem ('Put b) cs :~: 'True
    -> CmpNat a b :~: 'GT
thmGTAny a b (QualPred c cs) (DictPred r ds) Refl Refl =
    let bp :: Proxy ('Put b) = Proxy in
    case compareNat b r of
        Gt | Refl <- thmGTRem a r cs Refl
           , Refl <- witCmpNEQ b r Refl
           , Refl <- putDiff b r Refl
           , Refl <- withKnownNat b $ witElemRemove bp c (QualPred c cs) Refl
           -> thmGTAny a b cs ds Refl Refl
        Eq | Refl <- witCmpEQ b r Refl
           -> thmGT a r cs Refl
        Lt | Refl <- thmGTRem a r cs Refl
           , Refl <- witCmpNEQ b r Refl
           , Refl <- putDiff b r Refl
           , Refl <- withKnownNat b $ witElemRemove bp c (QualPred c cs) Refl
           -> thmGTAny a b cs ds Refl Refl

thmGTSucc :: forall a b
    .  N a -> Q b -> D b
    -> Greatest a b :~: 'True
    -> Greatest (Succ a) b :~: 'True
thmGTSucc _ (QualNone) _ _ = Refl
thmGTSucc a (QualPred _ bs) (DictPred r ds) Refl =
    case compareNat a r of
        Gt | Refl <- witSuccGT @a
           , Refl <- witCmpTrans (succ a) a r Gt Refl Refl
           , Refl <- thmGTSucc a bs ds Refl
           -> Refl

thmGTUnique :: forall a b
  .  N a -> Q b -> D b
  -> Greatest a b :~: 'True
  -> Elem ('Put a) b :~: 'False
thmGTUnique _ (QualNone) _ _ = Refl
thmGTUnique a (QualPred _ bs) (DictPred r ds) Refl =
    case compareNat a r of
        Gt | Refl <- witCmpNEQ a r Refl
           , Refl <- putDiff a r Refl
           , Refl <- thmGTUnique a bs ds Refl
           -> Refl

--------------------------------------------------------------------------------
-- Fin.
