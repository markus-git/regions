{-# OPTIONS_GHC -Wall #-}

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
    , strip
    , dress
    -- ** ...
    , testLabel
    , witSDIso
    , witSPlain
    -- * ...
    , Place
    , Rgn(..)
    -- ** ...
    , local
    , atBeta
    , atEta
    ) where

import Language.Diorite.Signatures (Signature, SigRep(..))
import qualified Language.Diorite.Signatures as S (Signature(..))
import Language.Diorite.Qualifiers (Qualifier(..), Remove)
import Language.Diorite.Syntax

import Data.Constraint (Constraint)
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)
import Data.Proxy (Proxy(..))

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
    LblPred  :: Typeable p => Proxy p -> LblRep lbl -> LblRep (p ':=> lbl)
    LblAt    :: Typeable r => Proxy r -> LblRep lbl -> LblRep (lbl ':^ r)

-- | ...
type  Lbl :: forall r . Label r * -> Constraint
class Lbl lbl where
    label :: LblRep lbl

instance Typeable a => Lbl ('Const a) where
    label = LblConst

instance (Lbl a, Lbl lbl) => Lbl (a ':-> lbl) where
    label = LblPart label label

instance (Typeable ('Put r), Lbl lbl) => Lbl ('Put r ':=> lbl) where
    label = LblPred Proxy label

instance (Typeable r, Lbl lbl) => Lbl (lbl ':^ r) where
    label = LblAt Proxy label

--------------------------------------------------------------------------------
-- ** Implementation of ...

strip :: forall r (lbl :: Label r *) . Typeable r => LblRep lbl -> SigRep (Strip lbl)
strip (LblConst)    = SigConst
strip (LblPart a b) = SigPart (strip a) (strip b)
strip (LblPred p a) = SigPred p (strip a)
strip (LblAt _ a)   = strip a

dress :: forall r (sig :: Signature (Put r) *) . SigRep sig -> LblRep (Dress sig)
dress (SigConst)      = LblConst
dress (SigPart a sig) = LblPart (dress a) (dress sig)
dress (SigPred p sig) = LblPred p (dress sig)

--------------------------------------------------------------------------------
-- ** ...

-- | ...
testLabel :: LblRep a -> LblRep b -> Maybe (a :~: b)
testLabel a@(LblConst) b@(LblConst)
    | Just Refl <- testConst a b
    = Just Refl
  where
    testConst :: LblRep ('Const a) -> LblRep ('Const b) -> Maybe (a :~: b)
    testConst LblConst LblConst = eqT
testLabel (LblPart a1 b1) (LblPart a2 b2)
    | Just Refl <- testLabel a1 a2
    , Just Refl <- testLabel b1 b2
    = Just Refl
testLabel (LblPred p1 a1) (LblPred p2 a2)
    | Just Refl <- eqP p1 p2
    , Just Refl <- testLabel a1 a2
    = Just Refl
testLabel (LblAt r1 a1) (LblAt r2 a2)
    | Just Refl <- eqP r1 r2
    , Just Refl <- testLabel a1 a2
    = Just Refl
testLabel _ _ = Nothing

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

-- note: 'Erasure' being a type family seems to prevent a 'HasDict' instance.
-- (|~) :: Maybe (a :~~: b) -> (a ~ Erasure b => Maybe c) -> Maybe c
-- (|~) m a = do (Erased Refl) <- m;  a
-- infixr |~

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

--------------------------------------------------------------------------------
-- * ...

-- | Introduce a local binding for place associated with region 'r'.
local :: forall r (sym :: Symbol (Put r) *) qs p a
    . (Rgn :<: sym, Typeable p, Typeable r)
    => ASTF sym ('Put p ':. qs) a
    -> Place p
    -> ASTF sym qs a
local ast p = (inj Local :: AST sym 'None (('Put p 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)) :$ (p :\\ Spine ast)
-- note: Since our region inference rules only introduce bindings at terms with
--       a first-order type it should be fine to limit 'local' to 'ASTF' values.

-- | Annotate a value-expression with the place to store its result in.
atBeta :: forall r sym qs a . (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => ASTF sym qs a
    -> Place r
    -> ASTF sym ('Put r ':. qs) a
atBeta ast p = (inj At :: AST sym 'None ('Put r 'S.:=> 'S.Const a 'S.:-> 'S.Const a)) :# p :$ (Spine ast)
-- note: 'Spine' is for values, hence sep. 'Beta'/'Eta' variants of 'at'.

-- | Annotate a function with the place to store its closure in.
atEta :: forall r sym qs sig . (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => Eta sym qs sig
    -> Place r
    -> AST sym ('Put r ':. qs) sig
atEta ast p = (inj At :: AST sym 'None ('Put r 'S.:=> sig 'S.:-> sig)) :# p :$ ast

--------------------------------------------------------------------------------
-- newtype LBeta sym qs sig l = LBeta (Beta sym qs sig, LblRep l, l :~~: sig)
-- newtype LEta  sym qs sig l = LEta  (Eta  sym qs sig, LblRep l, l :~~: sig)

-- localL :: forall r (sym :: Symbol (Put r) *) qs p a l
--     .  (Rgn :<: sym, Typeable p, Typeable r)
--     => LBeta sym ('Put p ':. qs) ('S.Const a) l
--     -> Place p
--     -> LBeta sym qs ('S.Const a) l
-- localL (LBeta (ast, t, Stripped Refl)) p =
--     LBeta (local ast p, t, Stripped Refl)
  
-- atBetaL :: forall sym r qs a l
--     .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
--     => LBeta sym qs ('S.Const a) l
--     -> Place r
--     -> LBeta sym ('Put r ':. qs) ('S.Const a) (l ':^ r)
-- atBetaL (LBeta (ast, t, Stripped Refl)) p =
--     LBeta (atBeta ast p, LblAt Proxy t, Stripped Refl)

-- atEtaL :: forall sym r qs sig l
--     .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
--     => LEta sym qs sig l
--     -> Place r
--     -> LBeta sym ('Put r ':. qs) sig (l ':^ r)
-- atEtaL (LEta (ast, t, Stripped Refl)) p =
--     LBeta (atEta ast p, LblAt Proxy t, Stripped Refl)

-- todo: not sure if 'atBetaL' and 'atEtaL' should have a 'Place r' argument or
--       produce an AST which expects a 'Place r'.
--------------------------------------------------------------------------------
-- Fin.
