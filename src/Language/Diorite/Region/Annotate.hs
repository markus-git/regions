--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}

module Language.Diorite.Region.Annotate
    (
    ) where

import Language.Diorite.Signatures (Signature, Result, SigRep(..))
import Language.Diorite.Qualifiers (Qualifier(..), type (==), If, Remove, Union, Difference, QualRep(..))
import Language.Diorite.Syntax (Name, Ev(..), Beta(..), Eta(..), AST, ASTF, elam, (:+:)(..), (:<:)(..))
--import Language.Diorite.Traversal (Args(..), constMatch)
import qualified Language.Diorite.Signatures as S (Signature(..))

import Data.Constraint (Constraint)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- What we (sorta) have:
--
-- > beta :: B [] ('Int -> 'Int -> 'Int)
-- > beta = \x. \y. x + y
--
-- What we (sorta) want:
--
-- > beta :: B [1,2,3,4,5] ('Int^1 ->^2 'Int^3 ->^4 'Int^5)
-- > beta = (\x . (\y . (local <1,3> in (x + y)) at 5) at 4) at 2
--   ~alternatively~
-- > beta = \x .^2 \y .^4 local <1,3> in (x + y)^5
--
-- note: rules must now match on "sym a at r" and "\x . e at r"
-- instead of just "sym a" and "\x . e" with a rule for "e at r".
--
-- What we (sorta) need to support:
--
-- Terms for region annotations:
-- > local r in E  where  local :: AST (r : rs) 'Int -> AST rs 'Int
-- > E at r        where  at    :: AST rs 'Int       -> AST ...
--
-- Symbol signatures extended with region annotations:
-- > t ::= a | t -> t | p => t | t ^ Put r

--------------------------------------------------------------------------------
-- Term-level stuff.

-- | Kind for 'Put' predicates, which assert that a region 'r' is allocated.
data Put r = Put r

-- | Evidence that a region 'r' is allocated.
type Place :: forall r . r -> *
type Place r = Ev ('Put r)

-- | Term annotations for region labels.
type Rgn :: forall r . Signature (Put r) * -> *
data Rgn sig where
    Local :: Rgn (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    At    :: Rgn ('Put r 'S.:=> a 'S.:-> sig)

-- | Introduce a local binding for place associated with region 'r'.
local :: forall sym r qs a
    .  (Rgn :<: sym)
    => ASTF sym ('Put r ':. qs) a
    -> Place r
    -> ASTF sym qs a
local ast p = (inj Local :: AST sym 'None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)) :$ (p :\\ Spine ast)
-- note: Since our region inference rules only introduce bindings at terms with
--       a first-order type it's fine to limit 'local' to 'ASTF' values.

-- | Annotate a value-expression with the place to store its result in.
atBeta :: forall sym r qs a
    .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => ASTF sym qs a
    -> Place r
    -> ASTF sym ('Put r ':. qs) a
atBeta ast p = (inj At :: AST sym 'None ('Put r 'S.:=> 'S.Const a 'S.:-> 'S.Const a)) :# p :$ (Spine ast)
-- note: 'Spine' is for values, hence sep. 'Beta'/'Eta' variants of 'at'.

-- | Annotate a function with the place to store its closure in.
atEta :: forall sym r qs sig
    .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => Eta sym qs sig
    -> Place r
    -> AST sym ('Put r ':. qs) sig
atEta ast p = (inj At :: AST sym 'None ('Put r 'S.:=> sig 'S.:-> sig)) :# p :$ ast

--------------------------------------------------------------------------------
-- Type-level stuff.

-- | Signature with region labels.
data Label r a =
      Const a
    | Label r a :-> Label r a
    | Put r :=> Label r a
    | Label r a :^ r

infixr 2 :->, :=>
infixl 1 :^

-- | Stip any region labels from a signature.
type Strip :: forall r . Label r * -> Signature (Put r) *
type family Strip sig where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

-- | Witness of a labelled symbol signature.
type LblRep :: forall r . Label r * -> *
data LblRep l where
    LblConst :: LblRep ('Const a)
    LblPart  :: LblRep a -> LblRep sig -> LblRep (a ':-> sig)
    LblPred  :: Proxy ('Put r) -> LblRep sig -> LblRep ('Put r ':=> sig)
    LblAt    :: Proxy r -> LblRep sig -> LblRep (sig ':^ r)
-- todo: 'Put r' in 'LblPred' really limits the choice for predicates.

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype sig :~~: lbl = Stripped (sig :~: Strip lbl)
infixr :~~:

type LBeta sym qs sig l = (Beta sym qs sig, LblRep l, l :~~: sig)
type LEta  sym qs sig l = (Eta  sym qs sig, LblRep l, l :~~: sig)

atBetaL :: forall sym r qs a l
    .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => LBeta sym qs ('S.Const a) l
    -> Place r
    -> LBeta sym ('Put r ':. qs) ('S.Const a) (l ':^ r)
atBetaL (ast, t, Stripped Refl) p = (atBeta ast p, LblAt Proxy t, Stripped Refl)
-- todo: Not sure if 'atBetaL' and 'atEtaL' should have a 'Place r' argument or
--       produce an AST which expects a 'Place r'. Also not sure if building a
--       'LblRep' alongside the labelled 'Beta' and 'Eta' is necessary yet.

atEtaL :: forall sym r qs sig l
    .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => LEta sym qs sig l
    -> Place r
    -> LBeta sym ('Put r ':. qs) sig (l ':^ r)
atEtaL (ast, t, Stripped Refl) p = (atEta ast p, LblAt Proxy t, Stripped Refl)

--------------------------------------------------------------------------------
-- When annotating an 'ASTF q a' only the result 'a' is visible, so we cannot
-- determine the resulting annotations/labels from its type alone.
--
-- So I (sorta) need something like:
--
-- > annotate :: ASTF q a -> exists p b. LASTF (p >= q) (Strip b ~ a)
--
-- Here P >= Q means that P implies everything in Q and Strip removes all
-- annotations from a signature.

--------------------------------------------------------------------------------
-- Constraint stuff.

type Elem :: forall p . p -> Qualifier p -> Bool
type family Elem p qs where
    Elem p ('None)    = 'False
    Elem p (q ':. qs) = If (p == q) 'True (Elem p qs)

type Subset :: forall p . Qualifier p -> Qualifier p -> Bool
type family Subset ps qs where
    Subset ('None)    qs = 'True
    Subset (p ':. ps) qs = If (Elem p qs) (Subset ps qs) 'False

class (Subset ps qs ~ True) => (>=) ps qs
instance (Subset ps qs ~ True) => (>=) ps qs

class (Strip b ~ a) => (~~) a b
instance (Strip b ~ a) => (~~) a b

--------------------------------------------------------------------------------
-- Ex-Beta stuff.

type EBeta :: forall r
    .  (Signature (Put r) * -> *)
    -> (Qualifier (Put r) -> Constraint)
    -> (Label r * -> Constraint)
    -> Label r *
    -> *
data EBeta sym p q sig where
    Ex :: forall qs sig . (p qs, q sig)
        => LBeta sym qs sig lbl
        -> ExBeta sym p q

annotate :: Beta sym qs sig -> EBeta sym ((>=) qs) ((~~) sig)
annotate = undefined

--------------------------------------------------------------------------------
-- Fin.
