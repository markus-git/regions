--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Diorite.Region.Annotate
    (
    ) where

import Language.Diorite.Signatures (Signature, Result, SigRep(..), Sig(..))
import qualified Language.Diorite.Signatures as S (Signature(..))
import Language.Diorite.Qualifiers
import qualified Language.Diorite.Qualifiers.Witness as W
import Language.Diorite.Syntax
import Language.Diorite.Traversal (Args(..), SmartApply, constMatch)
import qualified Language.Diorite.Traversal as T (QualArgs(..))

import Data.Constraint (Constraint, Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)

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

--------------------------------------------------------------------------------
-- * ...

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
-- todo: 'Put r' kind here really limits the choice of qualifiers. Ideally, some
--       compositional variant a la "Put r :<: p" could be used instead.

-- | Introduce a local binding for place associated with region 'r'.
local :: forall r (sym :: Symbol (Put r) *) (qs :: Qualifier (Put r)) (p :: r) (a :: *)
    .  (Rgn :<: sym, Typeable p, Typeable r)
    => ASTF sym ('Put p ':. qs) a
    -> Place p
    -> ASTF sym qs a
local ast p = (inj Local :: AST sym 'None (('Put p 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)) :$ (p :\\ Spine ast)
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
-- * ...

-- | Signature with region labels.
type Label :: * -> * -> *
data Label r a =
      Const a
    | Label r a :-> Label r a
    | Put r :=> Label r a
    | Label r a :^ r
-- todo: I put 'Put r' for ':=>' so that I could use just 'r' for ':^', not yet
--       sure if this is a good idea.. Constraints are already limited and this
--       doesn't help.

infixr 2 :->, :=>
infixl 1 :^

-- | Strip any region labels from a signature.
type Strip :: forall r . Label r * -> Signature (Put r) *
type family Strip sig where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

-- | ...
type Dress :: forall r . Signature (Put r) * -> Label r *
type family Dress sig where
    Dress ('S.Const a) = 'Const a
    Dress (a 'S.:-> b) = Dress a ':-> Dress b
    Dress (p 'S.:=> a) = p ':=> Dress a

--------------------------------------------------------------------------------
-- ** Rep. of ...

-- | Witness of a labelled symbol signature.
type LblRep :: forall r . Label r * -> *
data LblRep l where
    LblConst :: Typeable a => LblRep ('Const a)
    LblPart  :: LblRep a -> LblRep sig -> LblRep (a ':-> sig)
    LblPred  :: Typeable p => Proxy p -> LblRep sig -> LblRep (p ':=> sig)
    LblAt    :: Proxy r -> LblRep sig -> LblRep (sig ':^ r)

-- | ...
type  Lbl :: forall r . Label r * -> Constraint
class Lbl lbl where
    label :: LblRep lbl

--------------------------------------------------------------------------------
-- ** ...

strip :: forall r (lbl :: Label r *) . Typeable r => LblRep lbl -> SigRep (Strip lbl)
strip (LblConst)      = SigConst
strip (LblPart a lbl) = SigPart (strip a) (strip lbl)
strip (LblPred p lbl) = SigPred p (strip lbl)
strip (LblAt _ lbl)   = strip lbl

dress :: forall r (sig :: Signature (Put r) *) . SigRep sig -> LblRep (Dress sig)
dress (SigConst)      = LblConst
dress (SigPart a sig) = LblPart (dress a) (dress sig)
dress (SigPred p sig) = LblPred p (dress sig)

witSDIso :: forall r (sig :: Signature (Put r) *) . SigRep sig -> Strip (Dress sig) :~: sig
witSDIso (SigConst) = Refl
witSDIso (SigPart a b) | Refl <- witSDIso a, Refl <- witSDIso b = Refl
witSDIso (SigPred _ a) | Refl <- witSDIso a = Refl

--removeL :: Proxy q -> LblRep lbl -> LblRep (Remove q lbl)

--------------------------------------------------------------------------------
-- ** ...

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype lbl :~~: sig = Stripped (Strip lbl :~: sig)
infixr :~~:

newtype LBeta sym qs sig l = LBeta (Beta sym qs sig, LblRep l, l :~~: sig)
newtype LEta  sym qs sig l = LEta  (Eta  sym qs sig, LblRep l, l :~~: sig)

localL :: forall r (sym :: Symbol (Put r) *) (qs :: Qualifier (Put r)) (p :: r) (a :: *) (l :: Label r *)
    .  (Rgn :<: sym, Typeable p, Typeable r)
    => LBeta sym ('Put p ':. qs) ('S.Const a) l
    -> Place p
    -> LBeta sym qs ('S.Const a) l
localL (LBeta (ast, t, Stripped Refl)) p =
    LBeta (local ast p, t, Stripped Refl)
  
atBetaL :: forall sym r qs a l
    .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => LBeta sym qs ('S.Const a) l
    -> Place r
    -> LBeta sym ('Put r ':. qs) ('S.Const a) (l ':^ r)
atBetaL (LBeta (ast, t, Stripped Refl)) p =
    LBeta (atBeta ast p, LblAt Proxy t, Stripped Refl)
-- todo: not sure if 'atBetaL' and 'atEtaL' should have a 'Place r' argument or
--       produce an AST which expects a 'Place r'.
-- todo: also not sure if building a 'LblRep' alongside the labelled 'Beta' and
--       'Eta' is necessary yet.

atEtaL :: forall sym r qs sig l
    .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
    => LEta sym qs sig l
    -> Place r
    -> LBeta sym ('Put r ':. qs) sig (l ':^ r)
atEtaL (LEta (ast, t, Stripped Refl)) p =
    LBeta (atEta ast p, LblAt Proxy t, Stripped Refl)

--------------------------------------------------------------------------------
-- When annotating an 'ASTF q a' only the result 'a' is visible, so we cannot
-- determine the resulting annotations/labels from its type alone.
--
-- So I (sorta) need something like:
--
-- > annotate :: ASTF q a -> exists p b. LASTF p b where (p >= q) (Strip b ~ a)
--
-- Since I treat qualifiers like a set (or rather a list), 'P >= Q' simply means
-- that 'P' is a subset of 'Q'. But the annotation will never remove qualifiers
-- from 'P', so 'Q' really contains every qualifier in 'P' (even its duplicates
-- because of the list-masquerading-as-a-set thingy).
--
-- 'Strip' simply removes all annotations from a signature and indicates that
-- we havent altered the original programs "meaning".
--------------------------------------------------------------------------------

-- data ExLAST c sym p sig where
--     Ex :: (p qs, Strip l ~ sig)
--        => c sym qs sig l
--        -> QualRep qs
--        -> ExLAST c sym p sig
--   LBeta sym qs sig l = (Beta sym qs sig, LblRep l, l :~~: sig)
--   LEta  sym qs sig l = (Eta  sym qs sig, LblRep l, l :~~: sig)
--   ExLBeta = ExLAST LBeta
--   ExLEta  = ExLAST LEta

type LblArg :: forall r . Label r * -> *
data LblArg l where

class    (Extends ps qs ~ True) => (>=) ps qs
instance (Extends ps qs ~ True) => (>=) ps qs

type ExLBeta :: forall r
    .  (Symbol (Put r) *)
    -> (Qualifier (Put r) -> Constraint)
    -> (Signature (Put r) *)
    -> *
data ExLBeta sym p sig where
    ExLBeta :: (p qs, Strip l ~ sig)
        => Beta sym qs sig
        -> LblRep l
        -> QualRep qs
        -> ExLBeta sym p sig

type ExLEta :: forall r
    .  (Symbol (Put r) *)
    -> (Qualifier (Put r) -> Constraint)
    -> (Signature (Put r) *)
    -> *
data ExLEta sym p sig where
    ExLEta :: (p qs, Strip l ~ sig)
        => Eta sym qs sig
        -> LblRep l
        -> QualRep qs
        -> ExLEta sym p sig

-- pattern LB beta l r = LBeta (beta, l, r)
-- pattern LE eta  l r = LEta  (eta, l, r)
-- todo: figure out how to clean up the matching mess with patterns.

annotateBeta ::
    forall r (sym :: Symbol (Put r) *)
             (qs  :: Qualifier (Put r))
             (ps  :: Qualifier (Put r))
             (rs  :: T.QualArgs (Put r))
             (eps :: Qualifier (Put r))
             (sig :: Signature (Put r) *)
             (a   :: *)
    .  ( Sym sym
       , a  ~ Result sig
       , qs ~ SmartApply ps rs
       , Extends ps eps ~ 'True
       )
    => Beta sym eps sig
    -> Args sym rs  sig
    -> QualRep eps
    -> QualRep ps
    -> (ExLBeta sym ((>=) qs) ('S.Const a), QualRep qs)
annotateBeta (b {- Const a -}) Nil eps ps
    --
    | Refl :: qs :~: SmartApply ps 'T.Empty <- Refl
    , Refl :: qs :~: ps <- Refl
    , Dict :: Dict (Typeable a) <- undefined
    --
    = let b'   = b  :: Beta sym eps ('S.Const a) in
      let ps'  = ps :: QualRep ps in
      let eps' = eps :: QualRep eps in
      let l    = LblConst :: LblRep ('Const a) in
      --
      (ExLBeta b' l eps', ps')
-- todo: this l is useless, as it forgets the whole application of 'sig' so far.
annotateBeta (b {- x :-> y -}) ((e :: Eta sym xs x) :* (as :: Args sym ys y)) eps ps
    --
    | ( ExLEta (e' :: Eta sym exs x) (l :: LblRep l) (exs :: QualRep exs)
      , (xs :: QualRep xs))
        <- annotateEta e
    -- exs ~ qs2, xs ~ ps1
    , Refl :: Extends xs exs :~: 'True <- Refl
    , Refl :: Extends ps eps :~: 'True <- Refl
    , Refl :: Strip l :~: x <- Refl
    , Refl :: rs :~: 'T.Fun xs ys <- Refl
    , Refl :: Extends (Union ps xs) (Union eps exs) :~: 'True <- undefined
    --
    = let b'   = b :$ e' :: Beta sym (Union eps exs) y in
      let ps'  = union ps xs :: QualRep (Union ps xs) in
      let eps' = union eps exs :: QualRep (Union eps exs) in
      --
      annotateBeta b' as eps' ps'
annotateBeta b ((p :: Ev x) :~ (as :: Args sym ys y)) eps ps
    -- 
    | Refl :: qs :~: SmartApply ps ('T.Pre x ys) <- Refl
    , Dict :: Dict (Typeable x) <- undefined
    --
    = let b'   = b :# p :: Beta sym (x ':. eps) y in
      let ps'  = QualPred (Proxy :: Proxy x) ps :: QualRep (x ':. ps) in
      let eps' = QualPred (Proxy :: Proxy x) eps :: QualRep (x ':. eps) in
      --
      annotateBeta b' as eps' ps'

annotateEta :: forall r (sym :: Symbol (Put r) *)
                        (ps  :: Qualifier (Put r))
                        (sig :: Signature (Put r) *)
    .  Sym sym
    => Eta sym ps sig
    -> (ExLEta sym ((>=) ps) sig, QualRep ps)
annotateEta (Spine b)
    | ( ExLBeta (b' :: Beta sym xs a) (l :: LblRep l) (eps :: QualRep xs)
      , (ps :: QualRep qs))
        <- annotate b
    = --
      ( ExLEta (Spine b') l eps
      , ps)
annotateEta ((n :: Name) :\ (e :: Eta sym qs a))
    | ( ExLEta (e' :: Eta sym xs a) (l :: LblRep l) (eps :: QualRep xs)
      , (ps :: QualRep qs))
        <- annotateEta e
    = --
      let a = arg (Proxy :: Proxy sig) in
      witSDIso a |-
      --
      ( ExLEta (n :\ e') (LblPart (dress a) l) eps
      , ps)
  where
    arg :: forall a b . Sig a => Proxy (a 'S.:-> b) -> SigRep a
    arg _ = signature
-- note: would be nice to match on the exisential types in 'Beta'/'Eta' instead.
--       ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_applications.html#type-applications-in-patterns
annotateEta ((p :: Ev q) :\\ (e :: Eta sym qs a))
    | ( ExLEta (e' :: Eta sym xs a) (l :: LblRep l) (eps :: QualRep xs)
      , (qs :: QualRep qs))
        <- annotateEta e
      --
    , Refl :: Extends qs xs :~: 'True <- Refl
    , Refl :: Elem q qs :~: 'True <- Refl
      --
    , Refl :: Elem q xs :~: 'True
        <- W.witExtIn (Proxy :: Proxy q) qs eps Refl Refl
    , Refl :: Extends (Remove q qs) (Remove q xs) :~: 'True
        <- W.witExtShrink (Proxy :: Proxy q) qs eps Refl
    = --
      let (e''  :: Eta sym (Remove q xs) (q 'S.:=> a)) = p :\\ e' in
      let (l'   :: LblRep (q ':=> l)) = LblPred Proxy l in
      let (r    :: (q ':=> l) :~~: (q 'S.:=> a)) = Stripped Refl in
      let (eps' :: QualRep (Remove q xs)) = remove (Proxy :: Proxy q) eps in
      let (qs'  :: QualRep (Remove q qs)) = remove (Proxy :: Proxy q) qs in
      --
      ( ExLEta e'' l' eps'
      , qs')

annotate :: forall r (sym :: Symbol (Put r) *)
                     (qs :: Qualifier (Put r))
                     (a :: *)
    .  Sym sym
    => ASTF sym qs a
    -> (ExLBeta sym ((>=) qs) ('S.Const a), QualRep qs)
annotate = constMatch matchSym undefined
  where
    matchSym :: forall (ps  :: T.QualArgs (Put r))
                       (sig :: Signature (Put r) *)
        .  (a ~ Result sig, qs ~ SmartApply 'None ps)
        => sym sig
        -> Args sym ps sig
        -> (ExLBeta sym ((>=) qs) ('S.Const a), QualRep qs)
    matchSym s as = annotateBeta (Sym s) as (QualNone) (QualNone)

--------------------------------------------------------------------------------
-- Fin.
