--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotate where

import Language.Diorite.Signatures (Signature, Result, SigRep(..), Sig(..), testSig)
import qualified Language.Diorite.Signatures as S (Signature(..))
import Language.Diorite.Qualifiers
import qualified Language.Diorite.Qualifiers.Witness as W
import Language.Diorite.Syntax
import Language.Diorite.Traversal (Args(..), SmartApply, constMatch)
import qualified Language.Diorite.Traversal as T (QualArgs(..))
import Language.Diorite.Decoration

import Data.Constraint (Constraint, Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import qualified Data.IntMap as M

import Prelude hiding (lookup)

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

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype lbl :~~: sig = Stripped (Strip lbl :~: sig)
infixr :~~:

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

--------------------------------------------------------------------------------
-- ** ...

--newtype LBeta sym qs sig l = LBeta (Beta sym qs sig, LblRep l, l :~~: sig)
--newtype LEta  sym qs sig l = LEta  (Eta  sym qs sig, LblRep l, l :~~: sig)

-- localL :: forall r (sym :: Symbol (Put r) *) (qs :: Qualifier (Put r)) (p :: r) (a :: *) (l :: Label r *)
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
-- -- todo: not sure if 'atBetaL' and 'atEtaL' should have a 'Place r' argument or
-- --       produce an AST which expects a 'Place r'.
-- -- todo: also not sure if building a 'LblRep' alongside the labelled 'Beta' and
-- --       'Eta' is necessary yet.

-- atEtaL :: forall sym r qs sig l
--     .  (Rgn :<: sym, Remove ('Put r) qs ~ qs)
--     => LEta sym qs sig l
--     -> Place r
--     -> LBeta sym ('Put r ':. qs) sig (l ':^ r)
-- atEtaL (LEta (ast, t, Stripped Refl)) p =
--     LBeta (atEta ast p, LblAt Proxy t, Stripped Refl)

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
--
-- note:
--   would be nice to match on the exisential types in 'Beta'/'Eta' instead of
--   binding it in the 'sig' equality. Couldn't get it to work tho...
--   ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_applications.html#type-applications-in-patterns
--
--------------------------------------------------------------------------------

type LBeta :: forall r . Signature (Put r) * -> *
data LBeta sig where
    LSym :: LBeta sig
    LApp :: LBeta (a 'S.:-> sig) -> LEta a -> LBeta sig
    LEv  :: LBeta (p 'S.:=> sig) -> Proxy p -> LBeta sig

type LEta :: forall r . Signature (Put r) * -> *
data LEta sig where
    LSpine :: LEta ('S.Const a)
    LAbs   :: Sig a => LEta sig -> LEta (a 'S.:-> sig)
    LPre   :: Proxy p -> LEta sig -> LEta (p 'S.:=> sig)
-- todo: actually label things.

--type Ann :: * -> *
--data Ann a = Ann (LBeta @r ('S.Const a))

--------------------------------------------------------------------------------

data Hidden sym where
  Hide :: Beta (sym :&: LBeta) eps sig
       -> LBeta sig
       -> SigRep sig
       -> QualRep ps
       -> QualRep eps
       -> 'True :~: Extends ps eps
       -> Hidden sym

type Store sym = M.IntMap (Hidden sym)

--------------------------------------------------------------------------------

type ExLBeta :: forall r . (Symbol (Put r) *) -> (Qualifier (Put r) -> Constraint) -> (Signature (Put r) *) -> *
data ExLBeta sym p sig where
    ExLBeta :: (p qs)
        => Beta sym qs sig
        -> QualRep qs
        -> ExLBeta sym p sig

type ExLEta :: forall r . (Symbol (Put r) *) -> (Qualifier (Put r) -> Constraint) -> (Signature (Put r) *) -> *
data ExLEta sym p sig where
    ExLEta :: (p qs)
        => Eta sym qs sig
        -> QualRep qs
        -> ExLEta sym p sig

class    (Extends ps qs ~ True) => (>=) ps qs
instance (Extends ps qs ~ True) => (>=) ps qs

class    (Strip lbl ~ sig) => (~=) sig lbl
instance (Strip lbl ~ sig) => (~=) sig lbl

annotateBeta ::
    forall r (sym :: Symbol     (Put r) *) (qs  :: Qualifier  (Put r))
             (ps  :: Qualifier  (Put r))   (rs  :: T.QualArgs (Put r))
             (eps :: Qualifier  (Put r))   (sig :: Signature  (Put r) *)
             (a   :: *)
    .  ( Sym sym
       , 'S.Const a ~ Result sig
       , qs ~ SmartApply ps rs
       , 'True ~ Extends ps eps )
    => Beta (sym :&: LBeta) eps sig
    -> Args sym rs sig
    -> LBeta @r sig
    -> QualRep eps
    -> QualRep ps
    -> Store sym
    -> ( ExLBeta (sym :&: LBeta) ((>=) qs) ('S.Const a)
       , LBeta @r ('S.Const a)
       , QualRep qs )
annotateBeta b Nil l eps ps s
    | Refl :: qs :~: SmartApply ps 'T.Empty <- Refl
    , Refl :: qs :~: ps <- Refl
    , Refl :: sig :~: ('S.Const a) <- Refl
    --
    = let b'   = b   :: Beta (sym :&: LBeta) eps ('S.Const a) in
      let ps'  = ps  :: QualRep ps in
      let eps' = eps :: QualRep eps in
      let l'   = l   :: LBeta @r ('S.Const a) in
      --
      ( ExLBeta b' eps', l', ps')
annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l eps ps s
    | ( ExLEta (e' :: Eta (sym :&: LBeta) exs x) (exs :: QualRep exs)
      , (l' :: LEta x)
      , (xs :: QualRep xs))
        <- annotateEta e s
    , Refl :: Extends xs exs :~: 'True <- Refl
    , Refl :: Extends ps eps :~: 'True <- Refl
    , Refl :: rs :~: 'T.Fun xs ys <- Refl
    , Refl :: Extends (Union ps xs) (Union eps exs) :~: 'True
        <- W.witEUBoth ps eps xs exs Refl Refl
    --
    = let b'   = b :$ e' :: Beta (sym :&: LBeta) (Union eps exs) y in
      let ps'  = union ps xs :: QualRep (Union ps xs) in
      let eps' = union eps exs :: QualRep (Union eps exs) in
      let l''  = LApp l l' :: LBeta y in
      --
      annotateBeta b' as l'' eps' ps' s
annotateBeta b ((Ev p :: Ev x) :~ (as :: Args sym ys y)) l eps ps s
    | Refl :: qs :~: SmartApply ps ('T.Pre x ys) <- Refl
    , Dict :: Dict (Typeable x) <- Dict
    --
    = let b'   = b :# Ev p :: Beta (sym :&: LBeta) (x ':. eps) y in
      let ps'  = QualPred (Proxy :: Proxy x) ps :: QualRep (x ':. ps) in
      let eps' = QualPred (Proxy :: Proxy x) eps :: QualRep (x ':. eps) in
      let l'   = LEv l (Proxy :: Proxy x) :: LBeta y in
      --
      annotateBeta b' as l' eps' ps' s

annotateEta ::
  forall r (sym :: Symbol (Put r) *)
           (ps  :: Qualifier (Put r))
           (sig :: Signature (Put r) *)
    .  Sym sym
    => Eta sym ps sig
    -> Store sym
    -> ( ExLEta (sym :&: LBeta) ((>=) ps) sig
       , LEta @r sig
       , QualRep ps )
annotateEta (Spine (b :: Beta sym ps ('S.Const a))) s
    | ( ExLBeta (b' :: Beta (sym :&: LBeta) xs ('S.Const a)) (eps :: QualRep xs)
      , ps :: QualRep qs)
        <- annotateAST b s
    --
    = let e' = Spine b' :: Eta (sym :&: LBeta) xs ('S.Const a) in
      let l' = LSpine   :: LEta @r ('S.Const a) in
      --
      (ExLEta e' eps, l', ps)
annotateEta ((n :: Name) :\ (e :: Eta sym qs a)) s
    | Refl :: sig :~: (b 'S.:-> a) <- Refl
    , Dict :: Dict (Sig b) <- Dict
    = let b  = signature :: SigRep b in
      let x  = Var n :: Beta (sym :&: LBeta) 'None b in
      let xl = LSym :: LBeta b in
      let xp = QualNone :: QualRep 'None in
      let xh = Hide x xl b xp xp Refl :: Hidden sym in
      let s' = M.insert n xh s in
      witSDIso b |-
      --
      case annotateEta e s' of
        (ExLEta (e' :: Eta (sym :&: LBeta) xs a) (eps :: QualRep xs), l :: LEta x, ps  :: QualRep qs) ->
          let e''  = n :\ e' :: Eta (sym :&: LBeta) xs (b 'S.:-> a) in
          let l'   = LAbs l  :: LEta (b 'S.:-> a) in
          let eps' = eps     :: QualRep xs in
          let ps'  = ps      :: QualRep qs in
          --
          (ExLEta e'' eps', l', ps')
annotateEta ((Ev p :: Ev q) :\\ (e :: Eta sym qs a)) s
    | ( ExLEta (e' :: Eta (sym :&: LBeta) xs a) (eps :: QualRep xs)
      , l  :: LEta a
      , qs :: QualRep qs)
        <- annotateEta e s
    , Refl :: Extends qs xs :~: 'True <- Refl
    , Refl :: Elem q qs :~: 'True <- Refl
    , Refl :: Elem q xs :~: 'True
        <- W.witExtIn (Proxy :: Proxy q) qs eps Refl Refl
    , Refl :: Extends (Remove q qs) (Remove q xs) :~: 'True
        <- W.witExtShrink (Proxy :: Proxy q) qs eps Refl
    --
    = let e''  = Ev p :\\ e'                   :: Eta (sym :&: LBeta) (Remove q xs) (q 'S.:=> a) in
      let l'   = LPre (Proxy :: Proxy q) l     :: LEta (q 'S.:=> a) in
      let eps' = remove (Proxy :: Proxy q) eps :: QualRep (Remove q xs) in
      let qs'  = remove (Proxy :: Proxy q) qs  :: QualRep (Remove q qs) in
      --
      (ExLEta e'' eps', l', qs')

--------------------------------------------------------------------------------

annotateAST :: forall r (sym :: Symbol (Put r) *) qs a
    .  (Sym sym) => ASTF sym qs a -> Store sym
    -> (ExLBeta (sym :&: LBeta) ((>=) qs) ('S.Const a), QualRep qs)
annotateAST ast store = constMatch matchSym matchVar ast
  where
    matchSym :: forall ps sig
        .  ( 'S.Const a ~ Result sig
           , qs ~ SmartApply 'None ps )
        => sym sig -> Args sym ps sig
        -> (ExLBeta (sym :&: LBeta) ((>=) qs) ('S.Const a), QualRep qs)
    matchSym sym as =
        let rs = QualNone in
        let li = LSym in
        let (b, l, qs) = annotateBeta (Sym (sym :&: l)) as li rs rs store in
        (b, qs)

    matchVar :: forall ps rs sig
        .  ( 'S.Const a ~ Result sig
           , qs ~ SmartApply rs ps
           , Sig sig )
        => Name -> QualRep rs -> Args sym ps sig
        -> (ExLBeta (sym :&: LBeta) ((>=) qs) ('S.Const a), QualRep qs)
    matchVar name rs as
        | Just (Hide b l sig' ps' eps Refl) <- M.lookup name store
        , Just Refl <- testSig (signature :: SigRep sig) sig'
        , Just Refl <- testQual rs ps'
        = case annotateBeta b as l eps rs store of
            (b', l', qs) -> (b', qs)
    matchVar name _ _ = error $ "unknown variable v" ++ show name

--------------------------------------------------------------------------------

annotate :: Sym sym
    => ASTF sym qs a
    -> ExLBeta (sym :&: LBeta) ((>=) qs) ('S.Const a)
annotate ast = let (b, _) = annotateAST ast M.empty in b

--------------------------------------------------------------------------------
-- Fin.
