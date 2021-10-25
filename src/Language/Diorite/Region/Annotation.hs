--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotation where

import Language.Diorite.Signatures (Signature(..), Result, SigRep, Sig)
import Language.Diorite.Qualifiers (Qualifier(..), Elem, Remove, Union, Extends, QualRep)
import Language.Diorite.Syntax
import Language.Diorite.Traversal (Arguments, Args, SmartApply)
import Language.Diorite.Decoration ((:&:)(..))
import Language.Diorite.Region.Labels (Put(..), Label, Strip, Dress, LblRep, Place)
import Language.Diorite.Region.Labels.Witness (NatRep(..))
import qualified Language.Diorite.Signatures as S
import qualified Language.Diorite.Qualifiers as Q
import qualified Language.Diorite.Qualifiers.Witness as Q
import qualified Language.Diorite.Traversal as T
import qualified Language.Diorite.Decoration as D
import qualified Language.Diorite.Region.Labels as L
import qualified Language.Diorite.Region.Labels.Witness as L

import Data.Constraint (Dict(..), Constraint)
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))
import Numeric.Natural (Natural)

import GHC.TypeNats

import Prelude hiding (succ)

--------------------------------------------------------------------------------
-- * ASTs and arguments with annotations.
--------------------------------------------------------------------------------

class Sym sym => Annotate sym where
    annotate :: sym sig -> L (Result sig)
    -- sym a -> label a -> ann (result a)

-- Beta w/ ex. qualifiers bound by a constraint.
type Beta2 :: forall p . Symbol p * -> (Qualifier p -> Constraint) -> Signature p * -> *
data Beta2 sym q sig where
    B2 :: (q qs) => Beta sym qs sig -> QualRep qs -> Beta2 sym q sig

-- Eta w/ ex. qualifiers bound by a constraint.
type Eta2 :: forall p . Symbol p * -> (Qualifier p -> Constraint) -> Signature p * -> *
data Eta2 sym q sig where
    E2 :: (q qs) => Eta sym qs sig -> QualRep qs -> Eta2 sym q sig

-- ...
type L :: forall p . Signature p * -> *
data L a = L

-- Args w/ ...
type Args2 :: forall p . Symbol p * -> Arguments p -> Signature p * -> *
data Args2 sym qs sig where
    Nil :: Args2 sym ('T.Empty) ('Const a)
    Arg :: Eta2 sym ((>=) ps) a -> QualRep ps -> Args2 sym qs sig
        -> Args2 sym ('T.Union ps qs) (a ':-> sig)
    Rgn :: Ev p -> Args2 sym qs sig -> Args2 sym ('T.Insert p qs) (p ':=> sig)

-- Extends as a class so it can be partially applied.
type (>=) :: forall p . Qualifier p -> Qualifier p -> Constraint
class    (Extends ps qs ~ 'True) => (>=) ps qs
instance (Extends ps qs ~ 'True) => (>=) ps qs
-- todo: Perhaps swap >= for <=, I read ((>=) qs) as "something larger than qs",
-- but the fully applied constraint "qs >= ps". The >= symbol can then be a bit
-- confusing as |qs| < |ps|.

annotateBeta ::  forall (sym :: Symbol (Put Nat) *) ps rs qs sig a
    .  (Sym sym, L.Rgn :<: sym, 'Const a ~ Result sig, SmartApply ps rs ~ qs)
    => Beta2 (sym :&: L) ((>=) ps) sig
    -> Args2 (sym :&: L) rs sig
    -> QualRep ps
    -> SigRep sig
    -> Beta2 (sym :&: L) ((>=) qs) ('Const a)
annotateBeta b Nil ps (S.SigConst)
    -- By "Nil", know that "rs ~ 'T.Empty'" and thus "qs ~ ps".
    = b
annotateBeta (B2 b (ps' :: QualRep ps'))
             (Arg (E2 e (l' :: QualRep l')) (l :: QualRep l) as) ps
             (S.SigPart _ sig)
    -- By "Arg", know that "rs ~ 'T.Union l r" and thus
    -- "qs ~ SmartApply (Union ps l) r".
    -- 1: "(ps' + l') >= (ps + l)" from rec. call.
    -- As "ps' >= ps" and "l' >= l", then "(ps' + l') >= (ps + l)".
    | Refl :: Extends (Union ps l) (Union ps' l') :~: 'True
        <- Q.witEUBoth ps ps' l l' Refl Refl
    --
    = annotateBeta (B2 (b :$ e) (Q.union ps' l')) as (Q.union ps l) sig
annotateBeta (B2 b ps') (Rgn ev as) ps (S.SigPred evp sig)
    -- By Rgn, know that "rs ~ 'T.Insert p r" and thus
    -- "qs ~ SmartApply (p ':. ps) r".
    = annotateBeta (B2 (b :# ev) (Q.cons evp ps')) as (Q.cons evp ps) sig

annotateEta :: forall (sym :: Symbol (Put Nat) *) qs sig
    .  (Sym sym, Annotate sym, L.Rgn :<: sym)
    => Eta sym qs sig
    -> (Eta2 (sym :&: L) ((>=) qs) sig, QualRep qs)
annotateEta (Spine b)
    | qs :: QualRep qs <- Q.qualifier
    , B2 b' qs' <- annotateASTF b -- (qs :: QualRep qs)
    , Dict <- Q.witQual qs'
    = (E2 (Spine b') qs', qs)
annotateEta (v :\ e)
    | (E2 e' qs', qs) <- annotateEta e
    = (E2 (v :\ e') qs', qs)
annotateEta ((Ev p :: Ev p) :\\ (e :: Eta sym ps b))
    -- By ":\\", "qs ~ ps - p" but "(ps - p) + p ~/~ ps" because the order might
    -- change; we cannot recover the rep. of "ps" from "qs" and "p". Hence the
    -- need for "annotateEta @qs" to return a rep. of "qs".
    | (E2 (e' :: Eta (sym :&: L) ps' b) (ps' :: QualRep ps'), ps) <- annotateEta e
    -- By ":\\" and "E2", know that "p in ps", "qs ~ ps - p" and "ps' >= ps".
    -- 1: "p in ps'" from "p :\\ e'".
    --   As "ps' >= ps" and "p in ps", then "p in ps'".
    , Refl :: Elem p ps' :~: 'True
        <- Q.witExtIn (Proxy @p) ps ps' Refl Refl
    -- 2: "(ps' - p) >= qs" from "E2 _ (ps' - p)".
    --   As "qs ~ ps - p", then "(ps' - p) >= qs ~ (ps' - p) >= (ps - p)".
    --   "(ps' - p) >= (ps - p)" is eq. to "ps' >= ps".
    , Refl :: Extends (Remove p ps) (Remove p ps') :~: Extends ps ps'
        <- Q.witExtShrink (Proxy @p) ps ps' Refl
    --
    = (E2 (Ev p :\\ e') (Q.remove (Proxy @p) ps'), Q.remove (Proxy @p) ps)

annotateArgs :: forall (sym :: Symbol (Put Nat) *) rs sig
    .  (Sym sym, Annotate sym, L.Rgn :<: sym)
    => Args sym rs sig
    -> Args2 (sym :&: L) rs sig
annotateArgs (T.Nil) = Nil
annotateArgs ((e :: Eta sym ps a) T.:* (as :: Args sym qs b)) =
    -- Goal: annotateEta e :* annotateArgs as.
    -- By "T.:*", know that "rs ~ 'T.Union ps qs".
    let (e', ps) = annotateEta e in
    let as' = annotateArgs as in
    Arg e' ps as'
annotateArgs ((p :: Ev p) T.:~ (as :: Args sym ps b)) =
    -- Goal: .. p :~ annotateArgs as
    -- By "T.:~", know that "rs ~ 'T.Insert p ps".
    let as' = annotateArgs as in
    Rgn p as'

annotateSym :: forall (sym :: Symbol (Put Nat) *) qs rs a sig
    .  ( Sym sym, Annotate sym, L.Rgn :<: sym, SmartApply 'None rs ~ qs
       , Result sig ~ 'Const a)
    => sym sig
    -> Args sym rs sig
    -> Beta2 (sym :&: L) ((>=) qs) ('Const a)
annotateSym sym as =
    let sig = symbol sym in
    let as' = annotateArgs as in
    let l   = annotate sym in
    let b   = B2 (Sym (sym :&: l)) Q.QualNone in
    annotateBeta b as' Q.QualNone sig

annotateASTF :: forall (sym :: Symbol (Put Nat) *) qs a
    .  (Sym sym, Annotate sym, L.Rgn :<: sym)
    => ASTF sym qs a
    -> Beta2 (sym :&: L) ((>=) qs) ('Const a)
annotateASTF ast = T.constMatch annotateSym undefined ast

-- annotate :: forall (sym :: Symbol (Put Nat) *) qs a
--     .  (Sym sym, L.Rgn :<: sym)
--     => ASTF sym qs a
--     -> Beta2 (sym :&: Ann) ((>=) qs) ('Const a)
-- annotate ast = undefined -- annotateASTF ...

--------------------------------------------------------------------------------
-- ...
--------------------------------------------------------------------------------

-- type ABeta :: forall r . Label r * -> *
-- data ABeta l where
--     ASym   :: SigRep sig -> ABeta (Dress sig)
--     --     :: sig -> Dress sig
--     AApp   :: L.Plain b ~ a => ABeta (a 'L.:-> sig) -> AEta b -> ABeta sig
--     --     :: (a :-> sig) -> (a ^ r) -> sig
--     AEApp  :: ABeta (p 'L.:=> sig) -> Ev p -> ABeta sig
--     --     :: (p :=> sig) -> p -> sig
--     AAt    :: ABeta sig -> Proxy r -> ABeta (sig 'L.:^ r)

-- type AEta :: forall r . Label r * -> *
-- data AEta l where
--     ASpine :: LblRep sig -> AEta sig
--     --     :: ('Const a ^ r) -> ('Const a ^ r)
--     ALam   :: AEta sig -> AEta (a 'L.:-> sig)
--     --     :: a? -> sig -> ((a :-> sig) ^ r)
--     AELam  :: Ev p -> AEta sig -> AEta (p 'L.:=> sig)
--     --     :: p -> sig -> ((p :=> sig) ^ r)
-- -- todo: Actually annotate things.

-- type Ann :: forall r . Signature (Put r) * -> *
-- data Ann sig where
--     Ann :: ABeta ('L.Const a 'L.:^ p) -> Ann ('Const a)

-- type LEta :: forall r . (Label r * -> Constraint) -> *
-- data LEta p where
--     LEta :: p l => AEta l -> LblRep l -> LEta p

-- ev :: KnownNat p => NatRep p -> Place p
-- ev (Nat p) = Ev (fromInteger $ toInteger p)

-- local :: forall (sym :: Symbol (Put Nat) *) qs a (p :: Nat)
--     .  (L.Rgn :<: sym, Elem ('Put p) qs ~ 'True)
--     => NatRep p
--     -> Ann ('Const @(Put Nat) a)
--     -> Beta (sym :&: Ann) qs ('Const a)
--     -> Beta (sym :&: Ann) (Remove ('Put p) qs) ('Const a)
-- local p i ast = L.withKnownNat p $ L.local (ev p) i ast

-- atBeta :: forall (sym :: Symbol (Put Nat) *) qs a (p :: Nat)
--     .  (L.Rgn :<: sym, Remove ('Put p) qs ~ qs)
--     => Beta (sym :&: Ann) qs ('Const a)
--     -> Ann ('Const @(Put Nat) a)
--     -> NatRep p
--     -> Beta (sym :&: Ann) ('Put p ':. qs) ('Const a)
-- atBeta ast i p = L.withKnownNat p $ L.atBeta ast i (ev p)

-- atEta :: forall (sym :: Symbol (Put Nat) *) qs sig (p :: Nat)
--     .  (L.Rgn :<: sym, Remove ('Put p) qs ~ qs)
--     => Eta (sym :&: Ann) qs sig
--     -> Ann (Result sig)
--     -> NatRep p
--     -> Beta (sym :&: Ann) ('Put p ':. qs) sig
-- atEta ast i p = L.withKnownNat p $ L.atEta ast i (ev p)

-- class    (Extends ps qs ~ 'True) => (>=) ps qs
-- instance (Extends ps qs ~ 'True) => (>=) ps qs

-- class    (Strip lbl ~ sig) => (~=) sig lbl
-- instance (Strip lbl ~ sig) => (~=) sig lbl

-- class    (CmpNat m n ~ 'GT) => (>>) n m
-- instance (CmpNat m n ~ 'GT) => (>>) n m

-- annotateBeta :: forall (sym :: Symbol (Put Nat) *) qs ps eps rs sig l (n :: Nat) a
--     .  ( Sym sym
--        , Result sig ~ 'Const a
--        , L.Rgn :<: sym
--        -- Needed for (>= qs)
--        , SmartApply ps rs ~ qs
--        , Extends ps eps ~ 'True
--        , Strip l ~ sig
--        , Dress sig ~ l
--        -- Needed for unique n
--        , L.Greatest n qs ~ 'True
--        , L.Greatest n eps ~ 'True
--        , Remove ('Put n) eps ~ eps
--        )
--     => Beta (sym :&: Ann @Nat) eps sig
--     -> Args sym rs sig
--     -> ABeta @Nat l
--     -> SigRep sig
--     -> QualRep qs
--     -> L.QualNat qs
--     -> QualRep ps
--     -> QualRep eps
--     -> L.QualNat eps
--     -> ArgsRep rs
--     -> NatRep n
--     -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ((>) n) ('Const @(Put Nat) a)
--        , ABeta ('L.Const @Nat a)
--        )
-- annotateBeta b Nil l (S.SigConst) qs qsd ps eps epsd asd n
--     | Refl <- L.withKnownNat n $ Q.witExtCons (Proxy :: Proxy ('Put n)) ps eps Refl
--     , Refl <- L.thmGTSucc n eps epsd Refl
--     , Refl <- L.witSuccGT @n
--     --
--     = let b'   = atBeta b (Ann (AAt l (Proxy :: Proxy n))) n in
--       let eps' = L.withKnownNat n $ Q.QualPred (Proxy :: Proxy ('Put n)) eps in
--       --
--       (EBeta b' eps' (L.succ n), l)
-- ----------------------------------------
-- -- Application
-- annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l (S.SigPart a sig) qs qsd ps eps epsd (ArgsUnion xs ysd) n
--     | Refl :: Strip l :~: (x ':-> y) <- Refl
--     , Refl :: l       :~: (Dress x 'L.:-> Dress y) <- Refl
--     -- Convincing Haskell I'm right:
--     , Refl :: qs :~: SmartApply ps ('T.Union xs ys) <- Refl
--     , Refl :: qs :~: SmartApply (Q.Union ps xs) ys <- Refl
--     -- SmartApply (ps + xs) ys => Extends xs (SmartApply (ps + xs) ys) ~ Extends xs qs
--     , Refl :: Extends xs qs :~: 'True
--         <- witExtUnion xs ps ysd
--     -- Extends xs qs, n >> qs => n >> xs
--     , Refl :: L.Greatest n xs :~: 'True
--         <- witExtGT n qs qsd xs (undefined :: L.QualNat xs) Refl Refl
--     --
--     = case annotateEta e a n of
--         (EEta (e' :: Eta (sym :&: Ann) exs x) exs (m :: NatRep m), LEta (l' :: AEta lx) lr, qs')
--           | Refl :: Strip lx :~: x <- Refl
--           , Refl :: Extends (Q.Union ps xs) (Q.Union eps exs) :~: 'True
--               <- Q.witEUBoth ps eps xs exs Refl Refl
--           , Refl :: L.Plain lx :~: Dress x
--               <- L.witSPlain lr a Refl
--           -- m > n
--           , Refl :: CmpNat m n :~: 'GT
--               <- undefined
--           -- m > n, n >> eps => m >> eps
--           , Refl :: L.Greatest m eps :~: 'True
--               <- witGtAny m n eps epsd Refl Refl
--           -- m >> exs, m >> eps => m >> (exs + eps)
--           , Refl :: L.Greatest m (Q.Union eps exs) :~: 'True
--               <- undefined
--           , Refl :: Remove ('Put m) (Q.Union eps exs) :~: Q.Union eps exs
--               <- undefined
--           , Refl :: L.Greatest m qs :~: 'True
--               <- undefined
--           --
--           -> let b'    = b :$ e' in
--              let ps'   = Q.union ps xs in
--              let eps'  = Q.union eps exs in
--              let epsd' = L.union epsd (undefined :: L.QualNat exs) in
--              let l''   = AApp l l' in
--              annotateBeta
--                  b' as l'' sig
--                  qs qsd
--                  ps'
--                  eps' epsd'
--                  ysd
--                  m
-- ----------------------------------------
-- -- Evidence application
-- annotateBeta b ((p@(Ev _) :: Ev p) :~ (as :: Args sym ys y)) l (S.SigPred pp sig) qs qsd ps eps epsd (ArgsInsert (x :: NatRep x) asd) n
--     | Refl :: rs :~: 'T.Insert p ys <- Refl
--     , Refl :: 'Put x :~: p <- Refl
--     , Dict :: Dict (Typeable ('Put n)) <- L.withKnownNat n Dict
--     -- Convincing Haskell I'm right:
--     -- SmartApply ps (r : rs) ~ SmartApply (r : ps) rs
--     , Refl :: qs :~: SmartApply ps ('T.Insert p ys) <- Refl
--     , Refl :: qs :~: SmartApply (p ':. ps) ys <- Refl
--     -- n >> qs, n >> eps
--     --   (>>  = greatest = greater-than-any-in-qualifiers)
--     --   (eps = extended-ps ~ ps + ?)
--     , Refl :: L.Greatest n qs :~: 'True <- Refl
--     , Refl :: L.Greatest n eps :~: 'True <- Refl
--     -- SmartApply (r : ps) rs => Elem r (SmartApply (r : ps) rs) ~ Elem r qs ~ True
--     , Refl :: Elem p qs :~: 'True
--         <- witElemInsert (Proxy :: Proxy p) asd ps
--     -- Elem r qs, n >> qs => n > r
--     , Refl :: CmpNat n x :~: 'GT
--         <- L.thmGTAny n x qs qsd
--              (Refl :: L.Greatest n qs :~: 'True)
--              (Refl :: Elem p qs :~: 'True)
--     -- n >> eps, n > r => n >> (r : eps)
--     , Refl :: L.Greatest n (p ':. eps) :~: 'True <- Refl
--     -- n >> (r : eps) => Elem n (r : eps) ~ False
--     , Refl :: Elem ('Put n) (p ':. eps) :~: 'False
--         <- L.thmGTUnique n (Q.QualPred pp eps) (L.DictPred x epsd)
--              (Refl :: L.Greatest n (p ':. eps) :~: 'True)
--     -- Elem n (r : eps) ~ False => Remove n (r : eps) ~ (r : eps)
--     , Refl :: Remove ('Put n) (p ':. eps) :~: (p ':. eps)
--         <- Q.witElemId (Proxy :: Proxy ('Put n)) (Q.QualPred pp eps)
--              (Refl :: Elem ('Put n) (p ':. eps) :~: 'False)
--     --
--     = let b'    = b :# p in
--       let ps'   = Q.QualPred pp ps in
--       let eps'  = Q.QualPred pp eps in
--       let epsd' = L.DictPred x epsd in
--       let l'    = AEApp l p in
--       --
--       annotateBeta b' as l' sig qs qsd ps' eps' epsd' asd n

-- annotateEta :: forall (sym :: Symbol (Put Nat) *) qs (n :: Nat) sig
--     .  ( Sym sym
--        , L.Rgn :<: sym
--        --
--        , L.Greatest n qs ~ 'True
--        )
--     => Eta sym qs sig
--     -> SigRep sig
--     -> NatRep n
--     -> ( EEta (sym :&: Ann @Nat) ((>=) qs) n sig
--        , LEta @Nat ((~=) sig)
--        , QualRep qs
--        )
-- annotateEta (Spine b) (S.SigConst) n
--     = case annotateASTF n (undefined :: QualRep qs) (undefined :: L.QualNat qs) b of
--           (EBeta (b' :: Beta (sym :&: Ann @r) eqs ('Const a)) eqs (m :: NatRep m), (lr :: LblRep ('L.Const a)))
--               | Refl :: CmpNat m n :~: 'GT <- undefined
--               --
--               -> let e  = Spine b' in
--                  let sr = S.SigConst :: SigRep ('Const a) in
--                  let l' = ASpine lr in
--                  --
--                  (EEta e eqs m, LEta l' lr, (undefined :: QualRep qs))
-- ----------------------------------------
-- -- Variable abstraction
-- annotateEta (v :\ e) (S.SigPart b sig) n
--     | Refl :: sig :~: (b ':-> a) <- Refl
--     --
--     = case annotateEta e sig n of
--           (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs m, LEta (l :: AEta l) lr, qs)
--               | Refl :: Strip (Dress b) :~: b <- L.witSDIso b
--               --
--               -> let e'' = v :\ e' :: Eta (sym :&: Ann @r) eqs (b ':-> a) in
--                  let l'  = ALam l  :: AEta (Dress b 'L.:-> l) in
--                  let lr' = L.LblPart (L.dress b) lr in
--                  --
--                  (EEta e'' eqs m, LEta l' lr', qs)
-- ----------------------------------------
-- -- Evidence abstraction
-- annotateEta (p@(Ev _ :: Ev p) :\\ (e :: Eta sym xs x)) (S.SigPred _ sig) n
--     | Refl :: L.Greatest n xs :~: 'True <- undefined
--     --
--     = case annotateEta e sig n of
--           (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs (m :: NatRep m), LEta (l :: AEta l) lr, qs)
--               | Refl <- Q.witExtIn (Proxy :: Proxy p) qs eqs Refl Refl
--               , Refl <- Q.witExtShrink (Proxy :: Proxy p) qs eqs Refl
--               --
--               , Refl :: L.Greatest m (Remove p eqs) :~: 'True <- undefined
--               --
--               -> let e''  = p :\\ e' :: Eta (sym :&: Ann @r) (Q.Remove p eqs) (p ':=> a) in
--                  let pp   = Proxy :: Proxy p in
--                  let qs'  = Q.remove pp qs in
--                  let eqs' = Q.remove pp eqs in
--                  let l'   = AELam p l in
--                  let lr'  = L.LblPred pp lr in
--                  --
--                  (EEta e'' eqs' m, LEta l' lr', qs')

-- annotateSym :: forall (sym :: Symbol (Put Nat) *) sig qs rs a (n :: Nat)
--     .  ( Sym sym
--        , Result sig ~ 'Const a
--        , SmartApply 'None rs ~ qs
--        , L.Rgn :<: sym
--        , L.Greatest n qs ~ 'True
--        )
--     => NatRep n
--     -> QualRep qs
--     -> L.QualNat qs
--     -> sym sig
--     -> Args sym rs sig
--     -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ((>) n) ('Const @(Put Nat) a)
--        , LblRep ('L.Const @Nat a)
--        )
-- annotateSym n qs qsd sym as =
--     let none = Q.QualNone in
--     let sig  = symbol sym in
--     --
--     L.witSDIso sig |-
--     S.witTypeable (S.result sig) |-
--     --
--     let (b, l) =
--           let a = Ann (AAt l Proxy) in
--           annotateBeta (Sym (sym :&: a)) as (ASym sig) sig qs qsd none none L.DictNone undefined n
--     in
--     (b, L.LblConst @a)    

-- annotateASTF :: forall (sym :: Symbol (Put Nat) *) (n :: Nat) qs a
--     .  ( Sym sym
--        , L.Rgn :<: sym
--        , L.Greatest n qs ~ 'True
--        )
--     => NatRep n
--     -> QualRep qs
--     -> L.QualNat qs
--     -> ASTF sym qs a
--     -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ((>) n) ('Const @(Put Nat) a)
--        , LblRep ('L.Const @Nat a)
--        )
-- annotateASTF n qs qsd = T.constMatch (annotateSym n qs qsd) undefined

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

type ArgsRep :: T.Arguments (Put Nat) -> *
data ArgsRep qs where
    ArgsEmpty  :: ArgsRep ('T.Empty)
    ArgsUnion  :: QualRep qs -> ArgsRep ps -> ArgsRep ('T.Union qs ps)
    ArgsInsert :: NatRep n -> ArgsRep qs -> ArgsRep ('T.Insert ('Put n) qs)
    
--------------------------------------------------------------------------------
-- ** ...

witArgsElem :: forall a as bs . Typeable a => Proxy a -> QualRep as -> ArgsRep bs
    -> Elem a as :~: 'True
    -> Elem a (SmartApply as bs) :~: 'True
witArgsElem _ _ (ArgsEmpty) el = el
witArgsElem a as (ArgsUnion qs ps) el
    | Refl <- Q.witElemUni a as qs el
    = witArgsElem a (Q.union as qs) ps Refl
witArgsElem a as (ArgsInsert (n :: NatRep n) qs) Refl
    | Dict :: Dict (KnownNat n) <- L.withKnownNat n Dict
    , Refl <- Q.witEqIf @_ @_ @('True) a pn
    = witArgsElem a (Q.QualPred pn as) qs Refl
  where
    pn = Proxy :: Proxy ('Put n)

witArgsExt :: forall as bs cs . QualRep as -> QualRep bs -> ArgsRep cs
    -> Extends as bs :~: 'True
    -> Extends as (SmartApply bs cs) :~: 'True
witArgsExt _ _ (ArgsEmpty) ext = ext
witArgsExt as bs (ArgsUnion qs ps) ext =
    witArgsExt as (Q.union bs qs) ps (Q.witEUAdd as bs qs ext)
witArgsExt as bs (ArgsInsert (n :: NatRep n) (qs :: ArgsRep qs)) ext =
    L.withKnownNat n $
      witArgsExt as (Q.QualPred (Proxy @('Put n)) bs) qs $
        Q.witExtCons (Proxy @('Put n)) as bs ext

witElemInsert :: forall a as bs . Typeable a => Proxy a -> ArgsRep as -> QualRep bs
    -> Elem a (SmartApply bs ('T.Insert a as)) :~: 'True
witElemInsert a as bs = witArgsElem a (Q.QualPred a bs) as Refl

witExtUnion :: forall as bs cs . QualRep as -> QualRep bs -> ArgsRep cs
    -> Extends as (SmartApply bs ('T.Union as cs)) :~: 'True
witExtUnion as bs cs
    | Refl <- Q.witExtRefl as
    , Refl <- Q.witEUAdd as as bs Refl
    , Refl <- Q.witEURefl as as bs
    = witArgsExt as (Q.union bs as) cs Refl

--------------------------------------------------------------------------------
-- ...

witElemGT :: forall a b cs . NatRep a -> NatRep b -> QualRep cs -> L.QualNat cs
    -> L.Greatest a cs :~: 'True
    -> Elem ('Put b) cs :~: 'True
    -> CmpNat a b :~: 'GT
witElemGT a b (Q.QualPred c cs) (L.DictPred x xs) Refl Refl =
    let pb = Proxy @('Put b) in
    case L.withKnownNat b (Q.testEq pb c) of
        Left  Refl -> L.thmGT a x cs Refl
        Right Refl -> witElemGT a b cs xs (L.thmGTRem a x cs Refl) Refl

witExtGT :: forall a bs cs . NatRep a -> QualRep bs -> L.QualNat bs -> QualRep cs -> L.QualNat cs
    -> L.Greatest a bs :~: 'True
    -> Extends cs bs :~: 'True
    -> L.Greatest a cs :~: 'True
witExtGT _ _ _ (Q.QualNone) _ _ _ = Refl
witExtGT a bs bsd (Q.QualPred c cs) (L.DictPred x xs) Refl Refl
    | Refl <- Q.witExtRem c cs bs Refl
    , Refl <- witExtGT a bs bsd cs xs Refl Refl
    , Refl <- Q.witExtElem c cs bs Refl
    , Refl <- witElemGT a x bs bsd Refl Refl
    = Refl

witGtAny :: forall a b cs . NatRep a -> NatRep b -> QualRep cs -> L.QualNat cs
    -> CmpNat a b :~: 'GT
    -> L.Greatest b cs :~: 'True
    -> L.Greatest a cs :~: 'True
witGtAny _ _ (Q.QualNone) _ _ _ = Refl
witGtAny a b (Q.QualPred c cs) (L.DictPred x xs) Refl Refl
    | Refl <- L.thmGTRem b x cs Refl
    , Refl <- witGtAny a b cs xs Refl Refl
    , Refl <- L.thmGT b x cs Refl
    , Refl <- L.witCmpTrans a b x L.Gt Refl Refl
    = Refl

--------------------------------------------------------------------------------
-- Fin.
