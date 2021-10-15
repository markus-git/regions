--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotation where

import Language.Diorite.Signatures (Signature(..), Result, SigRep, Sig)
import Language.Diorite.Qualifiers (Qualifier(..), Elem, Remove, Extends, QualRep)
import Language.Diorite.Syntax
import Language.Diorite.Traversal (Arguments, Args(..), SmartApply)
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
-- * Annotation of ASTs with local region.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Annotations for symbols, labels each application/abstraction.

type ABeta :: forall r . Label r * -> *
data ABeta l where
    ASym   :: SigRep sig -> ABeta (Dress sig)
    --     :: sig -> Dress sig
    AApp   :: L.Plain b ~ a => ABeta (a 'L.:-> sig) -> AEta b -> ABeta sig
    --     :: (a :-> sig) -> (a ^ r) -> sig
    AEApp  :: ABeta (p 'L.:=> sig) -> Ev p -> ABeta sig
    --     :: (p :=> sig) -> p -> sig
    AAt    :: ABeta sig -> Proxy r -> ABeta (sig 'L.:^ r)

type AEta :: forall r . Label r * -> *
data AEta l where
    ASpine :: LblRep sig -> AEta sig
    --     :: ('Const a ^ r) -> ('Const a ^ r)
    ALam   :: AEta sig -> AEta (a 'L.:-> sig)
    --     :: a? -> sig -> ((a :-> sig) ^ r)
    AELam  :: Ev p -> AEta sig -> AEta (p 'L.:=> sig)
    --     :: p -> sig -> ((p :=> sig) ^ r)
-- todo: Actually lable things.

type Ann :: forall r . Signature (Put r) * -> *
data Ann sig where
    Ann :: ABeta ('L.Const a 'L.:^ p) -> Ann ('Const a)

type LEta :: forall r . (Label r * -> Constraint) -> *
data LEta p where
    LEta :: p l => AEta l -> LblRep l -> LEta p

--------------------------------------------------------------------------------
-- ** ASTs with "existential" but constrained qualifiers.

type EBeta :: forall p
    . Symbol p * -> (Qualifier p -> Constraint) -> (Nat -> Constraint) -> Signature p * -> *
data EBeta sym q p sig where
    EBeta :: (q qs, p m, L.Greatest m qs ~ 'True)
        => Beta sym qs sig
        -> QualRep qs
        -> NatRep m
        -> EBeta sym q p sig

type EEta :: forall p
    . Symbol p * -> (Qualifier p -> Constraint) -> Nat -> Signature p * -> *
data EEta sym q n sig where
    EEta :: (q qs, L.Greatest m qs ~ 'True, CmpNat m n ~ 'GT)
        => Eta sym qs sig
        -> QualRep qs
        -> NatRep m
        -> EEta sym q n sig
-- todo: clean up internal constraints.

class    (Extends ps qs ~ 'True) => (>=) ps qs
instance (Extends ps qs ~ 'True) => (>=) ps qs

class    (Strip lbl ~ sig) => (~=) sig lbl
instance (Strip lbl ~ sig) => (~=) sig lbl

class    (CmpNat m n ~ 'GT) => (>) n m
instance (CmpNat m n ~ 'GT) => (>) n m

--------------------------------------------------------------------------------
-- ** Region annotations.

ev :: KnownNat p => NatRep p -> Place p
ev (Nat p) = Ev (fromInteger $ toInteger p)

local :: forall (sym :: Symbol (Put Nat) *) qs a (p :: Nat)
    .  (L.Rgn :<: sym, Elem ('Put p) qs ~ 'True)
    => NatRep p
    -> Ann ('Const @(Put Nat) a)
    -> Beta (sym :&: Ann) qs ('Const a)
    -> Beta (sym :&: Ann) (Remove ('Put p) qs) ('Const a)
local p i ast = L.withKnownNat p $ L.local (ev p) i ast

atBeta :: forall (sym :: Symbol (Put Nat) *) qs a (p :: Nat)
    .  (L.Rgn :<: sym, Remove ('Put p) qs ~ qs)
    => Beta (sym :&: Ann) qs ('Const a)
    -> Ann ('Const @(Put Nat) a)
    -> NatRep p
    -> Beta (sym :&: Ann) ('Put p ':. qs) ('Const a)
atBeta ast i p = L.withKnownNat p $ L.atBeta ast i (ev p)

atEta :: forall (sym :: Symbol (Put Nat) *) qs sig (p :: Nat)
    .  (L.Rgn :<: sym, Remove ('Put p) qs ~ qs)
    => Eta (sym :&: Ann) qs sig
    -> Ann (Result sig)
    -> NatRep p
    -> Beta (sym :&: Ann) ('Put p ':. qs) sig
atEta ast i p = L.withKnownNat p $ L.atEta ast i (ev p)

--------------------------------------------------------------------------------
-- ** Region labelling.

annotateBeta :: forall (sym :: Symbol (Put Nat) *) qs ps eps rs sig l (n :: Nat) a
    .  ( Sym sym
       , Result sig ~ 'Const a
       , L.Rgn :<: sym
       -- Needed for (>= qs)
       , SmartApply ps rs ~ qs
       , Extends ps eps ~ 'True
       , Strip l ~ sig
       , Dress sig ~ l
       -- Needed for unique n
       , L.Greatest n qs ~ 'True
       , L.Greatest n eps ~ 'True
       , Remove ('Put n) eps ~ eps
       )
    => Beta (sym :&: Ann @Nat) eps sig
    -> Args sym rs sig
    -> ABeta @Nat l
    -> SigRep sig
    -> QualRep qs
    -> L.QualNat qs
    -> QualRep ps
    -> QualRep eps
    -> L.QualNat eps
    -> ArgsRep rs
    -> NatRep n
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ((>) n) ('Const @(Put Nat) a)
       , ABeta ('L.Const @Nat a)
       )
annotateBeta b Nil l (S.SigConst) qs qsd ps eps epsd asd n
    | Refl <- L.withKnownNat n $ Q.witExtCons (Proxy :: Proxy ('Put n)) ps eps Refl
    , Refl <- L.thmGTSucc n eps epsd Refl
    , Refl <- L.witSuccGT @n
    --
    = let b'   = atBeta b (Ann (AAt l (Proxy :: Proxy n))) n in
      let eps' = L.withKnownNat n $ Q.QualPred (Proxy :: Proxy ('Put n)) eps in
      --
      (EBeta b' eps' (L.succ n), l)
----------------------------------------
-- Application
annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l (S.SigPart a sig) qs qsd ps eps epsd (ArgsUnion xs ysd) n
    | Refl :: Strip l :~: (x ':-> y) <- Refl
    , Refl :: l       :~: (Dress x 'L.:-> Dress y) <- Refl
    -- Convincing Haskell I'm right:
    , Refl :: qs :~: SmartApply ps ('T.Union xs ys) <- Refl
    , Refl :: qs :~: SmartApply (Q.Union ps xs) ys <- Refl
    -- SmartApply (ps + xs) ys => Extends xs (SmartApply (ps + xs) ys) ~ Extends xs qs
    , Refl :: Extends xs qs :~: 'True
        <- witExtUnion xs ps ysd
    -- Extends xs qs, n >> qs => n >> xs
    , Refl :: L.Greatest n xs :~: 'True
        <- witExtGT n qs qsd xs (undefined :: L.QualNat xs) Refl Refl
    --
    = case annotateEta e a n of
        (EEta (e' :: Eta (sym :&: Ann) exs x) exs (m :: NatRep m), LEta (l' :: AEta lx) lr, qs')
          | Refl :: Strip lx :~: x <- Refl
          , Refl :: Extends (Q.Union ps xs) (Q.Union eps exs) :~: 'True
              <- Q.witEUBoth ps eps xs exs Refl Refl
          , Refl :: L.Plain lx :~: Dress x
              <- L.witSPlain lr a Refl
          -- m > n
          , Refl :: CmpNat m n :~: 'GT
              <- undefined
          -- m > n, n >> eps => m >> eps
          , Refl :: L.Greatest m eps :~: 'True
              <- witGtAny m n eps epsd Refl Refl
          -- m >> exs, m >> eps => m >> (exs + eps)
          , Refl :: L.Greatest m (Q.Union eps exs) :~: 'True
              <- undefined
          , Refl :: Remove ('Put m) (Q.Union eps exs) :~: Q.Union eps exs
              <- undefined
          , Refl :: L.Greatest m qs :~: 'True
              <- undefined
          --
          -> let b'    = b :$ e' in
             let ps'   = Q.union ps xs in
             let eps'  = Q.union eps exs in
             let epsd' = L.union epsd (undefined :: L.QualNat exs) in
             let l''   = AApp l l' in
             annotateBeta
                 b' as l'' sig
                 qs qsd
                 ps'
                 eps' epsd'
                 ysd
                 m
----------------------------------------
-- Evidence application
annotateBeta b ((p@(Ev _) :: Ev p) :~ (as :: Args sym ys y)) l (S.SigPred pp sig) qs qsd ps eps epsd (ArgsInsert (x :: NatRep x) asd) n
    | Refl :: rs :~: 'T.Insert p ys <- Refl
    , Refl :: 'Put x :~: p <- Refl
    , Dict :: Dict (Typeable ('Put n)) <- L.withKnownNat n Dict
    -- Convincing Haskell I'm right:
    -- SmartApply ps (r : rs) ~ SmartApply (r : ps) rs
    , Refl :: qs :~: SmartApply ps ('T.Insert p ys) <- Refl
    , Refl :: qs :~: SmartApply (p ':. ps) ys <- Refl
    -- n >> qs, n >> eps
    --   (>>  = greatest = greater-than-any-in-qualifiers)
    --   (eps = extended-ps ~ ps + ?)
    , Refl :: L.Greatest n qs :~: 'True <- Refl
    , Refl :: L.Greatest n eps :~: 'True <- Refl
    -- SmartApply (r : ps) rs => Elem r (SmartApply (r : ps) rs) ~ Elem r qs ~ True
    , Refl :: Elem p qs :~: 'True
        <- witElemInsert (Proxy :: Proxy p) asd ps
    -- Elem r qs, n >> qs => n > r
    , Refl :: CmpNat n x :~: 'GT
        <- L.thmGTAny n x qs qsd
             (Refl :: L.Greatest n qs :~: 'True)
             (Refl :: Elem p qs :~: 'True)
    -- n >> eps, n > r => n >> (r : eps)
    , Refl :: L.Greatest n (p ':. eps) :~: 'True <- Refl
    -- n >> (r : eps) => Elem n (r : eps) ~ False
    , Refl :: Elem ('Put n) (p ':. eps) :~: 'False
        <- L.thmGTUnique n (Q.QualPred pp eps) (L.DictPred x epsd)
             (Refl :: L.Greatest n (p ':. eps) :~: 'True)
    -- Elem n (r : eps) ~ False => Remove n (r : eps) ~ (r : eps)
    , Refl :: Remove ('Put n) (p ':. eps) :~: (p ':. eps)
        <- Q.witElemId (Proxy :: Proxy ('Put n)) (Q.QualPred pp eps)
             (Refl :: Elem ('Put n) (p ':. eps) :~: 'False)
    --
    = let b'    = b :# p in
      let ps'   = Q.QualPred pp ps in
      let eps'  = Q.QualPred pp eps in
      let epsd' = L.DictPred x epsd in
      let l'    = AEApp l p in
      --
      annotateBeta b' as l' sig qs qsd ps' eps' epsd' asd n

annotateEta :: forall (sym :: Symbol (Put Nat) *) qs (n :: Nat) sig
    .  ( Sym sym
       , L.Rgn :<: sym
       --
       , L.Greatest n qs ~ 'True
       )
    => Eta sym qs sig
    -> SigRep sig
    -> NatRep n
    -> ( EEta (sym :&: Ann @Nat) ((>=) qs) n sig
       , LEta @Nat ((~=) sig)
       , QualRep qs
       )
annotateEta (Spine b) (S.SigConst) n
    = case annotateASTF n (undefined :: QualRep qs) (undefined :: L.QualNat qs) b of
          (EBeta (b' :: Beta (sym :&: Ann @r) eqs ('Const a)) eqs (m :: NatRep m), (lr :: LblRep ('L.Const a)))
              | Refl :: CmpNat m n :~: 'GT <- undefined
              --
              -> let e  = Spine b' in
                 let sr = S.SigConst :: SigRep ('Const a) in
                 let l' = ASpine lr in
                 --
                 (EEta e eqs m, LEta l' lr, (undefined :: QualRep qs))
----------------------------------------
-- Variable abstraction
annotateEta (v :\ e) (S.SigPart b sig) n
    | Refl :: sig :~: (b ':-> a) <- Refl
    --
    = case annotateEta e sig n of
          (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs m, LEta (l :: AEta l) lr, qs)
              | Refl :: Strip (Dress b) :~: b <- L.witSDIso b
              --
              -> let e'' = v :\ e' :: Eta (sym :&: Ann @r) eqs (b ':-> a) in
                 let l'  = ALam l  :: AEta (Dress b 'L.:-> l) in
                 let lr' = L.LblPart (L.dress b) lr in
                 --
                 (EEta e'' eqs m, LEta l' lr', qs)
----------------------------------------
-- Evidence abstraction
annotateEta (p@(Ev _ :: Ev p) :\\ (e :: Eta sym xs x)) (S.SigPred _ sig) n
    | Refl :: L.Greatest n xs :~: 'True <- undefined
    --
    = case annotateEta e sig n of
          (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs (m :: NatRep m), LEta (l :: AEta l) lr, qs)
              | Refl <- Q.witExtIn (Proxy :: Proxy p) qs eqs Refl Refl
              , Refl <- Q.witExtShrink (Proxy :: Proxy p) qs eqs Refl
              --
              , Refl :: L.Greatest m (Remove p eqs) :~: 'True <- undefined
              --
              -> let e''  = p :\\ e' :: Eta (sym :&: Ann @r) (Q.Remove p eqs) (p ':=> a) in
                 let pp   = Proxy :: Proxy p in
                 let qs'  = Q.remove pp qs in
                 let eqs' = Q.remove pp eqs in
                 let l'   = AELam p l in
                 let lr'  = L.LblPred pp lr in
                 --
                 (EEta e'' eqs' m, LEta l' lr', qs')

--------------------------------------------------------------------------------

-- | ...
annotateSym :: forall (sym :: Symbol (Put Nat) *) sig qs rs a (n :: Nat)
    .  ( Sym sym
       , Result sig ~ 'Const a
       , SmartApply 'None rs ~ qs
       , L.Rgn :<: sym
       , L.Greatest n qs ~ 'True
       )
    => NatRep n
    -> QualRep qs
    -> L.QualNat qs
    -> sym sig
    -> Args sym rs sig
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ((>) n) ('Const @(Put Nat) a)
       , LblRep ('L.Const @Nat a)
       )
annotateSym n qs qsd sym as =
    let none = Q.QualNone in
    let sig  = symbol sym in
    --
    L.witSDIso sig |-
    S.witTypeable (S.result sig) |-
    --
    let (b, l) =
          let a = Ann (AAt l Proxy) in
          annotateBeta (Sym (sym :&: a)) as (ASym sig) sig qs qsd none none L.DictNone undefined n
    in
    (b, L.LblConst @a)    


annotateASTF :: forall (sym :: Symbol (Put Nat) *) (n :: Nat) qs a
    .  ( Sym sym
       , L.Rgn :<: sym
       , L.Greatest n qs ~ 'True
       )
    => NatRep n
    -> QualRep qs
    -> L.QualNat qs
    -> ASTF sym qs a
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ((>) n) ('Const @(Put Nat) a)
       , LblRep ('L.Const @Nat a)
       )
annotateASTF n qs qsd = T.constMatch (annotateSym n qs qsd) undefined

-- annotate :: forall (sym :: Symbol (Put Nat) *) qs a
--     .  ( Sym sym
--        , L.Rgn :<: sym
--        )
--     => ASTF sym qs a
--     -> EBeta (sym :&: Ann) ((>=) qs) ((>) 0) ('Const a)
-- annotate ast = undefined -- fst (annotateASTF ast zero)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

type ArgsRep :: T.Arguments (Put Nat) -> *
data ArgsRep qs where
    ArgsEmpty  :: ArgsRep ('T.Empty)
    ArgsUnion  :: QualRep qs -> ArgsRep ps -> ArgsRep ('T.Union qs ps)
    ArgsInsert :: NatRep n -> ArgsRep qs -> ArgsRep ('T.Insert ('Put n) qs)

type Arguments :: T.Arguments (Put Nat) -> Constraint
class Arguments qs where
    record :: ArgsRep qs
    
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
