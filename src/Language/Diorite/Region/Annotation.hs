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
    ASpine :: LblRep ('L.Const a 'L.:^ p) -> AEta ('L.Const a 'L.:^ p)
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
    . Symbol p * -> (Qualifier p -> Constraint) -> Signature p * -> *
data EBeta sym q sig where
    EBeta :: (q qs, L.Greatest n qs ~ 'True)
        => Beta sym qs sig
        -> QualRep qs
        -> NatRep n
        -> EBeta sym q sig

type EEta :: forall p
    . Symbol p * -> (Qualifier p -> Constraint) -> Signature p * -> *
data EEta sym q sig where
    EEta :: q qs => Eta sym qs sig -> QualRep qs -> EEta sym q sig

class    (Extends ps qs ~ True) => (>=) ps qs
instance (Extends ps qs ~ True) => (>=) ps qs

class    (Strip lbl ~ sig) => (~=) sig lbl
instance (Strip lbl ~ sig) => (~=) sig lbl

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
    -> L.QualDict qs
    -> QualRep ps
    -> QualRep eps
    -> L.QualDict eps
    -> NatRep n
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('Const @(Put Nat) a)
       , ABeta ('L.Const @Nat a)
       )
annotateBeta b Nil l (S.SigConst) qs qsd ps eps epsd n = L.withKnownNat n $ 
    let b'   = atBeta b (Ann (AAt l (Proxy :: Proxy n))) n in
    let eps' = Q.QualPred (Proxy :: Proxy ('Put n)) eps in
    --
    let pn = Proxy :: Proxy ('Put n) in
    Q.witExtCons pn ps eps Refl |-
    L.thmGTSucc n eps undefined Refl |-
    L.witSuccGT @n |-
    --
    (EBeta b' eps' (L.succ n), l)
annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l (S.SigPart a sig) qs qsd ps eps epsd n
    | Refl :: Strip l :~: (x ':-> y) <- Refl
    , Refl :: l       :~: (Dress x 'L.:-> Dress y) <- Refl
    --
    = case annotateEta e a of
        (EEta (e' :: Eta (sym :&: Ann @r) exs x) exs, LEta (l' :: AEta lx) lr, xs)
          | Refl :: Strip lx :~: x <- Refl
          -> Q.witEUBoth ps eps xs exs Refl Refl |-
             L.witSPlain lr a Refl |-
             --
             let b'   = b :$ e' in
             let ps'  = Q.union ps xs in
             let eps' = Q.union eps exs in
             let l''  = AApp l l' in
             --
             undefined
             --annotateBeta b' as l'' sig ps' eps' _
annotateBeta b ((p@(Ev _) :: Ev p) :~ (as :: Args sym ys y)) l (S.SigPred pp sig) qs qsd ps eps epsd n
    | Refl :: qs :~: SmartApply ps ('T.Insert p ys) <- Refl
    , Refl :: qs :~: SmartApply (p ':. ps) ys <- Refl
    , Refl :: L.Greatest n qs :~: 'True <- Refl
    , Refl :: L.Greatest n eps :~: 'True <- Refl
    -- These should come from the qualdict
    , Refl :: 'Put x :~: p <- undefined -- Hmm...
    , Dict :: Dict (Typeable ('Put n)) <- undefined -- Hmm..
    --
    , Refl :: Elem p qs :~: 'True
        <- witElemPre
             (Proxy :: Proxy p)
             (undefined :: ArgsNRep ys)
             (ps :: QualRep ps)
    , Refl :: CmpNat n x :~: 'GT
        <- L.thmGTAny n
             (undefined :: NatRep x)
             (qs   :: QualRep qs)
             (qsd  :: L.QualDict qs)
             (Refl :: L.Greatest n qs :~: 'True)
             (Refl :: Elem p qs :~: 'True)
    , Refl :: L.Greatest n (p ':. eps) :~: 'True <- Refl
    --
    , Refl :: Elem ('Put n) (p ':. eps) :~: 'False
        <- L.thmGTUnique n
             (Q.QualPred pp eps :: QualRep (p ':. eps))
             (L.DictPred undefined epsd :: L.QualDict (p ':. eps))
             (Refl :: L.Greatest n (p ':. eps) :~: 'True)
    , Refl :: Remove ('Put n) (p ':. eps) :~: (p ':. eps)
        <- Q.witElemId
             (Proxy :: Proxy ('Put n))
             (Q.QualPred pp eps :: QualRep (p ':. eps))
             (Refl)
    --
    = let b'    = b :# p in
      let ps'   = Q.QualPred pp ps in
      let eps'  = Q.QualPred pp eps in
      let epsd' = L.DictPred undefined epsd in
      let l'    = AEApp l p in
      --
      annotateBeta b' as l' sig qs qsd ps' eps' epsd' n

annotateEta :: forall (sym :: Symbol (Put Nat) *) qs (n :: Nat) (m :: Nat) sig
    .  ( Sym sym
       , L.Rgn :<: sym
       )
    => Eta sym qs sig
    -> SigRep sig
    -> ( EEta (sym :&: Ann @Nat) ((>=) qs) sig
       , LEta @Nat ((~=) sig)
       , QualRep qs
       )
-- annotateEta (Spine b) (S.SigConst)
--     = case annotateASTF b undefined of
--         (EBeta (b' :: Beta (sym :&: Ann @r) eqs ('Const a)) eqs n, lr, qs)
--           --
--           -> let e  = Spine b' in
--              let sr = S.SigConst :: SigRep ('Const a) in
--              let l' = ASpine lr in
--              --
--              (EEta e eqs, LEta l' lr, qs)
-- todo: as I discard the annotation on 'b' here I need to make sure it's
--       already "stored" in 'b' somehow (as a decoration prob.).
-- todo: if I add 'Typeable' to regions in 'LblPred' I would need to prove
--       'Typeable p' here, which in turn means I would have to create fresh,
--       constrained type-variables (not sure if that's possible).
annotateEta (v :\ e) (S.SigPart b sig)
    | Refl :: sig :~: (b ':-> a) <- Refl
    --
    = case annotateEta e sig of
        (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs, LEta (l :: AEta l) lr, qs)
          --
          -> let e'' = v :\ e' :: Eta (sym :&: Ann @r) eqs (b ':-> a) in
             let l'  = ALam l  :: AEta (Dress b 'L.:-> l) in
             let lr' = L.LblPart (L.dress b) lr in
             --
             L.witSDIso b |-
             --
             (EEta e'' eqs, LEta l' lr', qs)
annotateEta (p@(Ev _ :: Ev p) :\\ e) (S.SigPred _ sig)
    = case annotateEta e sig of
        (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs, LEta (l :: AEta l) lr, qs)
          | Refl <- Q.witExtIn (Proxy :: Proxy p) qs eqs Refl Refl
          , Refl <- Q.witExtShrink (Proxy :: Proxy p) qs eqs Refl
          --
          -> let e''  = p :\\ e' :: Eta (sym :&: Ann @r) (Q.Remove p eqs) (p ':=> a) in
             let pp   = Proxy :: Proxy p in
             let qs'  = Q.remove pp qs in
             let eqs' = Q.remove pp eqs in
             let l'   = AELam p l in
             let lr'  = L.LblPred pp lr in
             --
             (EEta e'' eqs', LEta l' lr', qs')

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
    -> L.QualDict qs
    -> sym sig
    -> Args sym rs sig
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('Const @(Put Nat) a)
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
          annotateBeta (Sym (sym :&: a)) as (ASym sig) sig qs qsd none none L.DictNone n
    in
    (b, L.LblConst @a)    

-- | ...
annotateASTF :: forall (sym :: Symbol (Put Nat) *) (n :: Nat) qs a
    .  ( Sym sym
       , L.Rgn :<: sym
       , L.Greatest n qs ~ 'True
       )
    => NatRep n
    -> QualRep qs
    -> L.QualDict qs
    -> ASTF sym qs a
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('Const @(Put Nat) a)
       , LblRep ('L.Const @Nat a)
       )
annotateASTF n qs qsd = T.constMatch (annotateSym n qs qsd) undefined

annotate :: forall (sym :: Symbol (Put Nat) *) qs a
    .  ( Sym sym
       , L.Rgn :<: sym
       )
    => ASTF sym qs a
    -> EBeta (sym :&: Ann) ((>=) qs) ('Const a)
annotate ast = undefined -- fst (annotateASTF ast zero)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

type ArgsNRep :: T.Arguments (Put Nat) -> *
data ArgsNRep qs where
    ArgsEmpty  :: ArgsNRep ('T.Empty)
    ArgsUnion  :: QualRep qs -> ArgsNRep ps -> ArgsNRep ('T.Union qs ps)
    ArgsInsert :: NatRep n -> ArgsNRep qs -> ArgsNRep ('T.Insert ('Put n) qs)

type NArgs :: T.Arguments (Put Nat) -> Constraint
class NArgs qs where
    record :: ArgsNRep qs

--instance NArgs 
    
--------------------------------------------------------------------------------
-- ** ...

witArgsElem :: forall a as bs . Typeable a
    => Proxy a
    -> QualRep as
    -> ArgsNRep bs
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
-- todo: how to apply type 'True to witEqIf for c?

witElemPre :: forall a as bs . Typeable a
    => Proxy a
    -> ArgsNRep as
    -> QualRep bs
    -> Elem a (SmartApply bs ('T.Insert a as)) :~: 'True
witElemPre a as bs = witArgsElem a (Q.QualPred a bs) as Refl

--------------------------------------------------------------------------------
-- Fin.
