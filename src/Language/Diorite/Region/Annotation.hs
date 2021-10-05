--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotation where

import Language.Diorite.Signatures (Signature, Result, SigRep, Sig)
import Language.Diorite.Qualifiers (Qualifier(..), Elem, Remove, Extends, QualRep)
import Language.Diorite.Syntax
import Language.Diorite.Traversal (SmartApply, Args(..))
import Language.Diorite.Decoration ((:&:)(..))
import Language.Diorite.Region.Labels (Put(..), Label, Strip, Dress, LblRep, Place)
import Language.Diorite.Region.Labels.Witness (NatRep(..), zero, succ, withKnownNat)
import qualified Language.Diorite.Signatures as S
import qualified Language.Diorite.Qualifiers as Q
import qualified Language.Diorite.Qualifiers.Witness as W
import qualified Language.Diorite.Traversal as T
import qualified Language.Diorite.Decoration as D
import qualified Language.Diorite.Region.Labels as L
import qualified Language.Diorite.Region.Labels.Witness as W

import Data.Constraint (Dict(..), Constraint)
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))
import Numeric.Natural (Natural)

import GHC.TypeNats

import Prelude hiding (succ)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

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
-- todo: actually lable things.

--------------------------------------------------------------------------------
-- ** ...

type LEta :: forall r . (Label r * -> Constraint) -> *
data LEta p where
    LEta :: p l => AEta l -> LblRep l -> LEta p

type EBeta :: forall p
    . Symbol p * -> (Qualifier p -> Constraint) -> Signature p * -> *
data EBeta sym q sig where
    EBeta :: q qs => Beta sym qs sig -> QualRep qs -> EBeta sym q sig

type EEta :: forall p
    . Symbol p * -> (Qualifier p -> Constraint) -> Signature p * -> *
data EEta sym q sig where
    EEta :: q qs => Eta sym qs sig -> QualRep qs -> EEta sym q sig

class    (Extends ps qs ~ True) => (>=) ps qs
instance (Extends ps qs ~ True) => (>=) ps qs

class    (Strip lbl ~ sig) => (~=) sig lbl
instance (Strip lbl ~ sig) => (~=) sig lbl

type Ann :: forall r . Signature (Put r) * -> *
data Ann sig where
    Ann :: ABeta ('L.Const a 'L.:^ p) -> Ann ('S.Const a)

--------------------------------------------------------------------------------
-- ** ...

ev :: KnownNat p => NatRep p -> Place p
ev (Nat p) = Ev (fromInteger $ toInteger p)

local :: forall (sym :: Symbol (Put Nat) *) qs a (p :: Nat)
    .  (L.Rgn :<: sym, Elem ('Put p) qs ~ 'True)
    => NatRep p
    -> Ann ('S.Const @(Put Nat) a)
    -> Beta (sym :&: Ann) qs ('S.Const a)
    -> Beta (sym :&: Ann) (Remove ('Put p) qs) ('S.Const a)
local p i ast = withKnownNat p $ L.local (ev p) i ast

atBeta :: forall (sym :: Symbol (Put Nat) *) qs a (p :: Nat)
    .  (L.Rgn :<: sym, Remove ('Put p) qs ~ qs)
    => Beta (sym :&: Ann) qs ('S.Const a)
    -> Ann ('S.Const @(Put Nat) a)
    -> NatRep p
    -> Beta (sym :&: Ann) ('Put p ':. qs) ('S.Const a)
atBeta ast i p = withKnownNat p $ L.atBeta ast i (ev p)

atEta :: forall (sym :: Symbol (Put Nat) *) qs sig (p :: Nat)
    .  (L.Rgn :<: sym, Remove ('Put p) qs ~ qs)
    => Eta (sym :&: Ann) qs sig
    -> Ann (Result sig)
    -> NatRep p
    -> Beta (sym :&: Ann) ('Put p ':. qs) sig
atEta ast i p = withKnownNat p $ L.atEta ast i (ev p)

--------------------------------------------------------------------------------
-- ** ...

type GNat :: Qualifier (Put Nat) -> *
data GNat qs where
    GNat :: L.Greatest n qs ~ 'True => NatRep n -> QualRep qs -> GNat qs

-- type Free :: forall r
--     . Label r * -> Qualifier (Put r) -> Qualifier (Put r) -> Qualifier (Put r)
-- type family Free lbl qs ps where
--     Free ('L.Const a) qs ps = ps
--     Free (a 'L.:-> b) qs ps = Free ...

-- free :: LblRep lbl -> QualRep qs -> QualRep (Free lbl qs 'None)
-- free = undefined

--------------------------------------------------------------------------------
-- ** ...

annotateBeta :: forall (sym :: Symbol (Put Nat) *) qs ps eps rs sig l (n :: Nat) a
    .  ( Sym sym
       , Result sig ~ 'S.Const a
       , L.Rgn :<: sym
       -- Needed for (>= qs)
       , SmartApply ps rs ~ qs
       , Extends ps eps ~ 'True
       , Strip l ~ sig
       , Dress sig ~ l
       -- Needed for unique nat
       , L.Greatest n eps ~ 'True
       , Remove ('Put n) eps ~ eps
       )
    => Beta (sym :&: Ann @Nat) eps sig
    -> Args sym rs sig
    -> ABeta @Nat l
    -> SigRep sig
    -> QualRep ps
    -> QualRep eps
    -> NatRep n
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
       , ABeta ('L.Const @Nat a)
       , QualRep qs
       , GNat ('Put n ':. eps)
       )
annotateBeta b Nil l (S.SigConst) ps eps n =
    let b'   = atBeta b (Ann (AAt l (Proxy :: Proxy n))) n in
    let eps' = withKnownNat n $ Q.QualPred (Proxy :: Proxy ('Put n)) eps in
    let n'   = succ n in
    --
    withKnownNat n (W.witExtCons (Proxy :: Proxy ('Put n)) ps eps Refl) |-
    L.thmGreatestSucc n eps undefined Refl |-
    W.witSuccGT @n |-
    --
    (EBeta b' eps', l, ps, GNat n' eps')
annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l (S.SigPart a sig) ps eps n
    | Refl :: Strip l :~: (x 'S.:-> y)             <- Refl
    , Refl :: l       :~: (Dress x 'L.:-> Dress y) <- Refl
    --
    = case annotateEta e a n of
        (EEta (e' :: Eta (sym :&: Ann @r) exs x) exs, LEta (l' :: AEta lx) lr, xs, _)
          | Refl :: Strip lx :~: x <- Refl
          -> W.witEUBoth ps eps xs exs Refl Refl |-
             L.witSPlain lr a Refl |-
             --
             let b'   = b :$ e' in
             let ps'  = Q.union ps xs in
             let eps' = Q.union eps exs in
             let l''  = AApp l l' in
             --
             undefined
             -- annotateBeta b' as l'' sig ps' eps' _
annotateBeta b ((p@(Ev _) :: Ev p) :~ (as :: Args sym ys y)) l (S.SigPred pp sig) ps eps n
    = let b'   = b :# p in
      let ps'  = Q.QualPred pp ps in
      let eps' = Q.QualPred pp eps in
      let l'   = AEApp l p in
      --
      annotateBeta b' as l' sig ps' eps' n
      -- todo: doesn't work, since eps in the result type ties it to the input
      -- and that fials here. Might need to put the nat into the EBeta to hide
      -- it. Since we don't really care what it is, only that its the "greatest",
      -- that should work fine.

annotateEta :: forall (sym :: Symbol (Put Nat) *) qs (n :: Nat) (m :: Nat) sig
    .  ( Sym sym
       , L.Rgn :<: sym
       )
    => Eta sym qs sig
    -> SigRep sig
    -> NatRep n
    -> ( EEta (sym :&: Ann @Nat) ((>=) qs) sig
       , LEta @Nat ((~=) sig)
       , QualRep qs
       , ()
       )
annotateEta (Spine b) (S.SigConst) n
    = case annotateASTF b n of
        (EBeta (b' :: Beta (sym :&: Ann @r) eqs ('S.Const a)) eqs, lr, qs, _)
          --
          -> let e  = Spine b' in
             let sr = S.SigConst :: SigRep ('S.Const a) in
             let l' = ASpine lr in
             --
             (EEta e eqs, LEta l' lr, qs, undefined)
-- todo: as I discard the annotation on 'b' here I need to make sure it's
--       already "stored" in 'b' somehow (as a decoration prob.).
-- todo: if I add 'Typeable' to regions in 'LblPred' I would need to prove
--       'Typeable p' here, which in turn means I would have to create fresh,
--       constrained type-variables (not sure if that's possible).
annotateEta (v :\ e) (S.SigPart b sig) n
    | Refl :: sig :~: (b 'S.:-> a) <- Refl
    --
    = case annotateEta e sig n of
        (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs, LEta (l :: AEta l) lr, qs, _)
          --
          -> let e'' = v :\ e' :: Eta (sym :&: Ann @r) eqs (b 'S.:-> a) in
             let l'  = ALam l  :: AEta (Dress b 'L.:-> l) in
             let lr' = L.LblPart (L.dress b) lr in
             --
             L.witSDIso b |-
             --
             (EEta e'' eqs, LEta l' lr', qs, undefined)
annotateEta (p@(Ev _ :: Ev p) :\\ e) (S.SigPred _ sig) n
    = case annotateEta e sig n of
        (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs, LEta (l :: AEta l) lr, qs, _)
          | Refl <- W.witExtIn (Proxy :: Proxy p) qs eqs Refl Refl
          , Refl <- W.witExtShrink (Proxy :: Proxy p) qs eqs Refl
          --
          -> let e''  = p :\\ e' :: Eta (sym :&: Ann @r) (Q.Remove p eqs) (p 'S.:=> a) in
             let pp   = Proxy :: Proxy p in
             let qs'  = Q.remove pp qs in
             let eqs' = Q.remove pp eqs in
             let l'   = AELam p l in
             let lr'  = L.LblPred pp lr in
             --
             (EEta e'' eqs', LEta l' lr', qs', undefined)

--------------------------------------------------------------------------------

annotateASTF :: forall (sym :: Symbol (Put Nat) *) (n :: Nat) qs a
    .  ( Sym sym
       , L.Rgn :<: sym
       )
    => ASTF sym qs a
    -> NatRep n
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
       , LblRep ('L.Const @Nat a 'L.:^ n)
       , QualRep qs
       , ()
       )
annotateASTF ast n = undefined -- T.constMatch matchSym matchVar ast
  where
    matchSym :: forall rs sig
        .  ( Result sig ~ 'S.Const a
           , SmartApply 'Q.None rs ~ qs
           )
        => sym sig
        -> Args sym rs sig
        -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
           , LblRep ('L.Const @Nat a 'L.:^ n)
           , QualRep qs
           , ()
           )
    matchSym sym as
        = let sig  = symbol sym in
          let none = Q.QualNone in
          --
          L.witSDIso sig |-
          S.witTypeable (S.result sig) |-
          --
          let pp = Proxy :: Proxy p in
          let tr = L.LblAt pp (L.LblConst :: LblRep ('L.Const a)) in
          let (b, l, qs, _) =
                let a = Ann (AAt l pp) in
                annotateBeta (Sym (sym :&: a)) as (ASym sig) sig none none n
          in
          --
          (b, tr, qs, undefined)

    matchVar :: forall ps rs sig
        .  ( Result sig ~ 'S.Const a
           , SmartApply ps rs ~ qs
           , Sig sig
           )
        => Name
        -> QualRep ps
        -> Args sym rs sig
        -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
           , LblRep ('L.Const @Nat a 'L.:^ n)
           , QualRep qs
           , ()
           )
    matchVar = undefined

annotate :: forall (sym :: Symbol (Put Nat) *) qs a
    .  ( Sym sym
       , L.Rgn :<: sym
       )
    => ASTF sym qs a
    -> EBeta (sym :&: Ann) ((>=) qs) ('S.Const a)
annotate ast = let (b, _, _, _) = annotateASTF ast zero in b

--------------------------------------------------------------------------------
-- Fin.
