--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotation where

import Language.Diorite.Signatures (Signature, Result, SigRep, Sig)
import Language.Diorite.Qualifiers (Qualifier, Extends, QualRep)
import Language.Diorite.Syntax
import Language.Diorite.Traversal (SmartApply, Args(..))
import Language.Diorite.Decoration ((:&:)(..))
import Language.Diorite.Region.Labels (Put(..), Label, Strip, Dress, LblRep, Place)

import qualified Language.Diorite.Signatures as S
import qualified Language.Diorite.Qualifiers as Q
import qualified Language.Diorite.Qualifiers.Witness as W
import qualified Language.Diorite.Traversal as T
import qualified Language.Diorite.Region.Labels as L

import Data.Constraint (Dict(..), Constraint)
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))

import GHC.TypeNats

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

type LEta :: forall r . (Label r * -> Constraint) -> *
data LEta p where
    LEta :: p l => AEta l -> LblRep l -> LEta p

-- EBeta :: (p qs, q l) => Beta qs sig -> ABeta l -> QR qs -> EBeta sig p q
-- EEta  :: (p qs, q l) => Eta sym qs sig -> AEta l -> QR qs -> LR l -> SR sig -> EEta sym sig p q

data EBeta sym q sig where
    EBeta :: q qs => Beta sym qs sig -> QualRep qs -> EBeta sym q sig

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

annotateBeta :: forall (sym :: Symbol (Put Nat) *) qs ps eps rs sig l a
    .  ( Sym sym
       , Result sig ~ 'S.Const a
       , SmartApply ps rs ~ qs
       , Extends ps eps ~ 'True
       , Strip l ~ sig
       , Dress sig ~ l
       )
    => Beta (sym :&: Ann @Nat) eps sig
    -> Args sym rs sig
    -> ABeta @Nat l
    -> SigRep sig
    -> QualRep ps
    -> QualRep eps
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
       , ABeta ('L.Const @Nat a)
       , QualRep qs
       )
annotateBeta b Nil l (S.SigConst) ps eps =
    (EBeta b eps, l, ps)
annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l (S.SigPart a sig) ps eps
    | Refl :: Strip l :~: (x 'S.:-> y)             <- Refl
    , Refl :: l       :~: (Dress x 'L.:-> Dress y) <- Refl
    --
    = case annotateEta e a of
        (EEta (e' :: Eta (sym :&: Ann @r) exs x) exs, LEta (l' :: AEta lx) lr, xs)
          | Refl :: Strip lx :~: x <- Refl
          -> W.witEUBoth ps eps xs exs Refl Refl |-
             L.witSPlain lr a Refl |-
             --
             let b'   = b :$ e' in
             let ps'  = Q.union ps xs in
             let eps' = Q.union eps exs in
             let l''  = AApp l l' in
             --
             annotateBeta b' as l'' sig ps' eps'
annotateBeta b ((p@(Ev _) :: Ev p) :~ (as :: Args sym ys y)) l (S.SigPred pp sig) ps eps
    = let b'   = b :# p in
      let ps'  = Q.QualPred pp ps in
      let eps' = Q.QualPred pp eps in
      let l'   = AEApp l p in
      --
      annotateBeta b' as l' sig ps' eps'

annotateEta :: forall (sym :: Symbol (Put Nat) *) qs sig
    .  ( Sym sym
       )
    => Eta sym qs sig
    -> SigRep sig
    -> ( EEta (sym :&: Ann @Nat) ((>=) qs) sig
       , LEta @Nat ((~=) sig)
       , QualRep qs
       )
annotateEta (Spine b) (S.SigConst)
    = case annotateASTF b of
        (EBeta (b' :: Beta (sym :&: Ann @r) eqs ('S.Const a)) eqs, lr, qs)
          --
          -> let e  = Spine b' in
             let sr = S.SigConst :: SigRep ('S.Const a) in
             let l' = ASpine lr in
             --
             (EEta e eqs, LEta l' lr, qs)
-- todo: as I discard the annotation on 'b' here I need to make sure it's
--       already "stored" in 'b' somehow (as a decoration prob.).
-- todo: if I add 'Typeable' to regions in 'LblPred' I would need to prove
--       'Typeable p' here, which in turn means I would have to create fresh,
--       constrained type-variables (not sure if that's possible).
annotateEta (n :\ e) (S.SigPart b sig)
    | Refl :: sig :~: (b 'S.:-> a) <- Refl
    --
    = case annotateEta e sig of
        (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs, LEta (l :: AEta l) lr, qs)
          --
          -> let e'' = n :\ e' :: Eta (sym :&: Ann @r) eqs (b 'S.:-> a) in
             let l'  = ALam l  :: AEta (Dress b 'L.:-> l) in
             let lr' = L.LblPart (L.dress b) lr in
             --
             L.witSDIso b |-
             --
             (EEta e'' eqs, LEta l' lr', qs)
annotateEta (p@(Ev _ :: Ev p) :\\ e) (S.SigPred _ sig)
    = case annotateEta e sig of
        (EEta (e' :: Eta (sym :&: Ann @r) eqs a) eqs, LEta (l :: AEta l) lr, qs)
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
             (EEta e'' eqs', LEta l' lr', qs')

--------------------------------------------------------------------------------

-- todo: Given a Beta/Eta, give me a "fresh" type.
-- cant be a "forall-type" since I need Typeable.
-- could be a Nat, but then I need to convice GHC that the Nats I produce are "fresh"

--nextBetaEv :: Beta sym qs sig -> EvNat (qs)
--nextBetaEv b = EvNat (maxEvBeta b + 1)

annotateASTF :: forall (sym :: Symbol (Put Nat) *) (p :: Nat) qs a
    .  (Sym sym)
    => ASTF sym qs a
    -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
       , LblRep ('L.Const @Nat a 'L.:^ p)
       , QualRep qs
       )
annotateASTF ast = T.constMatch matchSym matchVar ast
  where    
    matchSym :: forall rs sig
        .  ( Result sig ~ 'S.Const a
           , SmartApply 'Q.None rs ~ qs
           )
        => sym sig -> Args sym rs sig
        -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
           , LblRep ('L.Const @Nat a 'L.:^ p)
           , QualRep qs
           )
    matchSym sym as
        = let sig  = symbol sym in
          let none = Q.QualNone in
          --
          L.witSDIso sig |-
          S.witTypeable (S.result sig) |-
          --
          let ((b, l, qs), tr) =
                let pp  = Proxy :: Proxy p in
                let a   = Ann (AAt l pp) in
                let tr' = L.LblAt pp (L.LblConst :: LblRep ('L.Const a)) in
                (annotateBeta (Sym (sym :&: a)) as (ASym sig) sig none none, tr')
          in
          --
          (b, tr, qs)

    matchVar :: forall ps rs sig
        .  ( Result sig ~ 'S.Const a
           , SmartApply ps rs ~ qs
           , Sig sig
           )
        => Name -> QualRep ps -> Args sym rs sig
        -> ( EBeta (sym :&: Ann @Nat) ((>=) qs) ('S.Const @(Put Nat) a)
           , LblRep ('L.Const @Nat a 'L.:^ p)
           , QualRep qs
           )
    matchVar = undefined

annotate :: forall (sym :: Symbol (Put Nat) *) qs a . Sym sym => ASTF sym qs a -> EBeta (sym :&: Ann) ((>=) qs) ('S.Const a)
annotate ast = let (b, _, _) = annotateASTF ast in b

--------------------------------------------------------------------------------
-- Fin.
