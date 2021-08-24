--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotation where

import Language.Diorite.Signatures (Signature, Result, SigRep, Sig)
import Language.Diorite.Qualifiers (Qualifier, Extends, QualRep)
import Language.Diorite.Syntax
import Language.Diorite.Traversal (SmartApply, Args(..))
--import Language.Diorite.Decoration
import Language.Diorite.Region.Labels (Put(..), Label, Strip, Dress, LblRep, Place)

import qualified Language.Diorite.Signatures as S
import qualified Language.Diorite.Qualifiers as Q
import qualified Language.Diorite.Qualifiers.Witness as W
import qualified Language.Diorite.Traversal as T
import qualified Language.Diorite.Region.Labels as L

import Data.Constraint (Dict(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

type ABeta :: forall r . Label r * -> *
data ABeta l where
    ASym   :: SigRep sig -> ABeta (Dress sig)
    AApp   :: L.Plain b ~ a => ABeta (a 'L.:-> sig) -> AEta b -> ABeta sig
    AEApp  :: ABeta (p 'L.:=> sig) -> Ev p -> ABeta sig

type AEta :: forall r . Label r * -> *
data AEta l where
    ASpine :: LblRep ('L.Const a) -> AEta ('L.Const a)
    ALam   :: AEta sig -> AEta (a 'L.:-> sig)
    AELam  :: Ev p -> AEta sig -> AEta (p 'L.:=> sig)
-- todo: actually lable things.

data EBeta sym sig p q where
    EBeta :: (p qs, q l) => Beta sym qs sig -> ABeta l
        -> QualRep qs
        -> EBeta sym sig p q

data EEta sym sig p q where
    EEta :: (p qs, q l) => Eta sym qs sig -> AEta l
        -> QualRep qs -> LblRep l -> SigRep sig
        -> EEta sym sig p q

class    (Extends ps qs ~ True) => (>=) ps qs
instance (Extends ps qs ~ True) => (>=) ps qs

class    (Strip lbl ~ sig) => (~=) sig lbl
instance (Strip lbl ~ sig) => (~=) sig lbl

--------------------------------------------------------------------------------
-- ** ...

annotateBeta :: forall r (sym :: Symbol (Put r) *) qs ps eps rs sig l a
    .  ( Sym sym
       , Result sig ~ 'S.Const a
       , SmartApply ps rs ~ qs
       , Extends ps eps ~ 'True
       , Strip l ~ sig
       , Dress sig ~ l
       )
    => Beta sym eps sig
    -> Args sym rs sig
    -> ABeta @r l
    -> QualRep ps
    -> QualRep eps
    -> ( EBeta sym ('S.Const @(Put r) a) ((>=) qs) ((~=) ('S.Const @(Put r) a))
       , QualRep qs
       )
annotateBeta b Nil l ps eps =
    (EBeta b l eps, ps)
annotateBeta b ((e :: Eta sym xs x) :* (as :: Args sym ys y)) l ps eps
    | Refl :: Strip l :~: (x 'S.:-> y)             <- Refl
    , Refl :: l       :~: (Dress x 'L.:-> Dress y) <- Refl
    --
    = case annotateEta e of
        (EEta (e' :: Eta sym exs x) (l' :: AEta lx) exs lr xr, xs)
          | Refl :: Strip lx :~: x <- Refl
          --
          -> W.witEUBoth ps eps xs exs Refl Refl |-
             L.witSPlain lr xr Refl |-
             --
             let b'   = b :$ e' in
             let ps'  = Q.union ps xs in
             let eps' = Q.union eps exs in
             let l''  = AApp l l' in
             --
             annotateBeta b' as l'' ps' eps'
annotateBeta b ((p@(Ev _) :: Ev p) :~ (as :: Args sym ys y)) l ps eps
    = let b'   = b :# p in
      let ps'  = Q.QualPred (Proxy :: Proxy p) ps in
      let eps' = Q.QualPred (Proxy :: Proxy p) eps in
      let l'   = AEApp l p in
      --
      annotateBeta b' as l' ps' eps'

annotateEta :: forall r (sym :: Symbol (Put r) *) qs sig
    .  ( Sym sym
       )
    => Eta sym qs sig
    -> ( EEta sym sig ((>=) qs) ((~=) sig)
       , QualRep qs
       )
annotateEta (Spine b)
    = case annotateASTF b of
        (EBeta (b' :: Beta sym eqs ('S.Const a)) l eqs, qs)
          | Dict :: Dict (Typeable a) <- undefined
          --
          -> let e  = Spine b' in
             let lr = L.LblConst :: LblRep ('L.Const a) in
             let sr = S.SigConst :: SigRep ('S.Const a) in
             let l' = ASpine lr in
             --
             (EEta e l' eqs lr sr, qs)
annotateEta (n :\ e)
    | Refl :: sig :~: (b 'S.:-> a) <- Refl
    --
    = case annotateEta e of
        (EEta (e' :: Eta sym eqs a) (l :: AEta l) eqs lr sr, qs)
          -> let e'' = n :\ e' :: Eta sym eqs (b 'S.:-> a) in
             let l'  = ALam l  :: AEta (Dress b 'L.:-> l) in
             let sig = S.signature :: SigRep b in
             let sr' = S.SigPart sig sr in
             let lr' = L.LblPart (L.dress sig) lr in
             --
             L.witSDIso sig |-
             --
             (EEta e'' l' eqs lr' sr', qs)
annotateEta (p@(Ev _ :: Ev p) :\\ e)
    = case annotateEta e of
        (EEta (e' :: Eta sym eqs a) (l :: AEta l) eqs lr sr, qs)
          | Refl <- W.witExtIn (Proxy :: Proxy p) qs eqs Refl Refl
          , Refl <- W.witExtShrink (Proxy :: Proxy p) qs eqs Refl
          --
          -> let e''  = p :\\ e' :: Eta sym (Q.Remove p eqs) (p 'S.:=> a) in
             let qs'  = Q.remove (Proxy :: Proxy p) qs in
             let eqs' = Q.remove (Proxy :: Proxy p) eqs in
             let l'   = AELam p l in
             let sr'  = S.SigPred (Proxy :: Proxy p) sr in
             let lr'  = L.LblPred (Proxy :: Proxy p) lr in
             --
            (EEta e'' l' eqs' lr' sr', qs')

--------------------------------------------------------------------------------

-- | ...
annotateASTF :: forall r (sym :: Symbol (Put r) *) qs a
    .  ( Sym sym 
       )
    => ASTF sym qs a
    -> ( EBeta sym ('S.Const @(Put r) a) ((>=) qs) ((~=) ('S.Const @(Put r) a))
       , QualRep qs
       )
annotateASTF ast = T.constMatch matchSym matchVar ast
  where
    matchSym :: forall rs sig
        .  ( Result sig ~ 'S.Const a
           , SmartApply 'Q.None rs ~ qs
           )
        => sym sig -> Args sym rs sig
        -> ( EBeta sym ('S.Const @(Put r) a) ((>=) qs) ((~=) ('S.Const @(Put r) a))
           , QualRep qs
           )
    matchSym sym as
        = let sig = symbol sym in
          --
          L.witSDIso sig |-
          --
          annotateBeta (Sym sym) as (ASym sig) (Q.QualNone) (Q.QualNone)

    matchVar :: forall ps rs sig
        .  ( Result sig ~ 'S.Const a
           , SmartApply ps rs ~ qs
           , Sig sig
           )
        => Name -> QualRep ps -> Args sym rs sig
        -> ( EBeta sym ('S.Const @(Put r) a) ((>=) qs) ((~=) ('S.Const @(Put r) a))
           , QualRep qs
           )
    matchVar = undefined

--------------------------------------------------------------------------------
-- Fin.
