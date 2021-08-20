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

import Language.Diorite.Region.Labels

import Data.Constraint (Constraint, Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import qualified Data.IntMap as M

import Prelude hiding (lookup)

--------------------------------------------------------------------------------
-- * ...

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
