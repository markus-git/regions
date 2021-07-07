{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE EmptyCase #-}

module Language.Diorite.Qualifiers.Witness where

import Language.Diorite.Qualifiers

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

--------------------------------------------------------------------------------
-- *** Witnesses of various Qualifier properties.

witEqRefl :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> (a == b) :~: (b == a)
witEqRefl a b =
  case test a b of
      Left  Refl -> Refl
      Right Refl -> case test b a of
          Left  x    -> case x of {}
          Right Refl -> Refl
{-# NOINLINE witEqRefl #-}
{-# RULES "witEqRefl" forall a b . witEqRefl a b = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Insert.

witInsIdem :: Typeable a => Proxy a -> QualRep b -> Insert a (Insert a b) :~: Insert a b
witInsIdem _ (QualNone) = Refl
witInsIdem a (QualPred b bs) | Refl <- witInsIdem a bs =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> Refl
{-# NOINLINE witInsIdem #-}
{-# RULES "witInsIdem" forall a b . witInsIdem a b = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Remove.

witRemOrd :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> Remove a (Remove b c) :~: Remove b (Remove a c)
witRemOrd _ _ (QualNone) = Refl
witRemOrd a b (QualPred c cs) | Refl <- witRemOrd a b cs =
    case (test a c, test b c) of
        (Left  Refl, Left  Refl) -> Refl
        (Left  Refl, Right Refl) -> Refl
        (Right Refl, Left  Refl) -> Refl
        (Right Refl, Right Refl) -> Refl
{-# NOINLINE witRemOrd #-}
{-# RULES "witRemOrd" forall a b c . witRemOrd a b c = Unsafe.unsafeCoerce Refl #-}

witRemDist :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
witRemDist _ (QualNone) _ = Refl
witRemDist a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case (lhs, rhs) of
            (Refl, Refl) -> Refl
  where
    lhs :: (q ':. Remove a (Union qs (Remove q c))) :~: (q ':. Union (Remove a qs) (Remove a (Remove q c)))
    lhs | Refl <- witRemDist a bs (remove b c) = Refl

    rhs :: Union (q ':. Remove a qs) (Remove a c) :~: (q ':. Union (Remove a qs) (Remove a (Remove q c)))
    rhs | Refl <- witRemOrd a b c = Refl
{-# NOINLINE witRemDist #-}
{-# RULES "witRemDist" forall a b c . witRemDist a b c = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Union.

witUniIdent :: QualRep a -> Union a 'None :~: a
witUniIdent (QualNone) = Refl
witUniIdent (QualPred _ as) | Refl <- witUniIdent as = Refl
{-# NOINLINE witUniIdent #-}
{-# RULES "witUniIdent" forall a . witUniIdent a = Unsafe.unsafeCoerce Refl #-}

witUniAssoc :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Union a (Union b c) :~: Union (Union a b) c
witUniAssoc (QualNone) _ _ = Refl
witUniAssoc (QualPred (a :: Proxy q) (as :: QualRep qs)) b c =
    case (lhs, rhs) of
        (Refl, Refl) -> Refl
  where
    lhs :: Union (q ':. qs) (Union b c) :~: (q ':. Union qs (Union (Remove q b) (Remove q c)))
    lhs | Refl <- witRemDist a b c = Refl
    
    rhs :: Union (Union (q ':. qs) b) c :~: (q ':. Union qs (Union (Remove q b) (Remove q c)))
    rhs | Refl <- witUniAssoc as (remove a b) (remove a c) = Refl
{-# NOINLINE witUniAssoc #-}
{-# RULES "witUniAssoc" forall a b c . witUniAssoc a b c = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Elem.

witElemCons :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Elem a (Union b (a ':. c)) :~: 'True
witElemCons _ (QualNone) _ = Refl
witElemCons a (QualPred b bs) c =
    case test a b of
        Left  Refl -> Refl
        Right Refl | Refl <- witEqRefl a b, Refl <- witElemCons a bs (remove b c) -> Refl
{-# NOINLINE witElemCons #-}
{-# RULES "witElemCons" forall a b c . witElemCons a b c = Unsafe.unsafeCoerce Refl #-}

witElemRem :: forall a b c . (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> a :/~: b -> Elem a c :~: Elem a (Remove b c)
witElemRem _ _ (QualNone) Refl = Refl
witElemRem a b (QualPred c cs) Refl =
    case test b c of
        Left  Refl -> Refl
        Right Refl -> case test a c of
            Left  Refl -> Refl
            Right Refl | Refl <- witElemRem a b cs Refl -> Refl
{-# NOINLINE witElemRem #-}
{-# RULES "witElemRem" forall a b c . witElemRem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniRem :: forall a b c cs . Typeable a => Proxy a -> QualRep b -> QualRep (c ':. cs) -> a :/~: c -> Elem a (Union b cs) :~: Elem a (Union b (Remove c cs))
witElemUniRem a (QualNone) (QualPred c cs) Refl | Refl <- witElemRem a c cs Refl = Refl
witElemUniRem a (QualPred b bs) (QualPred c cs) Refl =
    case test a b of
        Left  Refl -> Refl
        Right Refl | Refl <- witRemOrd c b cs, Refl <- witElemUniRem a bs (QualPred c (remove b cs)) Refl -> Refl
{-# NOINLINE witElemUniRem #-}
{-# RULES "witElemUniRem" forall a b c . witElemUniRem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemSub :: forall a b c cs . Typeable a => Proxy a -> QualRep b -> QualRep (c ':. cs) -> a :/~: c -> Elem a (Union b cs) :~: Elem a (Union b (c ':. cs))
witElemSub _ (QualNone) _ Refl = Refl
witElemSub a (QualPred b bs) (QualPred c cs) Refl =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case test b c of
            Left  Refl | Refl <- witElemUniRem a bs (QualPred c cs) Refl -> Refl
            Right Refl | Refl <- witElemSub a bs (QualPred c (remove b cs)) Refl -> Refl
{-# NOINLINE witElemSub #-}
{-# RULES "witElemSub" forall a b c . witElemSub a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemRefl :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Elem a (Union b c) :~: Elem a (Union c b)
witElemRefl _ (QualNone) c | Refl <- witUniIdent c = Refl
witElemRefl a x@(QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
    case test a b of
        Left  Refl | Refl <- witElemCons a c bs -> Refl
        Right Refl | Refl <- witElemRefl a bs c, Refl <- witElemSub a c x Refl, Refl <- witElemUniRem a bs (QualPred b c) Refl -> Refl
{-# NOINLINE witElemRefl #-}
{-# RULES "witElemRefl" forall a b c . witElemRefl a b c = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Subset.

witSubElem :: forall a as b . QualRep (a ':. as) -> QualRep b -> Subset (a ':. as) b :~: 'True -> Elem a b :~: 'True
witSubElem (QualPred a _) b Refl =
    case testElem a b of
        Left  Refl -> Refl
        Right x    -> case x of {}
{-# NOINLINE witSubElem #-}
{-# RULES "witSubElem" forall a b . witSubElem a b Refl = Unsafe.unsafeCoerce Refl #-}

witSubRemL :: forall a as b . QualRep (a ':. as) -> QualRep b -> Subset (a ':. as) b :~: 'True -> Subset as b :~: 'True
witSubRemL a b Refl | Refl <- witSubElem a b Refl = Refl
{-# NOINLINE witSubRemL #-}
{-# RULES "witSubRemL" forall a b . witSubRemL a b Refl = Unsafe.unsafeCoerce Refl #-}

witSubCons :: forall a b c . Typeable c => QualRep a -> QualRep b -> Proxy c -> Subset a b :~: 'True -> Subset a (c ':. b) :~: 'True
witSubCons (QualNone) _ _ _ = Refl
witSubCons (QualPred a as) b c Refl =
    case test a c of
        Left  Refl | Refl <- witSubRemL (QualPred a as) b Refl, Refl <- witSubCons as b c Refl -> Refl
        Right Refl | Refl <- witSubElem (QualPred a as) b Refl, Refl <- witSubCons as b c Refl -> Refl
{-# NOINLINE witSubCons #-}
{-# RULES "witSubCons" forall a b c . witSubCons a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRefl :: forall a . QualRep a -> Subset a a :~: 'True
witSubRefl (QualNone) = Refl
witSubRefl (QualPred a as) | Refl <- witSubRefl as, Refl <- witSubCons as as a Refl = Refl
{-# NOINLINE witSubRefl #-}
{-# RULES "witSubRefl" forall a . witSubRefl a = Unsafe.unsafeCoerce Refl #-}

witSubIn :: forall a b c . Typeable c => QualRep a -> QualRep b -> Proxy c -> Subset a b :~: 'True -> Elem c a :~: 'True -> Elem c b :~: 'True
witSubIn x@(QualPred a as) b c Refl Refl =
    case test c a of
        Left  Refl | Refl <- witSubElem x b Refl -> Refl
        Right Refl | Refl <- witSubRemL x b Refl, Refl <- witSubIn as b c Refl Refl -> Refl
{-# NOINLINE witSubIn #-}
{-# RULES "witSubIn" forall a b c . witSubIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubTrans :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
witSubTrans (QualNone) _ _ _ _ = Refl
witSubTrans x@(QualPred a as) b c Refl Refl
    | Refl <- witSubElem x b Refl
    , Refl <- witSubIn b c a Refl Refl
    , Refl <- witSubTrans as b c Refl Refl
    = Refl
{-# NOINLINE witSubTrans #-}
{-# RULES "witSubTrans" forall a b c . witSubTrans a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubUniRemR :: forall a b bs . QualRep a -> QualRep (b ':. bs) -> Subset (Union (Remove b a) bs) (Union a (b ':. bs)) :~: 'True
witSubUniRemR (QualNone) (QualPred b bs) | Refl <- witSubRefl bs, Refl <- witSubCons bs bs b Refl = Refl
witSubUniRemR (QualPred (a :: Proxy q) (as :: QualRep qs)) (QualPred b bs) =
    let x :: QualRep (Union qs bs) = union as bs in
    let y :: QualRep (Remove q bs) = remove a bs in
    case test a b of
        Left  Refl | Refl <- witSubRefl x, Refl <- witSubCons x x b Refl -> Refl
        Right Refl
            | Refl <- witEqRefl a b
            , Refl <- witSubUniRemR as (QualPred b y)
            , Refl <- witSubCons (union (remove b as) y) (union as (QualPred b y)) a Refl
            -> Refl
{-# NOINLINE witSubUniRemR #-}
{-# RULES "witSubUniRemR" forall a b . witSubUniRemR a b = Unsafe.unsafeCoerce Refl #-}

witSubUniRefl :: forall a b . QualRep a -> QualRep b -> Subset (Union a b) (Union b a) :~: 'True
witSubUniRefl (QualNone) b
    | Refl <- witUniIdent b
    , Refl <- witSubRefl b
    = Refl
witSubUniRefl o@(QualPred (a :: Proxy q) (as :: QualRep qs)) b
    | Refl <- witElemCons a b as
    , Refl <- witSubUniRefl as (remove a b)
    , Refl <- witSubUniRemR b o
    = let x :: QualRep (Union qs (Remove q b)) = union as (remove a b) in
      let y :: QualRep (Union (Remove q b) qs) = union (remove a b) as in
      let z :: QualRep (Union b (q ':. qs))    = union b o in
      case witSubTrans x y z Refl Refl of 
          Refl -> Refl
{-# NOINLINE witSubUniRefl #-}
{-# RULES "witSubUniRefl" forall a b . witSubUniRefl a b = Unsafe.unsafeCoerce Refl #-}

--witSubUniL :: forall a as b . QualRep (a ':. as) -> QualRep b -> Subset (Union as (a ':. b)) (Union (a ':. as) b) :~: 'True
--witSubUniL (QualPred _ _) _ = undefined
--
-- Subset (Union ps rs) qs
--   > ps ~ (x?:xs?)
-- Subset (Union (x?:xs?) rs) qs
-- ???
-- Subset (Union xs? (x?:rs)) qs
--
-- ???:
--   > Prove: Subset (Union xs? (x?:rs)) (Union (x?:xs?) rs)
--   > Then by trans and: Subset (Union (x?:xs?) rs) qs
-- Subset (Union xs? (x?:rs)) qs

--------------------------------------------------------------------------------
-- Fin.
