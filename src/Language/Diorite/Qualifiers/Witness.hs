{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE EmptyCase #-}

module Language.Diorite.Qualifiers.Witness where

import Language.Diorite.Qualifiers

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

--------------------------------------------------------------------------------
-- * Witnesses for various 'Qualifier' properties.
--
-- > General:
-- witEqRefl        :: (a == b) :~: (b == a)
--
-- > Insert:
-- witInsIdem       :: Insert a (Insert a b) :~: Insert a b
--
-- > Remove:
-- witRemOrd        :: Remove a (Remove b c) :~: Remove b (Remove a c)
-- witRemDist       :: Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
--
-- > Union:
-- witUniIdent      :: Union a 'None :~: a
-- witUniAssoc      :: Union a (Union b c) :~: Union (Union a b) c
--
-- > Elem:
-- witElemCons      :: Elem a (Union b (a ':. c)) :~: 'True
-- witElemRemove    :: a :/~: b -> Elem a c :~: Elem a (Remove b c)
-- witElemUniRemove :: a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (Remove b d))
-- witElemSub       :: a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (b ':. d))
-- witElemUniCons   :: Elem a b :~: 'True -> Elem a (Union b c) :~: 'True
-- witElemRefl      :: Elem a (Union b c) :~: Elem a (Union c b)
--
-- > Subset:
-- witSubElem       :: Subset (a ':. b) c :~: 'True -> Elem a c :~: 'True
-- witSubRem        :: Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True
-- witSubRemove     :: Subset b c :~: 'True -> Subset (Remove a b) c :~: 'True
-- witSubCons       :: Subset b c :~: 'True -> Subset b (a ':. c) :~: 'True
-- witSubRefl       :: Subset a a :~: 'True
-- witSubUni        :: Subset a (Union a b) :~: 'True
-- witSubIn         :: Subset a b :~: 'True -> Elem c a :~: 'True -> Elem c b :~: 'True
-- witSubTrans      :: Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
--
--------------------------------------------------------------------------------

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

witElemRemove :: forall a b c . (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> a :/~: b -> Elem a c :~: Elem a (Remove b c)
witElemRemove _ _ (QualNone) Refl = Refl
witElemRemove a b (QualPred c cs) Refl =
    case test b c of
        Left  Refl -> Refl
        Right Refl -> case test a c of
            Left  Refl -> Refl
            Right Refl | Refl <- witElemRemove a b cs Refl -> Refl
{-# NOINLINE witElemRemove #-}
{-# RULES "witElemRemove" forall a b c . witElemRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniRemove :: forall a b c d . (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> QualRep d -> a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (Remove b d))
witElemUniRemove a b (QualNone) d Refl | Refl <- witElemRemove a b d Refl = Refl
witElemUniRemove a b (QualPred c cs) d Refl =
    case test a c of
        Left  Refl -> Refl
        Right Refl | Refl <- witRemOrd b c d, Refl <- witElemUniRemove a b cs (remove c d) Refl -> Refl
{-# NOINLINE witElemUniRemove #-}
{-# RULES "witElemUniRemove" forall a b c d . witElemUniRemove a b c d Refl = Unsafe.unsafeCoerce Refl #-}

witElemSub :: forall a b c d . (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> QualRep d -> a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (b ':. d))
witElemSub _ _ (QualNone) _ Refl = Refl
witElemSub a b (QualPred c cs) d Refl =
    case test a c of
        Left  Refl -> Refl
        Right Refl -> case test c b of
            Left  Refl | Refl <- witElemUniRemove a b cs d Refl -> Refl
            Right Refl | Refl <- witElemSub a b cs (remove c d) Refl -> Refl
{-# NOINLINE witElemSub #-}
{-# RULES "witElemSub" forall a b c d . witElemSub a b c d Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniCons :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Elem a b :~: 'True -> Elem a (Union b c) :~: 'True
witElemUniCons _ b (QualNone) Refl | Refl <- witUniIdent b = Refl
witElemUniCons a b (QualPred c cs) Refl =
    case test a c of
        Left  Refl | Refl <- witElemCons a b cs -> Refl
        Right Refl | Refl <- witElemUniCons a b cs Refl, Refl <- witElemSub a c b cs Refl -> Refl
{-# NOINLINE witElemUniCons #-}
{-# RULES "witElemUniCons" forall a b c . witElemUniCons a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniRefl :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Elem a (Union b c) :~: Elem a (Union c b)
witElemUniRefl _ (QualNone) c | Refl <- witUniIdent c = Refl
witElemUniRefl a (QualPred b bs) c =
    case test a b of
        Left  Refl | Refl <- witElemCons a c bs -> Refl
        Right Refl | Refl <- witElemUniRefl a bs c, Refl <- witElemSub a b c bs Refl, Refl <- witElemUniRemove a b bs c Refl -> Refl
{-# NOINLINE witElemUniRefl #-}
{-# RULES "witElemUniRefl" forall a b c . witElemUniRefl a b c = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Subset.

witSubElem :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (a ':. b) c :~: 'True -> Elem a c :~: 'True
witSubElem a _ c Refl =
    case testElem a c of
        Left  Refl -> Refl
        Right x    -> case x of {}
{-# NOINLINE witSubElem #-}
{-# RULES "witSubElem" forall a b c . witSubElem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRem :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True
witSubRem a b c Refl | Refl <- witSubElem a b c Refl = Refl
{-# NOINLINE witSubRem #-}
{-# RULES "witSubRem" forall a b c . witSubRem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRemove :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset b c :~: 'True -> Subset (Remove a b) c :~: 'True
witSubRemove _ (QualNone) _ Refl = Refl
witSubRemove a (QualPred b bs) c Refl =
    case test a b of
        Left  Refl | Refl <- witSubRem b bs c Refl -> Refl
        Right Refl | Refl <- witEqRefl a b ->
            case testElem b c of
                Left  Refl | Refl <- witSubRemove a bs c Refl -> Refl
                Right x -> case x of {}
{-# NOINLINE witSubRemove #-}
{-# RULES "witSubRemove" forall a b c . witSubRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubCons :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset b c :~: 'True -> Subset b (a ':. c) :~: 'True
witSubCons _ (QualNone) _ _ = Refl
witSubCons a (QualPred b bs) c Refl =
    case test b a of
        Left  Refl | Refl <- witSubRem  b bs c Refl, Refl <- witSubCons a bs c Refl -> Refl
        Right Refl | Refl <- witSubElem b bs c Refl, Refl <- witSubCons a bs c Refl -> Refl
{-# NOINLINE witSubCons #-}
{-# RULES "witSubCons" forall a b c . witSubCons a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRefl :: forall a . QualRep a -> Subset a a :~: 'True
witSubRefl (QualNone) = Refl
witSubRefl (QualPred a as) | Refl <- witSubRefl as, Refl <- witSubCons a as as Refl = Refl
{-# NOINLINE witSubRefl #-}
{-# RULES "witSubRefl" forall a . witSubRefl a = Unsafe.unsafeCoerce Refl #-}

witSubUni :: forall a b . QualRep a -> QualRep b -> Subset a (Union a b) :~: 'True
witSubUni (QualNone) _ = Refl
witSubUni (QualPred a as) b | Refl <- witSubUni as (remove a b), Refl <- witSubCons a as (union as (remove a b)) Refl = Refl
{-# NOINLINE witSubUni #-}
{-# RULES "witSubUni" forall a b . witSubUni a b = Unsafe.unsafeCoerce Refl #-}

witSubIn :: forall a b c . Typeable c => QualRep a -> QualRep b -> Proxy c -> Subset a b :~: 'True -> Elem c a :~: 'True -> Elem c b :~: 'True
witSubIn (QualPred a as) b c Refl Refl =
    case test c a of
        Left  Refl | Refl <- witSubElem a as b Refl -> Refl
        Right Refl | Refl <- witSubRem a as b Refl, Refl <- witSubIn as b c Refl Refl -> Refl
{-# NOINLINE witSubIn #-}
{-# RULES "witSubIn" forall a b c . witSubIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubTrans :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
witSubTrans (QualNone) _ _ _ _ = Refl
witSubTrans (QualPred a as) b c Refl Refl
    | Refl <- witSubElem a as b Refl
    , Refl <- witSubIn b c a Refl Refl
    , Refl <- witSubTrans as b c Refl Refl
    = Refl
{-# NOINLINE witSubTrans #-}
{-# RULES "witSubTrans" forall a b c . witSubTrans a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Subset & Union (SU).

lemSU1_1 :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Elem a b :~: 'True -> Elem a c :~: 'False -> Subset b c :~: 'False
lemSU1_1 _ (QualNone) _ x _ = case x of {}
lemSU1_1 a (QualPred b bs) c Refl Refl =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case testElem b c of
           Left  Refl | Refl <- lemSU1_1 a bs c Refl Refl -> Refl
           Right Refl -> Refl

lemSU1_2_1 :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Elem a c :~: 'True -> Subset (Remove a b) c :~: Subset b c
lemSU1_2_1 _ (QualNone) _ _ = Refl
lemSU1_2_1 a (QualPred b bs) c Refl =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case testElem b c of
            Left  Refl | Refl <- lemSU1_2_1 a bs c Refl -> Refl
            Right Refl -> Refl

lemSU1_2_2 :: forall a b c d . Typeable a => Proxy a -> QualRep b -> QualRep c -> QualRep d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b c) d
lemSU1_2_2 a (QualNone) c d Refl | Refl <- lemSU1_2_1 a c d Refl = Refl
lemSU1_2_2 a (QualPred b bs) c d Refl =
    case testElem b d of
        Left  Refl | Refl <- witRemOrd b a c, Refl <- lemSU1_2_2 a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl

lemSU1_2_3 :: forall a b c d . Typeable a => Proxy a -> QualRep b -> QualRep c -> QualRep d -> Elem a d :~: 'True -> Subset (Union b (Remove a (Remove a c))) d :~: Subset (Union b c) d
lemSU1_2_3 a b c d Refl | Refl <- lemSU1_2_2 a b c d Refl, Refl <- lemSU1_2_2 a b (remove a c) d Refl = Refl

lemSU1_2_4 :: forall a b c d . Typeable a => Proxy a -> QualRep b -> QualRep c -> QualRep d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b (a ':. c)) d
lemSU1_2_4 a b c d Refl | Refl <- lemSU1_2_3 a b (QualPred a c) d Refl = Refl

lemSU1_2 :: forall a b c d . Typeable a => Proxy a -> QualRep b -> QualRep c -> QualRep d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b (a ':. c)) d
lemSU1_2 a (QualNone) c d Refl | Refl <- lemSU1_2_1 a c d Refl = Refl
lemSU1_2 a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c d Refl =
    case testElem b d of
        Left  Refl -> case test b a of
            Left  Refl | Refl <- lemSU1_2_3 a bs c d Refl -> Refl
            Right Refl | Refl <- witRemOrd b a c, Refl <- lemSU1_2_4 a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl

witSU1 :: forall a b c d . Typeable a => Proxy a -> QualRep b -> QualRep c -> QualRep d -> Subset (Union (a ':. b) c) d :~: Subset (Union b (a ':. c)) d
witSU1 a b c d =
    case testElem a d of
        Left  Refl | Refl <- lemSU1_2 a b c d Refl -> Refl
        Right Refl | Refl <- witElemCons a b c, Refl <- lemSU1_1 a (union b (QualPred a c)) d Refl Refl -> Refl 
--
-- Needed for:
--   matchBeta (b :# p) as = matchBeta b (p :~ as)
-- 
-- Where I know:
--   Subset (Union ps rs) qs ~ True
--   ps ~ (a:as)
--
-- Subset (Union (a:as) rs) qs ~ True
--   > Union 2nd rule.
-- Subset (a : (Union as rs)) qs ~ True
--   > ??? 
-- Subset (Union as (a:rs)) qs ~ True

--------------------------------------------------------------------------------

witSUExt :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Subset b c :~: 'True -> Subset b (Union a c) :~: 'True
witSUExt _ (QualNone) _ _ = Refl
witSUExt a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c Refl
    | Refl <- witSubElem b bs c Refl
    , Refl <- witElemUniCons b c a Refl
    , Refl <- witElemUniRefl b c a
    , Refl <- witSUExt a bs c Refl
    = Refl

witSUExtL :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Subset b (Union a c) :~: 'True -> Subset (Union a b) (Union a c) :~: 'True
witSUExtL a (QualNone) c Refl | Refl <- witUniIdent a, Refl <- witSubUni a c = Refl
witSUExtL a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c Refl
    | Refl :: Subset qs (Union a c) :~: 'True <- witSubRem b bs (union a c) Refl
    , Refl :: Subset (Union a qs) (Union a c) :~: 'True <- witSUExtL a bs c Refl
    , Refl :: Elem q (Union a c) :~: 'True <- witSubElem b bs (union a c) Refl
  --, Refl :: Subset (Union a (q ':. qs)) (Union a c) :~: 'True <- witSU1 b bs a (union a c) Refl Refl
    = undefined
   -- _ :: Subset (Union a (q ':. qs)) (Union a c) :~: 'True

-- witSubRem :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True

witSUCons :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union b c) (Union b (a ':. c)) :~: 'True
witSUCons a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
witSUCons a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
    let x :: QualRep (Union qs (Remove a c)) = union bs (remove a c) in
    let y :: QualRep (Union qs (a ':. (Remove a c))) = union bs (QualPred a (remove a c)) in
    let z :: QualRep (a ':. Union qs c) = QualPred a (union bs c) in
    case test a b of
        Left  Refl -- case a == q
            | Refl :: Subset (Union qs (Remove a c)) (Union qs (a ':. (Remove a c))) :~: 'True <- witSUCons a bs (remove a c)
            , Refl :: Subset (Union qs (a ':. (Remove a c))) (a ':. Union qs c)      :~: 'True <- witCR bs
            , Refl :: Subset (Union qs (Remove a c)) (a ':. Union qs c)              :~: 'True <- witSubTrans x y z Refl Refl
            -> Refl
            -- _ :: Subset (Union qs (Remove a c)) (a ':. Union qs c) :~: 'True
        Right Refl -- case a /= q
            | Refl <- witEqRefl a b
            -> undefined
            -- _ :: Subset (Union qs (Remove q c)) (q ':. Union qs (a ':. Remove q c)) :~: 'True
  where
    witCR :: forall d . QualRep d -> Subset (Union d (a ':. (Remove a c))) (a ':. Union d c) :~: 'True
    witCR d
        | Refl :: Subset (Union d (a ':. (Remove a c))) (a ':. (Union d (Remove a c))) :~: 'True <- undefined
        , Refl :: Subset (a ':. (Union d (Remove a c))) (a ':. (Union d c))            :~: 'True <- undefined
        = let x :: QualRep (Union d (a ':. (Remove a c))) = (union d (QualPred a (remove a c))) in
          let y :: QualRep (a ':. (Union d (Remove a c))) = QualPred a (union d (remove a c)) in
          let z :: QualRep (a ':. (Union d c)) = QualPred a (union d c) in
          case (witSubTrans x y z Refl Refl :: Subset (Union d (a ':. (Remove a c))) (a ':. (Union d c)) :~: 'True) of
            Refl -> Refl

--------------------------------------------------------------------------------

-- witSURemove :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union (Remove a b) c) (Union b (a ':. c)) :~: 'True
-- witSURemove a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSURemove a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
--     let x :: QualRep (Union qs c) = union bs c in
--     let y :: QualRep (Remove q c) = remove b c in
--     let z :: QualRep (Union (Remove a qs) (Remove q c)) = (union (remove a bs) y) in
--     let v :: QualRep (Union qs (a ':. (Remove q c))) = (union bs (QualPred a y)) in
--     case test b a of
--         Left  Refl | Refl <- witSubRefl x, Refl <- witSubCons b x x Refl -> Refl
--         Right Refl | Refl <- witEqRefl b a, Refl <- witSURemove a bs y, Refl <- witSubCons b z v Refl -> Refl

-- witSURemove :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union b (Remove a c)) (Union b c) :~: 'True
-- witSURemove = undefined

-- witSUShift :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union b (a ':. c)) (a ':. (Union b c)) :~: 'True
-- witSUShift a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSUShift a (QualPred b bs) c =
--     case test b a of
--         Left  Refl -> undefined
--         -- _ :: Subset (Union qs c) (a ':. (a ':. Union qs (Remove a c))) :~: 'True
--         Right Refl -> undefined
--         -- _ :: Subset (Union qs (a ':. Remove q c)) (a ':. (q ':. Union qs (Remove q c))) :~: 'True

-- witSubUniCons :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union b c) (Union b (a ':. c)) :~: 'True
-- witSubUniCons a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSubUniCons a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
--     case test a b of
--         Left  Refl | Refl <- (witSubUniCons a bs c   :: Subset (Union qs c) (Union qs (a ':. c)) :~: 'True)
--                    -> undefined -- _ :: Subset (Union qs (Remove a c)) (a ':. Union qs c) :~: 'True
--         Right Refl -> undefined

-- witSubUniRefl :: forall a b . QualRep a -> QualRep b -> Subset (Union a b) (Union b a) :~: 'True
-- witSubUniRefl (QualNone) b | Refl <- witUniIdent b, Refl <- witSubRefl b = Refl
-- witSubUniRefl (QualPred (a :: Proxy q) (as :: QualRep qs)) b
--     | Refl <- witElemCons a b as
--     , Refl <- witSubUniRefl as (remove a b)
--     , Refl <- witSURemove a b as
--     = let x :: QualRep (Union qs (Remove q b)) = union as (remove a b) in
--       let y :: QualRep (Union (Remove q b) qs) = union (remove a b) as in
--       let z :: QualRep (Union b (q ':. qs)) = union b (QualPred a as) in
--       case witSubTrans x y z Refl Refl of
--           Refl -> Refl
-- {-# NOINLINE witSubUniRefl #-}
-- {-# RULES "witSubUniRefl" forall a b . witSubUniRefl a b = Unsafe.unsafeCoerce Refl #-}

-- witSubUniMove :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union (a ':. b) c) (Union b (a ':. c)) :~: 'True
-- witSubUniMove a (QualNone) c
--     | Refl <- witSubRefl c
--     , Refl <- witSubCons a c c Refl
--     , Refl <- witSubRemove a c (QualPred a c) Refl
--     = Refl
-- witSubUniMove a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
--     let x :: QualRep (Union qs (Remove a (Remove q c))) = union bs (remove a (remove b c)) in
--     let y :: QualRep (Union qs (a ':. Remove q c)) = union bs (QualPred a (remove b c)) in
--     case test a b of
--         Left  (Refl :: a :~: q)
--             | Refl <- (witSubUniMove a bs c
--                            :: Subset (Union (a ':. qs) c) (Union qs (a ':. c)) :~: 'True)
--             , Refl <- (witElemCons a bs c
--                            :: Elem a (Union qs (a ':. c)) :~: 'True)
--             , Refl <- (witSubRefl (union bs c)
--                            :: Subset (Union qs c) (Union qs c) :~: 'True)
--             , Refl <- (undefined
--                            :: Subset (Union qs c) (Union qs (a ':. c)) :~: 'True)
--             --, Refl <- (witSURemove a
--             --                :: Subset (Union qs c) (Union qs (a ':. c)) :~: 'True)
--             --
--             -> let Refl :: Subset (a ':. Union qs c) (Union qs (a ':. c)) :~: 'True = Refl in
--                undefined -- goal :: Subset (Union qs (Remove a (Remove a c))) (a ':. Union qs c) :~: 'True
--         Right (Refl :: a :/~: q)
--             | Refl <- (witEqRefl a b)
--             , Refl <- (witElemCons a bs (remove b c)   :: Elem a (Union qs (a ':. (Remove q c))) :~: 'True)
--             , Refl <- (witSubUniMove a bs (remove b c) :: Subset (Union qs (Remove a (Remove q c))) (Union qs (a ':. Remove q c)) :~: 'True)
--             , Refl <- (witRemOrd a b c                 :: Remove a (Remove q c) :~: Remove q (Remove a c))
--             , Refl <- (witSubCons b x y Refl           :: Subset (Union qs (Remove a (Remove q c))) (q ':. Union qs (a ':. Remove q c)) :~: 'True)
--             -> Refl
            
-- witSURemove' :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union b (Remove a c)) (Union b (a ':. c)) :~: 'True
-- witSURemove' a b c
--   | Refl <- (witSURemove a c b        :: Subset (Union (Remove a c) b) (Union c (a ':. b)) :~: 'True)
--   , Refl <- (witSubUniRefl b (remove a c) :: Subset (Union b (Remove a c)) (Union (Remove a c) b) :~: 'True)
--   , Refl <- (witSubTrans (union b (remove a c)) (union (remove a c) b) (union c (QualPred a b)) Refl Refl
--                                           :: Subset (Union b (Remove a c)) (Union c (a ':. b)) :~: 'True)
--   = undefined

-- witSubUniCons :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (a ':. (Union b c)) (Union b (a ':. c)) :~: 'True
-- witSubUniCons a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSubUniCons a (QualPred b _) _ =
--     case test a b of
--         Left  Refl -> undefined -- ::  Subset (Union qs (Remove a c)) (a ':. Union qs c) :~: 'True
--         Right Refl -> undefined

-- witSubUniMove' :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Subset (Union (a ':. b) c) (Union b (a ':. c)) :~: 'True
-- witSubUniMove' a b c
--   | Refl <- witElemCons a b c
--   , Refl <- witSubRefl (union b c)
--   , Refl <- witSubCons a (union b c) (union b c) Refl
--   , Refl <- witSubUniCons a b c
--   , Refl <- witSURemove' a b c
--   = Refl

--------------------------------------------------------------------------------
-- Fin.
