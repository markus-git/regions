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
-- witElemUniCons   :: a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (b ':. d))
-- witElemUni       :: Elem a b :~: 'True -> Elem a (Union b c) :~: 'True
-- witElemUniRefl   :: Elem a (Union b c) :~: Elem a (Union c b)
--
-- > Subset:
-- witSubElem       :: Subset (a ':. b) c :~: 'True -> Elem a c :~: 'True
-- witSubRem        :: Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True
-- witSubRemove     :: Elem a c :~: 'True -> Subset (Remove a b) c :~: Subset b c
-- witSubIn         :: Subset a b :~: 'True -> Elem c a :~: 'True -> Elem c b :~: 'True
-- witSubNotIn      :: Elem a b :~: 'True -> Elem a c :~: 'False -> Subset b c :~: 'False
-- witSubCons       :: Subset b c :~: 'True -> Subset b (a ':. c) :~: 'True
-- witSubRefl       :: Subset a a :~: 'True
-- witSubUni        :: Subset a (Union a b) :~: 'True
-- witSubTrans      :: Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
--
-- > Subset & Union (SU):
-- witSURemove :: Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b c) d
-- witSUCons   :: Elem a d :~: 'True -> Subset (Union b c) d :~: Subset (Union b (a ':. c)) d
-- witSURefl   :: Subset (Union a b) c :~: Subset (Union b a) c
-- witSURefl'  :: Subset a (Union b c) :~: Subset a (Union c b)
--
--------------------------------------------------------------------------------

type T = Typeable
type P = Proxy
type Q = QualRep

witEqRefl :: (T a, T b) => P a -> P b -> (a == b) :~: (b == a)
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

witInsIdem :: T a => P a -> Q b -> Insert a (Insert a b) :~: Insert a b
witInsIdem _ (QualNone) = Refl
witInsIdem a (QualPred b bs) | Refl <- witInsIdem a bs =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> Refl
{-# NOINLINE witInsIdem #-}
{-# RULES "witInsIdem" forall a b . witInsIdem a b = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Remove.

witRemOrd :: (T a, T b) => P a -> P b -> Q c -> Remove a (Remove b c) :~: Remove b (Remove a c)
witRemOrd _ _ (QualNone) = Refl
witRemOrd a b (QualPred c cs) | Refl <- witRemOrd a b cs =
    case (test a c, test b c) of
        (Left  Refl, Left  Refl) -> Refl
        (Left  Refl, Right Refl) -> Refl
        (Right Refl, Left  Refl) -> Refl
        (Right Refl, Right Refl) -> Refl
{-# NOINLINE witRemOrd #-}
{-# RULES "witRemOrd" forall a b c . witRemOrd a b c = Unsafe.unsafeCoerce Refl #-}

witRemDist :: forall a b c . T a => P a -> Q b -> Q c -> Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
witRemDist _ (QualNone) _ = Refl
witRemDist a (QualPred (b :: P q) (bs :: Q qs)) c =
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

witUniIdent :: Q a -> Union a 'None :~: a
witUniIdent (QualNone) = Refl
witUniIdent (QualPred _ as) | Refl <- witUniIdent as = Refl
{-# NOINLINE witUniIdent #-}
{-# RULES "witUniIdent" forall a . witUniIdent a = Unsafe.unsafeCoerce Refl #-}

witUniAssoc :: forall a b c . Q a -> Q b -> Q c -> Union a (Union b c) :~: Union (Union a b) c
witUniAssoc (QualNone) _ _ = Refl
witUniAssoc (QualPred (a :: P q) (as :: Q qs)) b c =
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

witElemCons :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Union b (a ':. c)) :~: 'True
witElemCons _ (QualNone) _ = Refl
witElemCons a (QualPred b bs) c =
    case test a b of
        Left  Refl -> Refl
        Right Refl | Refl <- witEqRefl a b, Refl <- witElemCons a bs (remove b c) -> Refl
{-# NOINLINE witElemCons #-}
{-# RULES "witElemCons" forall a b c . witElemCons a b c = Unsafe.unsafeCoerce Refl #-}

witElemRemove :: forall a b c . (T a, T b) => P a -> P b -> Q c -> a :/~: b -> Elem a c :~: Elem a (Remove b c)
witElemRemove _ _ (QualNone) Refl = Refl
witElemRemove a b (QualPred c cs) Refl =
    case test b c of
        Left  Refl -> Refl
        Right Refl -> case test a c of
            Left  Refl -> Refl
            Right Refl | Refl <- witElemRemove a b cs Refl -> Refl
{-# NOINLINE witElemRemove #-}
{-# RULES "witElemRemove" forall a b c . witElemRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniRemove :: forall a b c d . (T a, T b) => P a -> P b -> Q c -> Q d -> a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (Remove b d))
witElemUniRemove a b (QualNone) d Refl | Refl <- witElemRemove a b d Refl = Refl
witElemUniRemove a b (QualPred c cs) d Refl =
    case test a c of
        Left  Refl -> Refl
        Right Refl | Refl <- witRemOrd b c d, Refl <- witElemUniRemove a b cs (remove c d) Refl -> Refl
{-# NOINLINE witElemUniRemove #-}
{-# RULES "witElemUniRemove" forall a b c d . witElemUniRemove a b c d Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniCons :: forall a b c d . (T a, T b) => P a -> P b -> Q c -> Q d -> a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (b ':. d))
witElemUniCons _ _ (QualNone) _ Refl = Refl
witElemUniCons a b (QualPred c cs) d Refl =
    case test a c of
        Left  Refl -> Refl
        Right Refl -> case test c b of
            Left  Refl | Refl <- witElemUniRemove a b cs d Refl -> Refl
            Right Refl | Refl <- witElemUniCons a b cs (remove c d) Refl -> Refl
{-# NOINLINE witElemUniCons #-}
{-# RULES "witElemUniCons" forall a b c d . witElemUniCons a b c d Refl = Unsafe.unsafeCoerce Refl #-}

witElemUni :: forall a b c . T a => P a -> Q b -> Q c -> Elem a b :~: 'True -> Elem a (Union b c) :~: 'True
witElemUni _ b (QualNone) Refl | Refl <- witUniIdent b = Refl
witElemUni a b (QualPred c cs) Refl =
    case test a c of
        Left  Refl | Refl <- witElemCons a b cs -> Refl
        Right Refl | Refl <- witElemUni a b cs Refl, Refl <- witElemUniCons a c b cs Refl -> Refl
{-# NOINLINE witElemUni #-}
{-# RULES "witElemUni" forall a b c . witElemUni a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniRefl :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Union b c) :~: Elem a (Union c b)
witElemUniRefl _ (QualNone) c | Refl <- witUniIdent c = Refl
witElemUniRefl a (QualPred b bs) c =
    case test a b of
        Left  Refl | Refl <- witElemCons a c bs -> Refl
        Right Refl | Refl <- witElemUniRefl a bs c, Refl <- witElemUniCons a b c bs Refl, Refl <- witElemUniRemove a b bs c Refl -> Refl
{-# NOINLINE witElemUniRefl #-}
{-# RULES "witElemUniRefl" forall a b c . witElemUniRefl a b c = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Subset.

witSubElem :: forall a b c . T a => P a -> Q b -> Q c -> Subset (a ':. b) c :~: 'True -> Elem a c :~: 'True
witSubElem a _ c Refl =
    case testElem a c of
        Left  Refl -> Refl
        Right x    -> case x of {}
{-# NOINLINE witSubElem #-}
{-# RULES "witSubElem" forall a b c . witSubElem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRem :: forall a b c . T a => P a -> Q b -> Q c -> Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True
witSubRem a b c Refl | Refl <- witSubElem a b c Refl = Refl
{-# NOINLINE witSubRem #-}
{-# RULES "witSubRem" forall a b c . witSubRem a b c Refl = Unsafe.unsafeCoerce Refl #-}

-- witSubRemove :: forall a b c . T a => P a -> Q b -> Q c -> Subset b c :~: 'True -> Subset (Remove a b) c :~: 'True
-- witSubRemove _ (QualNone) _ Refl = Refl
-- witSubRemove a (QualPred b bs) c Refl =
--     case test a b of
--         Left  Refl | Refl <- witSubRem b bs c Refl -> Refl
--         Right Refl | Refl <- witEqRefl a b ->
--             case testElem b c of
--                 Left  Refl | Refl <- witSubRemove a bs c Refl -> Refl
--                 Right x -> case x of {}

witSubRemove :: forall a b c . T a => P a -> Q b -> Q c -> Elem a c :~: 'True -> Subset (Remove a b) c :~: Subset b c
witSubRemove _ (QualNone) _ _ = Refl
witSubRemove a (QualPred b bs) c Refl =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case testElem b c of
            Left  Refl | Refl <- witSubRemove a bs c Refl -> Refl
            Right Refl -> Refl
{-# NOINLINE witSubRemove #-}
{-# RULES "witSubRemove" forall a b c . witSubRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubIn :: forall a b c . T c => Q a -> Q b -> P c -> Subset a b :~: 'True -> Elem c a :~: 'True -> Elem c b :~: 'True
witSubIn (QualPred a as) b c Refl Refl =
    case test c a of
        Left  Refl | Refl <- witSubElem a as b Refl -> Refl
        Right Refl | Refl <- witSubRem a as b Refl, Refl <- witSubIn as b c Refl Refl -> Refl
{-# NOINLINE witSubIn #-}
{-# RULES "witSubIn" forall a b c . witSubIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubNotIn :: forall a b c . T a => P a -> Q b -> Q c -> Elem a b :~: 'True -> Elem a c :~: 'False -> Subset b c :~: 'False
witSubNotIn _ (QualNone) _ x _ = case x of {}
witSubNotIn a (QualPred b bs) c Refl Refl =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case testElem b c of
           Left  Refl | Refl <- witSubNotIn a bs c Refl Refl -> Refl
           Right Refl -> Refl
{-# NOINLINE witSubNotIn #-}
{-# RULES "witSubNotIn" forall a b c . witSubNotIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubCons :: forall a b c . T a => P a -> Q b -> Q c -> Subset b c :~: 'True -> Subset b (a ':. c) :~: 'True
witSubCons _ (QualNone) _ _ = Refl
witSubCons a (QualPred b bs) c Refl =
    case test b a of
        Left  Refl | Refl <- witSubRem  b bs c Refl, Refl <- witSubCons a bs c Refl -> Refl
        Right Refl | Refl <- witSubElem b bs c Refl, Refl <- witSubCons a bs c Refl -> Refl
{-# NOINLINE witSubCons #-}
{-# RULES "witSubCons" forall a b c . witSubCons a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRefl :: forall a . Q a -> Subset a a :~: 'True
witSubRefl (QualNone) = Refl
witSubRefl (QualPred a as) | Refl <- witSubRefl as, Refl <- witSubCons a as as Refl = Refl
{-# NOINLINE witSubRefl #-}
{-# RULES "witSubRefl" forall a . witSubRefl a = Unsafe.unsafeCoerce Refl #-}

witSubUni :: forall a b . Q a -> Q b -> Subset a (Union a b) :~: 'True
witSubUni (QualNone) _ = Refl
witSubUni (QualPred a as) b | Refl <- witSubUni as (remove a b), Refl <- witSubCons a as (union as (remove a b)) Refl = Refl
{-# NOINLINE witSubUni #-}
{-# RULES "witSubUni" forall a b . witSubUni a b = Unsafe.unsafeCoerce Refl #-}

-- witSubU :: forall a b c . Q a -> Q b -> Q c -> Subset a b :~: 'True -> Subset a (Union b c) :~: 'True
-- witSubU (QualNone) _ _ _ = Refl
-- witSubU (QualPred (a::P q) (as::Q qs)) b c Refl
--   | Refl :: Elem q b <- witSubIn = _

witSubTrans :: forall a b c . Q a -> Q b -> Q c -> Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
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

witSURemove :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b c) d
witSURemove a (QualNone) c d Refl | Refl <- witSubRemove a c d Refl = Refl
witSURemove a (QualPred b bs) c d Refl =
    case testElem b d of
        Left  Refl | Refl <- witRemOrd b a c, Refl <- witSURemove a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl

witSUCons :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b c) d :~: Subset (Union b (a ':. c)) d
witSUCons _ (QualNone) _ _ Refl = Refl
witSUCons a (QualPred b bs) c d Refl =
    case testElem b d of
        Left  Refl -> case test b a of
            Left  Refl | Refl <- witSURemove a bs c d Refl -> Refl
            Right Refl | Refl <- witSUCons a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl
    
witSURefl :: forall a b c . Q a -> Q b -> Q c -> Subset (Union a b) c :~: Subset (Union b a) c
witSURefl (QualNone) b _ | Refl <- witUniIdent b = Refl
witSURefl (QualPred a as) b c =
    case testElem a c of
        Left  Refl | Refl <- witSURemove a as b c Refl, Refl <- witSURefl as b c, Refl <- witSUCons a b as c Refl -> Refl
        Right Refl | Refl <- witElemCons a b as, Refl <- witSubNotIn a (union b (QualPred a as)) c Refl Refl -> Refl

witSURefl' :: forall a b c . Q a -> Q b -> Q c -> Subset a (Union b c) :~: Subset a (Union c b)
witSURefl' (QualNone) _ _ = Refl
witSURefl' (QualPred a as) b c | Refl <- witElemUniRefl a b c, Refl <- witSURefl' as b c = Refl

--------------------------------------------------------------------------------

lemSU1 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a (Remove a c))) d :~: Subset (Union b c) d
lemSU1 a b c d Refl | Refl <- witSURemove a b c d Refl, Refl <- witSURemove a b (remove a c) d Refl = Refl

lemSU2 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b (a ':. c)) d
lemSU2 a b c d Refl | Refl <- lemSU1 a b (QualPred a c) d Refl = Refl

lemSU3 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b (a ':. c)) d
lemSU3 a (QualNone) c d Refl | Refl <- witSubRemove a c d Refl = Refl
lemSU3 a (QualPred (b :: P q) (bs :: Q qs)) c d Refl =
    case testElem b d of
        Left  Refl -> case test b a of
            Left  Refl | Refl <- lemSU1 a bs c d Refl -> Refl
            Right Refl | Refl <- witRemOrd b a c, Refl <- lemSU2 a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl

witSU1 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Subset (Union (a ':. b) c) d :~: Subset (Union b (a ':. c)) d
witSU1 a b c d =
    case testElem a d of
        Left  Refl | Refl <- lemSU3 a b c d Refl -> Refl
        Right Refl | Refl <- witElemCons a b c, Refl <- witSubNotIn a (union b (QualPred a c)) d Refl Refl -> Refl 

lemSU4 :: forall a b c d . (T a, T b) => P a -> P b -> Q c -> Q d -> a :/~: b -> Elem a (Union c (Remove b d)) :~: Elem a (Union c (b ':. d))
lemSU4 a b c d Refl | Refl <- witElemUniRemove a b c d Refl, Refl <- witElemUniCons a b c d Refl = Refl

witSU1' :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Subset b (Union (a ':. c) d) :~: Subset b (Union c (a ':. d))
witSU1' _ (QualNone) _ _ = Refl
witSU1' a (QualPred b bs) c d =
    case test b a of
        Left  Refl | Refl <- witElemCons a c d, Refl <- witSU1' a bs c d -> Refl
        Right Refl | Refl <- lemSU4 b a c d Refl -> case testElem b (union c (remove a d)) of
            Left  Refl | Refl <- witSU1' a bs c d -> Refl
            Right Refl -> Refl

--------------------------------------------------------------------------------

witSU2 :: forall a b . Q a -> Q b -> Subset (Difference (Union a b) b) a :~: 'True
witSU2 = undefined

--------------------------------------------------------------------------------

-- witSUExt :: forall a b c . Q a -> Q b -> Q c -> Subset b c :~: 'True -> Subset b (Union a c) :~: 'True
-- witSUExt _ (QualNone) _ _ = Refl
-- witSUExt a (QualPred (b :: P q) (bs :: Q qs)) c Refl
--     | Refl <- witSubElem b bs c Refl
--     , Refl <- witElemUni b c a Refl
--     , Refl <- witElemUniRefl b c a
--     , Refl <- witSUExt a bs c Refl
--     = Refl

-- witSUExtL :: forall a b c . Q a -> Q b -> Q c -> Subset b (Union a c) :~: 'True -> Subset (Union a b) (Union a c) :~: 'True
-- witSUExtL a (QualNone) c Refl | Refl <- witUniIdent a, Refl <- witSubUni a c = Refl
-- witSUExtL a (QualPred (b :: P q) (bs :: Q qs)) c Refl
--     | Refl :: Subset qs (Union a c) :~: 'True <- witSubRem b bs (union a c) Refl
--     , Refl :: Subset (Union a qs) (Union a c) :~: 'True <- witSUExtL a bs c Refl
--     , Refl :: Elem q (Union a c) :~: 'True <- witSubElem b bs (union a c) Refl
--   --, Refl :: Subset (Union a (q ':. qs)) (Union a c) :~: 'True <- witSU1 b bs a (union a c) Refl Refl
--     = undefined
--    -- _ :: Subset (Union a (q ':. qs)) (Union a c) :~: 'True

-- witSubRem :: forall a b c . T a => P a -> Q b -> Q c -> Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True

-- witSUCons :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union b c) (Union b (a ':. c)) :~: 'True
-- witSUCons a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSUCons a (QualPred (b :: P q) (bs :: Q qs)) c =
--     let x :: Q (Union qs (Remove a c)) = union bs (remove a c) in
--     let y :: Q (Union qs (a ':. (Remove a c))) = union bs (QualPred a (remove a c)) in
--     let z :: Q (a ':. Union qs c) = QualPred a (union bs c) in
--     case test a b of
--         Left  Refl -- case a == q
--             | Refl :: Subset (Union qs (Remove a c)) (Union qs (a ':. (Remove a c))) :~: 'True <- witSUCons a bs (remove a c)
--             , Refl :: Subset (Union qs (a ':. (Remove a c))) (a ':. Union qs c)      :~: 'True <- witCR bs
--             , Refl :: Subset (Union qs (Remove a c)) (a ':. Union qs c)              :~: 'True <- witSubTrans x y z Refl Refl
--             -> Refl
--             -- _ :: Subset (Union qs (Remove a c)) (a ':. Union qs c) :~: 'True
--         Right Refl -- case a /= q
--             | Refl <- witEqRefl a b
--             -> undefined
--             -- _ :: Subset (Union qs (Remove q c)) (q ':. Union qs (a ':. Remove q c)) :~: 'True
--   where
--     witCR :: forall d . Q d -> Subset (Union d (a ':. (Remove a c))) (a ':. Union d c) :~: 'True
--     witCR d
--         | Refl :: Subset (Union d (a ':. (Remove a c))) (a ':. (Union d (Remove a c))) :~: 'True <- undefined
--         , Refl :: Subset (a ':. (Union d (Remove a c))) (a ':. (Union d c))            :~: 'True <- undefined
--         = let x :: Q (Union d (a ':. (Remove a c))) = (union d (QualPred a (remove a c))) in
--           let y :: Q (a ':. (Union d (Remove a c))) = QualPred a (union d (remove a c)) in
--           let z :: Q (a ':. (Union d c)) = QualPred a (union d c) in
--           case (witSubTrans x y z Refl Refl :: Subset (Union d (a ':. (Remove a c))) (a ':. (Union d c)) :~: 'True) of
--             Refl -> Refl

--------------------------------------------------------------------------------

-- witSURemove :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union (Remove a b) c) (Union b (a ':. c)) :~: 'True
-- witSURemove a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSURemove a (QualPred (b :: P q) (bs :: Q qs)) c =
--     let x :: Q (Union qs c) = union bs c in
--     let y :: Q (Remove q c) = remove b c in
--     let z :: Q (Union (Remove a qs) (Remove q c)) = (union (remove a bs) y) in
--     let v :: Q (Union qs (a ':. (Remove q c))) = (union bs (QualPred a y)) in
--     case test b a of
--         Left  Refl | Refl <- witSubRefl x, Refl <- witSubCons b x x Refl -> Refl
--         Right Refl | Refl <- witEqRefl b a, Refl <- witSURemove a bs y, Refl <- witSubCons b z v Refl -> Refl

-- witSURemove :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union b (Remove a c)) (Union b c) :~: 'True
-- witSURemove = undefined

-- witSUShift :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union b (a ':. c)) (a ':. (Union b c)) :~: 'True
-- witSUShift a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSUShift a (QualPred b bs) c =
--     case test b a of
--         Left  Refl -> undefined
--         -- _ :: Subset (Union qs c) (a ':. (a ':. Union qs (Remove a c))) :~: 'True
--         Right Refl -> undefined
--         -- _ :: Subset (Union qs (a ':. Remove q c)) (a ':. (q ':. Union qs (Remove q c))) :~: 'True

-- witSubUniCons :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union b c) (Union b (a ':. c)) :~: 'True
-- witSubUniCons a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSubUniCons a (QualPred (b :: P q) (bs :: Q qs)) c =
--     case test a b of
--         Left  Refl | Refl <- (witSubUniCons a bs c   :: Subset (Union qs c) (Union qs (a ':. c)) :~: 'True)
--                    -> undefined -- _ :: Subset (Union qs (Remove a c)) (a ':. Union qs c) :~: 'True
--         Right Refl -> undefined

-- witSubUniRefl :: forall a b . Q a -> Q b -> Subset (Union a b) (Union b a) :~: 'True
-- witSubUniRefl (QualNone) b | Refl <- witUniIdent b, Refl <- witSubRefl b = Refl
-- witSubUniRefl (QualPred (a :: P q) (as :: Q qs)) b
--     | Refl <- witElemCons a b as
--     , Refl <- witSubUniRefl as (remove a b)
--     , Refl <- witSURemove a b as
--     = let x :: Q (Union qs (Remove q b)) = union as (remove a b) in
--       let y :: Q (Union (Remove q b) qs) = union (remove a b) as in
--       let z :: Q (Union b (q ':. qs)) = union b (QualPred a as) in
--       case witSubTrans x y z Refl Refl of
--           Refl -> Refl
-- {-# NOINLINE witSubUniRefl #-}
-- {-# RULES "witSubUniRefl" forall a b . witSubUniRefl a b = Unsafe.unsafeCoerce Refl #-}

-- witSubUniMove :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union (a ':. b) c) (Union b (a ':. c)) :~: 'True
-- witSubUniMove a (QualNone) c
--     | Refl <- witSubRefl c
--     , Refl <- witSubCons a c c Refl
--     , Refl <- witSubRemove a c (QualPred a c) Refl
--     = Refl
-- witSubUniMove a (QualPred (b :: P q) (bs :: Q qs)) c =
--     let x :: Q (Union qs (Remove a (Remove q c))) = union bs (remove a (remove b c)) in
--     let y :: Q (Union qs (a ':. Remove q c)) = union bs (QualPred a (remove b c)) in
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
            
-- witSURemove' :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union b (Remove a c)) (Union b (a ':. c)) :~: 'True
-- witSURemove' a b c
--   | Refl <- (witSURemove a c b        :: Subset (Union (Remove a c) b) (Union c (a ':. b)) :~: 'True)
--   , Refl <- (witSubUniRefl b (remove a c) :: Subset (Union b (Remove a c)) (Union (Remove a c) b) :~: 'True)
--   , Refl <- (witSubTrans (union b (remove a c)) (union (remove a c) b) (union c (QualPred a b)) Refl Refl
--                                           :: Subset (Union b (Remove a c)) (Union c (a ':. b)) :~: 'True)
--   = undefined

-- witSubUniCons :: forall a b c . T a => P a -> Q b -> Q c -> Subset (a ':. (Union b c)) (Union b (a ':. c)) :~: 'True
-- witSubUniCons a (QualNone) c | Refl <- witSubRefl c, Refl <- witSubCons a c c Refl = Refl
-- witSubUniCons a (QualPred b _) _ =
--     case test a b of
--         Left  Refl -> undefined -- ::  Subset (Union qs (Remove a c)) (a ':. Union qs c) :~: 'True
--         Right Refl -> undefined

-- witSubUniMove' :: forall a b c . T a => P a -> Q b -> Q c -> Subset (Union (a ':. b) c) (Union b (a ':. c)) :~: 'True
-- witSubUniMove' a b c
--   | Refl <- witElemCons a b c
--   , Refl <- witSubRefl (union b c)
--   , Refl <- witSubCons a (union b c) (union b c) Refl
--   , Refl <- witSubUniCons a b c
--   , Refl <- witSURemove' a b c
--   = Refl

--------------------------------------------------------------------------------
-- Fin.
