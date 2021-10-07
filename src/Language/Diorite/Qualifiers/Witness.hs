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
-- witEqSym         :: (a == b) :~: (b == a)
-- witEqIf          :: If (a == b) c c :~: c
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
-- > Union & Remove:
-- witUniRemDist    :: Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
--
-- > Elem & Insert:
-- witElemIns       :: Elem a (Insert a b) :~: 'True
-- > Elem & Remove:
-- witElemId        :: Elem a b :~: 'False -> Remove a b :~: b
-- witElemAdd       :: Elem a (Remove b c) :~: 'True -> Elem a c :~: 'True
-- witElemRemove    :: a :/~: b -> Elem a c :~: Elem a (Remove b c)
-- witElemShrink    :: Elem a c :~: 'False -> Elem a (Remove b c) :~: 'False
-- > Elem & Union:
-- witElemCons      :: Elem a (Union b (a ':. c)) :~: 'True
-- witElemUniRemove :: a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (Remove b d))
-- witElemUniCons   :: a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (b ':. d))
-- witElemUni       :: Elem a b :~: 'True -> Elem a (Union b c) :~: 'True
-- witElemUniRefl   :: Elem a (Union b c) :~: Elem a (Union c b)
--
-- > Subset:
-- witSubElem       :: Subset (a ':. b) c :~: 'True -> Elem a c :~: 'True
-- witSubRem        :: Subset (a ':. b) c :~: 'True -> Subset b c :~: 'True
-- witSubAdd        :: Subset b (Remove a c) :~: 'True -> Subset b c :~: 'True
-- witSubRemove     :: Elem a c :~: 'True -> Subset (Remove a b) c :~: Subset b c
-- witSubRemove'    :: Elem a b :~: 'False -> Subset b (Remove a c) :~: Subset b c
-- witSubShrink     :: Elem a (Remove a b) :~: 'False -> Elem a c :~: 'True -> Subset (Remove a b) (Remove a c) :~: Subset b c
-- witSubIn         :: Subset b c :~: 'True -> Elem a b :~: 'True -> Elem a c :~: 'True
-- witSubNotIn      :: Elem a b :~: 'True -> Elem a c :~: 'False -> Subset b c :~: 'False
-- witSubCons       :: Subset b c :~: 'True -> Subset b (a ':. c) :~: 'True
-- witSubRefl       :: Subset a a :~: 'True
-- witSubUni        :: Subset a (Union a b) :~: 'True
-- witSubTrans      :: Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
--
-- > Extends:
-- witExtRefl       :: Extends a a :~: 'True
-- witExtNotIn      :: Elem a b :~: 'True -> Elem a c :~: 'False -> Extends b c :~: 'False
-- witExtSub        :: Extends a b :~: 'True -> Subset a b :~: 'True
-- witExtElem       :: Extends (a ':. b) c :~: 'True -> Elem a c :~: 'True
-- witExtIn         :: Extends b c :~: 'True -> Elem a b :~: 'True -> Elem a c :~: 'True
-- witExtAdd        :: Extends b (Remove a c) :~: 'True -> Extends b c :~: 'True
-- witExtRem        :: Extends (a ':. b) c :~: 'True -> Extends b c :~: 'True
-- witExtCons       :: Extends b c :~: 'True -> Extends b (a ':. c) :~: 'True
-- witExtShrink     :: Elem a c :~: 'True -> Extends (Remove a b) (Remove a c) :~: Extends b c
-- witExtRemove     :: Extends b c :~: 'True -> Extends (Remove a b) c :~: 'True
-- witExtTrans      :: Extends a b :~: 'True -> Extends b c :~: 'True -> Extends a c :~: 'True
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

absurd :: 'True :~: 'False -> a
absurd x = case x of {}

--------------------------------------------------------------------------------

witEqSym :: forall a b . (T a, T b) => P a -> P b -> (a == b) :~: (b == a)
witEqSym a b =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl -> case testEq b a of
            Left  x    -> case x of {}
            Right Refl -> Refl
{-# NOINLINE witEqSym #-}
{-# RULES "witEqSym" forall a b . witEqSym a b = Unsafe.unsafeCoerce Refl #-}

witEqIf :: forall a b c . (T a, T b) => P a -> P b -> If (a == b) c c :~: c
witEqIf a b =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl -> Refl

--------------------------------------------------------------------------------
-- Insert.

witInsIdem :: T a => P a -> Q b -> Insert a (Insert a b) :~: Insert a b
witInsIdem _ (QualNone) = Refl
witInsIdem a (QualPred b bs) | Refl <- witInsIdem a bs =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl -> Refl
{-# NOINLINE witInsIdem #-}
{-# RULES "witInsIdem" forall a b . witInsIdem a b = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Remove.

witRemOrd :: (T a, T b) => P a -> P b -> Q c -> Remove a (Remove b c) :~: Remove b (Remove a c)
witRemOrd _ _ (QualNone) = Refl
witRemOrd a b (QualPred c cs) | Refl <- witRemOrd a b cs =
    case (testEq a c, testEq b c) of
        (Left  Refl, Left  Refl) -> Refl
        (Left  Refl, Right Refl) -> Refl
        (Right Refl, Left  Refl) -> Refl
        (Right Refl, Right Refl) -> Refl
{-# NOINLINE witRemOrd #-}
{-# RULES "witRemOrd" forall a b c . witRemOrd a b c = Unsafe.unsafeCoerce Refl #-}

witRemDist :: forall a b c . T a => P a -> Q b -> Q c -> Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
witRemDist _ (QualNone) _ = Refl
witRemDist a (QualPred (b :: P q) (bs :: Q qs)) c =
    case testEq a b of
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

witUniRemDist :: forall a b c . T a => P a -> Q b -> Q c -> Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
witUniRemDist _ (QualNone) _ = Refl
witUniRemDist a (QualPred b bs) c =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl
            | Refl <- witUniRemDist a bs (remove b c)
            , Refl <- witRemOrd a b c
            -> Refl
{-# NOINLINE witUniRemDist #-}
{-# RULES "witUniRemDist" forall a b c . witUniRemDist a b c = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Elem.

witElemIns :: forall a b . T a => P a -> Q b -> Elem a (Insert a b) :~: 'True
witElemIns _ (QualNone) = Refl
witElemIns a (QualPred b bs) =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl | Refl <- witElemIns a bs -> Refl
{-# NOINLINE witElemIns #-}
{-# RULES "witElemIns" forall a b . witElemIns a b = Unsafe.unsafeCoerce Refl #-}

witElemId :: forall a b . T a => P a -> Q b -> Elem a b :~: 'False -> Remove a b :~: b
witElemId _ (QualNone) _ = Refl
witElemId a (QualPred b bs) Refl =
    case testEq a b of
        Left  x -> case x of {}
        Right Refl | Refl <- witElemId a bs Refl -> Refl

witElemAdd :: forall a b c . (T a, T b) => P a -> P b -> Q c -> Elem a (Remove b c) :~: 'True -> Elem a c :~: 'True
witElemAdd _ _ (QualNone) x = case x of {}
witElemAdd a b (QualPred c cs) Refl =
    case testEq a c of
        Left  Refl -> Refl
        Right Refl -> case testEq b c of
            Left  Refl -> Refl
            Right Refl | Refl <- witElemAdd a b cs Refl -> Refl
{-# NOINLINE witElemAdd #-}
{-# RULES "witElemAdd" forall a b c . witElemAdd a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemRemove :: forall a b c . (T a, T b) => P a -> P b -> Q c -> a :/~: b -> Elem a c :~: Elem a (Remove b c)
witElemRemove _ _ (QualNone) Refl = Refl
witElemRemove a b (QualPred c cs) Refl =
    case testEq b c of
        Left  Refl -> Refl
        Right Refl -> case testEq a c of
            Left  Refl -> Refl
            Right Refl | Refl <- witElemRemove a b cs Refl -> Refl
{-# NOINLINE witElemRemove #-}
{-# RULES "witElemRemove" forall a b c . witElemRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemShrink :: forall a b c . (T a, T b) => P a -> P b -> Q c -> Elem a c :~: 'False -> Elem a (Remove b c) :~: 'False
witElemShrink _ _ (QualNone) _ = Refl
witElemShrink a b (QualPred c cs) Refl =
    case testEq a b of
        Left  Refl -> case testEq a c of
            Left  x -> case x of {}
            Right Refl | Refl <- witElemShrink a a cs Refl -> Refl
        Right Refl | Refl <- witElemRemove a b (QualPred c cs) Refl -> Refl
{-# NOINLINE witElemShrink #-}
{-# RULES "witElemShrink" forall a b c . witElemShrink a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemCons :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Union b (a ':. c)) :~: 'True
witElemCons _ (QualNone) _ = Refl
witElemCons a (QualPred b bs) c =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl
            | Refl <- witEqSym a b
            , Refl <- witElemCons a bs (remove b c)
            -> Refl
{-# NOINLINE witElemCons #-}
{-# RULES "witElemCons" forall a b c . witElemCons a b c = Unsafe.unsafeCoerce Refl #-}

witElemUniRemove :: forall a b c d . (T a, T b) => P a -> P b -> Q c -> Q d -> a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (Remove b d))
witElemUniRemove a b (QualNone) d Refl | Refl <- witElemRemove a b d Refl = Refl
witElemUniRemove a b (QualPred c cs) d Refl =
    case testEq a c of
        Left  Refl -> Refl
        Right Refl
            | Refl <- witRemOrd b c d
            , Refl <- witElemUniRemove a b cs (remove c d) Refl
            -> Refl
{-# NOINLINE witElemUniRemove #-}
{-# RULES "witElemUniRemove" forall a b c d . witElemUniRemove a b c d Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniCons :: forall a b c d . (T a, T b) => P a -> P b -> Q c -> Q d -> a :/~: b -> Elem a (Union c d) :~: Elem a (Union c (b ':. d))
witElemUniCons _ _ (QualNone) _ Refl = Refl
witElemUniCons a b (QualPred c cs) d Refl =
    case testEq a c of
        Left  Refl -> Refl
        Right Refl -> case testEq c b of
            Left  Refl | Refl <- witElemUniRemove a b cs d Refl -> Refl
            Right Refl | Refl <- witElemUniCons a b cs (remove c d) Refl -> Refl
{-# NOINLINE witElemUniCons #-}
{-# RULES "witElemUniCons" forall a b c d . witElemUniCons a b c d Refl = Unsafe.unsafeCoerce Refl #-}

witElemUni :: forall a b c . T a => P a -> Q b -> Q c -> Elem a b :~: 'True -> Elem a (Union b c) :~: 'True
witElemUni _ b (QualNone) Refl | Refl <- witUniIdent b = Refl
witElemUni a b (QualPred c cs) Refl =
    case testEq a c of
        Left  Refl | Refl <- witElemCons a b cs -> Refl
        Right Refl
            | Refl <- witElemUni a b cs Refl
            , Refl <- witElemUniCons a c b cs Refl
            -> Refl
{-# NOINLINE witElemUni #-}
{-# RULES "witElemUni" forall a b c . witElemUni a b c Refl = Unsafe.unsafeCoerce Refl #-}

witElemUniRefl :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Union b c) :~: Elem a (Union c b)
witElemUniRefl _ (QualNone) c | Refl <- witUniIdent c = Refl
witElemUniRefl a (QualPred b bs) c =
    case testEq a b of
        Left  Refl | Refl <- witElemCons a c bs -> Refl
        Right Refl
            | Refl <- witElemUniRefl a bs c
            , Refl <- witElemUniCons a b c bs Refl
            , Refl <- witElemUniRemove a b bs c Refl
            -> Refl
{-# NOINLINE witElemUniRefl #-}
{-# RULES "witElemUniRefl" forall a b c . witElemUniRefl a b c = Unsafe.unsafeCoerce Refl #-}

witElemUniRight :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Union b c) :~: 'True -> Elem a b :~: 'False -> Elem a c :~: 'True
witElemUniRight _ (QualNone) _ Refl _ = Refl
witElemUniRight a o@(QualPred b bs) c Refl Refl =
    case testEq a b of
        Left  x    -> case x of {}
        Right Refl
            | Refl <- witElemRemove a b o Refl
            , Refl <- witElemUniRefl a o c
            , Refl <- witElemUniRemove a b c o Refl
            , Refl <- witElemUniRefl a c bs
            , Refl <- witElemUniRight a bs c Refl Refl
            -> Refl

witElemUniEither :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Union b c) :~: 'True -> Either (Elem a b :~: 'True) (Elem a c :~: 'True)
witElemUniEither a b c Refl =
    case testElem a b of
        Left  Refl -> Left Refl
        Right Refl | Refl <- witElemUniRight a b c Refl Refl -> Right Refl

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

witSubAdd :: forall a b c . T a => P a -> Q b -> Q c -> Subset b (Remove a c) :~: 'True -> Subset b c :~: 'True
witSubAdd _ (QualNone) _ _ = Refl
witSubAdd a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c Refl =
    case testElem b c of
        Left Refl
            | Refl <- witSubRem b bs (remove a c) Refl
            , Refl <- witSubAdd a bs c Refl
            -> Refl
        Right Refl -> case witElemShrink b a c Refl of {}
{-# NOINLINE witSubAdd #-}
{-# RULES "witSubAdd" forall a b c . witSubAdd a b c Refl = Unsafe.unsafeCoerce Refl #-}

-- witSubRemove :: forall a b c . T a => P a -> Q b -> Q c -> Subset b c :~: 'True -> Subset (Remove a b) c :~: 'True
-- witSubRemove _ (QualNone) _ Refl = Refl
-- witSubRemove a (QualPred b bs) c Refl =
--     case testEq a b of
--         Left  Refl | Refl <- witSubRem b bs c Refl -> Refl
--         Right Refl | Refl <- witEqSym a b ->
--             case testElem b c of
--                 Left  Refl | Refl <- witSubRemove a bs c Refl -> Refl
--                 Right x -> case x of {}

witSubRemove :: forall a b c . T a => P a -> Q b -> Q c -> Elem a c :~: 'True -> Subset (Remove a b) c :~: Subset b c
witSubRemove _ (QualNone) _ _ = Refl
witSubRemove a (QualPred b bs) c Refl =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl -> case testElem b c of
            Left  Refl | Refl <- witSubRemove a bs c Refl -> Refl
            Right Refl -> Refl
{-# NOINLINE witSubRemove #-}
{-# RULES "witSubRemove" forall a b c . witSubRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRemove' :: forall a b c . T a => P a -> Q b -> Q c -> Elem a b :~: 'False -> Subset b (Remove a c) :~: Subset b c
witSubRemove' _ (QualNone) _ _ = Refl
witSubRemove' a (QualPred b bs) c Refl
    | Refl <- lem b bs Refl
    , Refl <- witEqSym b a
    , Refl <- witElemRemove b a c Refl
    = case testElem b c of
          Left  Refl | Refl <- witSubRemove' a bs c Refl -> Refl
          Right Refl -> Refl
  where
    lem :: forall d e . T d => P d -> Q e -> Elem a (d ':. e) :~: 'False -> a :/~: d
    lem d _ Refl =
        case testEq a d of
            Left  x    -> case x of {}
            Right Refl -> Refl
{-# NOINLINE witSubRemove' #-}
{-# RULES "witSubRemove'" forall a b c . witSubRemove' a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubShrink :: forall a b c . T a => P a -> Q b -> Q c -> Elem a (Remove a b) :~: 'False -> Elem a c :~: 'True -> Subset (Remove a b) (Remove a c) :~: Subset b c
witSubShrink a b c Refl Refl
    | Refl <- witSubRemove a b c Refl
    , Refl <- witSubRemove' a (remove a b) c Refl
    = Refl
{-# NOINLINE witSubShrink #-}
{-# RULES "witSubShrink" forall a b c . witSubShrink a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubIn :: forall a b c . T a => P a -> Q b -> Q c -> Subset b c :~: 'True -> Elem a b :~: 'True -> Elem a c :~: 'True
witSubIn a (QualPred b bs) c Refl Refl =
    case testEq a b of
        Left  Refl | Refl <- witSubElem b bs c Refl -> Refl
        Right Refl
            | Refl <- witSubRem b bs c Refl
            , Refl <- witSubIn a bs c Refl Refl
            -> Refl
{-# NOINLINE witSubIn #-}
{-# RULES "witSubIn" forall a b c . witSubIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubNotIn :: forall a b c . T a => P a -> Q b -> Q c -> Elem a b :~: 'True -> Elem a c :~: 'False -> Subset b c :~: 'False
witSubNotIn _ (QualNone) _ x _ = case x of {}
witSubNotIn a (QualPred b bs) c Refl Refl =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl -> case testElem b c of
           Left  Refl | Refl <- witSubNotIn a bs c Refl Refl -> Refl
           Right Refl -> Refl
{-# NOINLINE witSubNotIn #-}
{-# RULES "witSubNotIn" forall a b c . witSubNotIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubCons :: forall a b c . T a => P a -> Q b -> Q c -> Subset b c :~: 'True -> Subset b (a ':. c) :~: 'True
witSubCons _ (QualNone) _ _ = Refl
witSubCons a (QualPred b bs) c Refl =
    case testEq b a of
        Left Refl
            | Refl <- witSubRem b bs c Refl
            , Refl <- witSubCons a bs c Refl
            -> Refl
        Right Refl
            | Refl <- witSubElem b bs c Refl
            , Refl <- witSubCons a bs c Refl
            -> Refl
{-# NOINLINE witSubCons #-}
{-# RULES "witSubCons" forall a b c . witSubCons a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubRefl :: forall a . Q a -> Subset a a :~: 'True
witSubRefl (QualNone) = Refl
witSubRefl (QualPred a as)
    | Refl <- witSubRefl as
    , Refl <- witSubCons a as as Refl
    = Refl
{-# NOINLINE witSubRefl #-}
{-# RULES "witSubRefl" forall a . witSubRefl a = Unsafe.unsafeCoerce Refl #-}

witSubUni :: forall a b . Q a -> Q b -> Subset a (Union a b) :~: 'True
witSubUni (QualNone) _ = Refl
witSubUni (QualPred a as) b
    | Refl <- witSubUni as (remove a b)
    , Refl <- witSubCons a as (union as (remove a b)) Refl
    = Refl
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
    , Refl <- witSubIn a b c Refl Refl
    , Refl <- witSubTrans as b c Refl Refl
    = Refl
{-# NOINLINE witSubTrans #-}
{-# RULES "witSubTrans" forall a b c . witSubTrans a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Extends.

witExtRefl :: forall a . Q a -> Extends a a :~: 'True
witExtRefl (QualNone) = Refl
witExtRefl (QualPred _ as) | Refl <- witExtRefl as = Refl
{-# NOINLINE witExtRefl #-}
{-# RULES "witExtRefl" forall a . witExtRefl a = Unsafe.unsafeCoerce Refl #-}

witExtNotIn :: forall a b c . T a => P a -> Q b -> Q c -> Elem a b :~: 'True -> Elem a c :~: 'False -> Extends b c :~: 'False
witExtNotIn _ (QualNone) _ x _ = case x of {}
witExtNotIn a (QualPred b bs) c Refl Refl =
    case testElem b c of
        Left Refl -> case testEq a b of
            Left x -> case x of {}
            Right Refl
                | Refl <- witElemRemove a b c Refl
                , Refl <- witExtNotIn a bs (remove b c) Refl Refl
                -> Refl
        Right Refl -> Refl
{-# NOINLINE witExtNotIn #-}
{-# RULES "witExtNotIn" forall a b c . witExtNotIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witExtSub :: forall a b . Q a -> Q b -> Extends a b :~: 'True -> Subset a b :~: 'True
witExtSub (QualNone) _ _ = Refl
witExtSub (QualPred a as) b Refl =
    case testElem a b of
        Left  Refl
            | Refl <- witExtSub as (remove a b) Refl
            , Refl <- witSubAdd a as b Refl
            -> Refl
        Right x -> case x of {}
{-# NOINLINE witExtSub #-}
{-# RULES "witExtSub" forall a b . witExtSub a b Refl = Unsafe.unsafeCoerce Refl #-}

witExtElem :: forall a b c . T a => P a -> Q b -> Q c -> Extends (a ':. b) c :~: 'True -> Elem a c :~: 'True
witExtElem a b c Refl
    | Refl <- witExtSub (QualPred a b) c Refl
    , Refl <- witSubElem a b c Refl
    = Refl
{-# NOINLINE witExtElem #-}
{-# RULES "witExtElem" forall a b c . witExtElem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witExtIn :: forall a b c . T a => P a -> Q b -> Q c -> Extends b c :~: 'True -> Elem a b :~: 'True -> Elem a c :~: 'True
witExtIn _ (QualNone) _ _ x = case x of {}
witExtIn a (QualPred b bs) c Refl Refl | Refl <- witExtElem b bs c Refl =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl
            | Refl <- witExtIn a bs (remove b c) Refl Refl
            , Refl <- witElemRemove a b c Refl
            -> Refl
{-# NOINLINE witExtIn #-}
{-# RULES "witExtIn" forall a b c . witExtIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witExtAdd :: forall a b c . T a => P a -> Q b -> Q c -> Extends b (Remove a c) :~: 'True -> Extends b c :~: 'True
witExtAdd _ (QualNone) _ _ = Refl
witExtAdd a (QualPred b bs) c Refl =
    case testElem b c of
        Left  Refl
            | Refl <- witExtElem b bs (remove a c) Refl
            , Refl <- witRemOrd b a c
            , Refl <- witExtAdd a bs (remove b c) Refl
            -> Refl
        Right Refl
            | Refl <- witExtElem b bs (remove a c) Refl
            -> case witElemAdd b a c Refl of {}
{-# NOINLINE witExtAdd #-}
{-# RULES "witExtAdd" forall a b c . witExtAdd a b c Refl = Unsafe.unsafeCoerce Refl #-}

witExtRem :: forall a b c . T a => P a -> Q b -> Q c -> Extends (a ':. b) c :~: 'True -> Extends b c :~: 'True
witExtRem _ (QualNone) _ _ = Refl
witExtRem a (QualPred b bs) c Refl
    | Refl <- witExtElem a (QualPred b bs) c Refl
    , Refl <- witExtElem b bs (remove a c) Refl
    , Refl <- witRemOrd b a c
    , Refl <- witExtAdd a bs (remove b c) Refl
    , Refl <- witElemAdd b a c Refl
    = Refl
{-# NOINLINE witExtRem #-}
{-# RULES "witExtRem" forall a b c . witExtRem a b c Refl = Unsafe.unsafeCoerce Refl #-}

witExtCons :: forall a b c . T a => P a -> Q b -> Q c -> Extends b c :~: 'True -> Extends b (a ':. c) :~: 'True
witExtCons _ (QualNone) _ _ = Refl
witExtCons a (QualPred b bs) c Refl =
    case testEq a b of
        Left  Refl | Refl <- witExtRem a bs c Refl -> Refl
        Right Refl | Refl <- witEqSym a b -> case testElem b c of
            Left  Refl | Refl <- witExtCons a bs (remove b c) Refl -> Refl
            Right x    -> case x of {}
{-# NOINLINE witExtCons #-}
{-# RULES "witExtCons" forall a b c . witExtCons a b c Refl = Unsafe.unsafeCoerce Refl #-}
    
witExtShrink :: forall a b c . T a => P a -> Q b -> Q c -> Elem a c :~: 'True -> Extends (Remove a b) (Remove a c) :~: Extends b c
witExtShrink _ (QualNone) _ _ = Refl
witExtShrink a (QualPred b bs) c Refl =
    case testEq a b of
        Left  Refl -> Refl
        Right Refl | Refl <- witEqSym a b, Refl <- witElemRemove b a c Refl ->
            case testElem b c of
                Left  Refl
                  | Refl <- witRemOrd b a c
                  , Refl <- witElemRemove a b c Refl
                  , Refl <- witExtShrink a bs (remove b c) Refl -> Refl
                Right Refl -> Refl
{-# NOINLINE witExtShrink #-}
{-# RULES "witExtShrink" forall a b c . witExtShrink a b c Refl = Unsafe.unsafeCoerce Refl #-}

witExtRemove :: forall a b c . T a => P a -> Q b -> Q c -> Extends b c :~: 'True -> Extends (Remove a b) c :~: 'True
witExtRemove _ (QualNone) _ _ = Refl
witExtRemove a (QualPred b bs) c Refl
    | Refl <- witExtElem b bs c Refl
    , Refl <- witExtRemove a bs (remove b c) Refl
    = case testEq a b of
        Left  Refl | Refl <- witExtShrink a bs c Refl -> Refl
        Right Refl -> Refl
{-# NOINLINE witExtRemove #-}
{-# RULES "witExtRemove" forall a b c . witExtRemove a b c Refl = Unsafe.unsafeCoerce Refl #-}

witExtTrans :: forall a b c . Q a -> Q b -> Q c -> Extends a b :~: 'True -> Extends b c :~: 'True -> Extends a c :~: 'True
witExtTrans (QualNone) _ _ _ _ = Refl
witExtTrans (QualPred a as) b c Refl Refl
    | Refl <- witExtElem a as b Refl
    , Refl <- witExtIn a b c Refl Refl
    , Refl <- witExtRemove a b c Refl
    , Refl <- witExtShrink a b c Refl
    , Refl <- witExtTrans as (remove a b) (remove a c) Refl Refl
    = Refl
{-# NOINLINE witExtTrans #-}
{-# RULES "witExtTrans" forall a b c . witExtTrans a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Extends & Union (EU).

witEUAdd :: forall a b c . Q a -> Q b -> Q c -> Extends a b :~: 'True -> Extends a (Union b c) :~: 'True
witEUAdd (QualNone) _ _ _ = Refl
witEUAdd (QualPred a as) b c Refl
    | Refl <- witExtElem a as b Refl
    , Refl <- witElemUni a b c Refl
    , Refl <- witEUAdd as (remove a b) (remove a c) Refl
    , Refl <- witUniRemDist a b c
    = Refl

witEURefl :: forall a b c . Q a -> Q b -> Q c -> Extends a (Union b c) :~: Extends a (Union c b)
witEURefl (QualNone) _ _ = Refl
witEURefl (QualPred a as) b c
    | Refl <- witElemUniRefl a b c
    = case testElem a (union b c) of
        Left  Refl
            | Refl <- witEURefl as (remove a b) (remove a c)
            , Refl <- witUniRemDist a b c
            , Refl <- witUniRemDist a c b
            -> Refl
        Right Refl -> Refl

witEUBoth :: forall a b c d . Q a -> Q b -> Q c -> Q d -> Extends a b :~: 'True -> Extends c d :~: 'True -> Extends (Union a c) (Union b d) :~: 'True
witEUBoth (QualNone) b c d _ Refl
    | Refl <- witEUAdd c d b Refl
    , Refl <- witEURefl c d b
    = Refl
witEUBoth (QualPred a as) b c d Refl Refl
    | Refl <- witExtElem a as b Refl
    , Refl <- witElemUni a b d Refl
    , Refl <- witUniRemDist a b d
    = case testElem a d of
        Left  Refl
          | Refl <- witExtShrink a c d Refl
          , Refl <- witEUBoth as (remove a b) (remove a c) (remove a d) Refl Refl
          -> Refl
        Right Refl
          | Refl <- witElemId a d Refl
          , Refl <- witExtRemove a c d Refl
          , Refl <- witEUBoth as (remove a b) (remove a c) (remove a d) Refl Refl
          -> Refl

--------------------------------------------------------------------------------
-- Subset & Union (SU).

witSURemove :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b c) d
witSURemove a (QualNone) c d Refl | Refl <- witSubRemove a c d Refl = Refl
witSURemove a (QualPred b bs) c d Refl =
    case testElem b d of
        Left  Refl
          | Refl <- witRemOrd b a c
          , Refl <- witSURemove a bs (remove b c) d Refl
          -> Refl
        Right Refl -> Refl

witSUCons :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b c) d :~: Subset (Union b (a ':. c)) d
witSUCons _ (QualNone) _ _ Refl = Refl
witSUCons a (QualPred b bs) c d Refl =
    case testElem b d of
        Left  Refl -> case testEq b a of
            Left  Refl | Refl <- witSURemove a bs c d Refl -> Refl
            Right Refl | Refl <- witSUCons a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl
    
witSURefl :: forall a b c . Q a -> Q b -> Q c -> Subset (Union a b) c :~: Subset (Union b a) c
witSURefl (QualNone) b _ | Refl <- witUniIdent b = Refl
witSURefl (QualPred a as) b c =
    case testElem a c of
        Left  Refl
          | Refl <- witSURemove a as b c Refl
          , Refl <- witSURefl as b c
          , Refl <- witSUCons a b as c Refl
          -> Refl
        Right Refl
          | Refl <- witElemCons a b as
          , Refl <- witSubNotIn a (union b (QualPred a as)) c Refl Refl
          -> Refl

witSURefl' :: forall a b c . Q a -> Q b -> Q c -> Subset a (Union b c) :~: Subset a (Union c b)
witSURefl' (QualNone) _ _ = Refl
witSURefl' (QualPred a as) b c
  | Refl <- witElemUniRefl a b c
  , Refl <- witSURefl' as b c
  = Refl

--------------------------------------------------------------------------------

lemSU1 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a (Remove a c))) d :~: Subset (Union b c) d
lemSU1 a b c d Refl
  | Refl <- witSURemove a b c d Refl
  , Refl <- witSURemove a b (remove a c) d Refl
  = Refl

lemSU2 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b (a ':. c)) d
lemSU2 a b c d Refl | Refl <- lemSU1 a b (QualPred a c) d Refl = Refl

lemSU3 :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Elem a d :~: 'True -> Subset (Union b (Remove a c)) d :~: Subset (Union b (a ':. c)) d
lemSU3 a (QualNone) c d Refl | Refl <- witSubRemove a c d Refl = Refl
lemSU3 a (QualPred (b :: P q) (bs :: Q qs)) c d Refl =
    case testElem b d of
        Left  Refl -> case testEq b a of
            Left  Refl | Refl <- lemSU1 a bs c d Refl -> Refl
            Right Refl
              | Refl <- witRemOrd b a c
              , Refl <- lemSU2 a bs (remove b c) d Refl -> Refl
        Right Refl -> Refl

lemSU4 :: forall a b c d . (T a, T b) => P a -> P b -> Q c -> Q d -> a :/~: b -> Elem a (Union c (Remove b d)) :~: Elem a (Union c (b ':. d))
lemSU4 a b c d Refl
  | Refl <- witElemUniRemove a b c d Refl
  , Refl <- witElemUniCons a b c d Refl
  = Refl

witSU1L :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Subset (Union (a ':. b) c) d :~: Subset (Union b (a ':. c)) d
witSU1L a b c d =
    case testElem a d of
        Left  Refl | Refl <- lemSU3 a b c d Refl -> Refl
        Right Refl
          | Refl <- witElemCons a b c
          , Refl <- witSubNotIn a (union b (QualPred a c)) d Refl Refl -> Refl 

witSU1R :: forall a b c d . T a => P a -> Q b -> Q c -> Q d -> Subset b (Union (a ':. c) d) :~: Subset b (Union c (a ':. d))
witSU1R _ (QualNone) _ _ = Refl
witSU1R a (QualPred b bs) c d =
    case testEq b a of
        Left  Refl | Refl <- witElemCons a c d, Refl <- witSU1R a bs c d -> Refl
        Right Refl | Refl <- lemSU4 b a c d Refl ->
            case testElem b (union c (remove a d)) of
                Left  Refl | Refl <- witSU1R a bs c d -> Refl
                Right Refl -> Refl

--------------------------------------------------------------------------------
-- Fin.
