{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Diorite.Qualifiers
    (
    -- * Qualifiers.
      Qualifier(..)
    , type (==)
    , If
    , Insert
    , Remove
    , Union
    , Difference
    , Elem
    , Subset
    , type (>=)
    -- ** ...
    , QualRep(..)
    , Qual(..)
    -- ** ...
    , insert
    , remove
    , union
    -- ** ...
    , witInsIdem
    , witRemOrd
    , witRemDist
    , witUniIdent
    , witUniAssoc
    , witElemCons
    , witElemRem
    , witElemUniRem
    , witElemSub
    , witElemRefl
    , witSubElem
    , witSubRem
    , witSubCons
    , witSubRefl
    , witSubIn
    , witSubTrans
    , witSubUni
    ) where

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..), testEquality)
import Data.Typeable (Typeable)
import Type.Reflection (TypeRep, typeRep)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

--------------------------------------------------------------------------------
-- * Qualifiers.
--------------------------------------------------------------------------------

-- | Collection of predicates.
data Qualifier p =
      None
    | p :. Qualifier p

infixr 2 :.

-- | ...
type (==) :: forall k . k -> k -> Bool
type family (==) a b where
    a == a = 'True
    _ == _ = 'False
  
-- | ...
type If :: forall k . Bool -> k -> k -> k
type family If c a b where
    If 'True  a b = a
    If 'False a b = b

-- | Insert a predicate into a set of qualifiers.
type Insert :: forall p . p -> Qualifier p -> Qualifier p
type family Insert p qs where
    Insert p ('None)    = p ':. 'None
    Insert p (q ':. qs) = If (p == q) (q ':. qs) (q ':. Insert p qs)
  
-- | Remove a predicate from a set of qualifiers.
type Remove :: forall p . p -> Qualifier p -> Qualifier p
type family Remove p qs where
    Remove _ ('None)    = 'None
    Remove p (q ':. qs) = If (p == q) (qs) (q ':. Remove p qs)

-- | Join the predicates from two sets of qualifiers.
type Union :: forall p . Qualifier p -> Qualifier p -> Qualifier p
type family Union ps qs where
    Union ('None)    qs = qs
    Union (p ':. ps) qs = p ':. Union ps (Remove p qs)

-- | Remove any predicates in the second set of qualifiers from the first set.
type Difference :: forall p . Qualifier p -> Qualifier p -> Qualifier p
type family Difference ps qs where
  Difference ps ('None)    = ps
  Difference ps (q ':. qs) = Difference (Remove q ps) qs

-- | Check if a predicate is part of a set of qualifiers.
type Elem :: forall p . p -> Qualifier p -> Bool
type family Elem p qs where
    Elem p ('None)    = 'False
    Elem p (q ':. qs) = If (p == q) 'True (Elem p qs)

-- | Check if the first set of qualifiers is a subset of the second one.
type Subset :: forall p . Qualifier p -> Qualifier p -> Bool
type family Subset ps qs where
    Subset ('None)    qs = 'True
    Subset (p ':. ps) qs = If (Elem p qs) (Subset ps qs) 'False

-- | ...
type qs >= ps = (Subset ps qs ~ 'True)

--------------------------------------------------------------------------------
-- ** Rep. of a valid qualifier.

-- | Witness of a symbol qualifier.
type QualRep :: forall p . Qualifier p -> *
data QualRep qs where
    QualNone  :: QualRep ('None)
    QualPred  :: Typeable q => Proxy q -> QualRep qs -> QualRep (q ':. qs)

-- | Valid symbol qualifiers.
class Qual qs where
    qualifier :: QualRep qs

instance Qual ('None) where
    qualifier = QualNone

instance (Typeable q, Qual qs) => Qual (q ':. qs) where
    qualifier = QualPred Proxy qualifier

--------------------------------------------------------------------------------
-- ** Implementation of ...

-- | Short-hand for type inequality.
type (:/~:) :: forall k . k -> k -> *
type (:/~:) a b = (a == b) :~: 'False

-- | Check whether 'a' and 'b' are equal or not.
test :: forall k (a :: k) (b :: k)
    .  (Typeable a, Typeable b)
    => Proxy a
    -> Proxy b
    -> Either (a :~: b) (a :/~: b)
test _ _ =
    case testEquality (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
        Just Refl -> Left Refl
        Nothing   -> Right (Unsafe.unsafeCoerce Refl)

-- | Check whether 'a' is an "element" of 'b' or not.
testElem :: forall k (a :: k) (b :: Qualifier k)
    .  Typeable a
    => Proxy a
    -> QualRep b
    -> Either (Elem a b :~: 'True) (Elem a b :~: 'False)
testElem _ (QualNone) = Right Refl
testElem a (QualPred b bs) =
    case test a b of
        Left  Refl -> Left Refl
        Right Refl -> testElem a bs

insert :: Typeable p => Proxy p -> QualRep qs -> QualRep (Insert p qs)
insert p (QualNone)      = QualPred p QualNone
insert p (QualPred q qs) =
    case test p q of
      Left  Refl -> QualPred q qs
      Right Refl -> QualPred q (insert p qs)

remove :: Typeable p => Proxy p -> QualRep qs -> QualRep (Remove p qs)
remove _ (QualNone)      = QualNone
remove p (QualPred q qs) =
    case test p q of
      Left  Refl -> qs
      Right Refl -> QualPred q (remove p qs)

union :: QualRep ps -> QualRep qs -> QualRep (Union ps qs)
union (QualNone)      qs = qs
union (QualPred p ps) qs = QualPred p (union ps (remove p qs))

--------------------------------------------------------------------------------
-- *** Witness of ...

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

witSubRem :: forall a as b . QualRep (a ':. as) -> QualRep b -> Subset (a ':. as) b :~: 'True -> Subset as b :~: 'True
witSubRem a b Refl | Refl <- witSubElem a b Refl = Refl
{-# NOINLINE witSubRem #-}
{-# RULES "witSubRem" forall a b . witSubRem a b Refl = Unsafe.unsafeCoerce Refl #-}

witSubCons :: forall a b c . Typeable c => QualRep a -> QualRep b -> Proxy c -> Subset a b :~: 'True -> Subset a (c ':. b) :~: 'True
witSubCons (QualNone) _ _ _ = Refl
witSubCons (QualPred a as) b c Refl =
    case test a c of
        Left  Refl | Refl <- witSubRem  (QualPred a as) b Refl, Refl <- witSubCons as b c Refl -> Refl
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
        Right Refl | Refl <- witSubRem x b Refl, Refl <- witSubIn as b c Refl Refl -> Refl
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

witSubUni :: forall a b . QualRep a -> QualRep b -> Subset (Union a b) (Union b a) :~: 'True
witSubUni (QualNone) b
    | Refl <- witUniIdent b
    , Refl <- witSubRefl b
    = Refl
witSubUni (QualPred (_ :: Proxy q) (_ :: QualRep qs)) _
   -- | Refl <- witUniElem a b as
   -- , Refl <- witSubUni as b
    = undefined
    -- Subset (Union (a:as) b) (Union b (a:as))
    --   > Union (p : ps) qs = p : Union ps (Remove p qs)
    -- Subset (a : Union as (Remove a b)) (Union b (a:as))
    --   > Subset (p : ps) qs = If (Elem p qs) (Subset ps qs) False
    -- If (Elem a (Union b (a:as))) (Subset (Union as (Remove a b)) (Union b (a:as))) False
    --   > Elem a (Union b (a:as)) = True
    -- Subset (Union as (Remove a b)) (Union b (a:as))
    --   > ...

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
