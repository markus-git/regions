{-# OPTIONS_GHC -Wall #-}

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
    , witSubsetElem
    , witSubsetRem
    , witSubsetCons
    , witSubsetRefl
    , witSubsetIn
    , witSubsetTrans
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
test _ _ = case testEquality (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
    Just Refl -> Left Refl
    Nothing   -> Right (Unsafe.unsafeCoerce Refl)

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

witInsIdem :: Typeable a => Proxy a -> QualRep b -> Insert a (Insert a b) :~: Insert a b
witInsIdem _ (QualNone) = Refl
witInsIdem a (QualPred b bs) | Refl <- witInsIdem a bs =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> Refl
{-# NOINLINE witInsIdem #-}
{-# RULES "witInsIdem" forall a b . witInsIdem a b = Unsafe.unsafeCoerce Refl #-}

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

witElemCons :: forall a b c . (Typeable a, Typeable c) => Proxy a -> QualRep b -> Proxy c -> Elem a b :~: 'True -> Elem a (c ':. b) :~: 'True
witElemCons a _ c (Refl) =
    case test a c of
        Left  Refl -> Refl
        Right Refl -> Refl
{-# NOINLINE witElemCons #-}
{-# RULES "witElemCons" forall a b c . witElemCons a b c = Unsafe.unsafeCoerce Refl #-}

testElem :: Typeable a => Proxy a -> QualRep b -> Either (Elem a b :~: 'True) (Elem a b :~: 'False)
testElem _ (QualNone) = Right Refl
testElem a (QualPred b bs) =
    case test a b of
        Left  Refl -> Left Refl
        Right Refl -> testElem a bs

-- note: removing 'Right ..' leads to missing cases, but writing out 'Right Refl' produces an inaccessible rhs error...
witSubsetElem :: forall a as b . QualRep (a ':. as) -> QualRep b -> Subset (a ':. as) b :~: 'True -> Elem a b :~: 'True
witSubsetElem (QualPred a _) b Refl =
    case testElem a b of
        Left  Refl -> Refl
        Right _    -> error "inaccessible right hand side"
{-# NOINLINE witSubsetElem #-}
{-# RULES "witSubsetElem" forall a b . witSubsetElem a b Refl = Unsafe.unsafeCoerce Refl #-}

witSubsetRem :: forall a as b . QualRep (a ':. as) -> QualRep b -> Subset (a ':. as) b :~: 'True -> Subset as b :~: 'True
witSubsetRem a b Refl | Refl <- witSubsetElem a b Refl = Refl
{-# NOINLINE witSubsetRem #-}
{-# RULES "witSubsetRem" forall a b . witSubsetRem a b Refl = Unsafe.unsafeCoerce Refl #-}

witSubsetCons :: forall a b c . Typeable c => QualRep a -> QualRep b -> Proxy c -> Subset a b :~: 'True -> Subset a (c ':. b) :~: 'True
witSubsetCons (QualNone) _ _ _ = Refl
witSubsetCons (QualPred a as) b c Refl =
    case test a c of
        Left  Refl | Refl <- witSubsetRem  (QualPred a as) b Refl, Refl <- witSubsetCons as b c Refl -> Refl
        Right Refl | Refl <- witSubsetElem (QualPred a as) b Refl, Refl <- witSubsetCons as b c Refl -> Refl
{-# NOINLINE witSubsetCons #-}
{-# RULES "witSubsetCons" forall a b c . witSubsetCons a b c Refl = Unsafe.unsafeCoerce Refl #-}

witSubsetRefl :: forall a . QualRep a -> Subset a a :~: 'True
witSubsetRefl (QualNone) = Refl
witSubsetRefl (QualPred a as) | Refl <- witSubsetRefl as, Refl <- witSubsetCons as as a Refl = Refl
{-# NOINLINE witSubsetRefl #-}
{-# RULES "witSubsetRefl" forall a . witSubsetRefl a = Unsafe.unsafeCoerce Refl #-}

witSubsetIn :: forall a b c . Typeable c => QualRep a -> QualRep b -> Proxy c -> Subset a b :~: 'True -> Elem c a :~: 'True -> Elem c b :~: 'True
witSubsetIn x@(QualPred a as) b c Refl Refl =
    case test c a of
        Left  Refl | Refl <- witSubsetElem x b Refl -> Refl
        Right Refl | Refl <- witSubsetRem x b Refl, Refl <- witSubsetIn as b c Refl Refl -> Refl
{-# NOINLINE witSubsetIn #-}
{-# RULES "witSubsetIn" forall a b c . witSubsetIn a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

witSubsetTrans :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Subset a b :~: 'True -> Subset b c :~: 'True -> Subset a c :~: 'True
witSubsetTrans (QualNone) _ _ _ _ = Refl
witSubsetTrans x@(QualPred a as) b c Refl Refl
    | Refl <- witSubsetElem x b Refl
    , Refl <- witSubsetIn b c a Refl Refl
    , Refl <- witSubsetTrans as b c Refl Refl
    = Refl
{-# NOINLINE witSubsetTrans #-}
{-# RULES "witSubsetTrans" forall a b c . witSubsetTrans a b c Refl Refl = Unsafe.unsafeCoerce Refl #-}

--------------------------------------------------------------------------------
-- Fin.
