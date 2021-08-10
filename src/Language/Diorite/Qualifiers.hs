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
--  , type (>=)
--  , type (~=)
    -- ** ...
    , QualRep(..)
    , Qual(..)
    -- ** ...
    , (:/~:)
    , test
    , testElem
    , insert
    , remove
    , union
    -- ** ...
    , witQual
    ) where

import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..), testEquality)
import Data.Typeable (Typeable)
import Type.Reflection (TypeRep, typeRep)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)

--------------------------------------------------------------------------------
-- * Qualifiers.
--------------------------------------------------------------------------------

-- | Collection of predicates.
type Qualifier :: * -> *
data Qualifier p = None | p :. Qualifier p

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
type Set :: forall p . Qualifier p -> Bool
type family Set qs where
    Set ('None)    = 'True
    Set (q ':. qs) = If (Elem q qs) 'False (Set qs)

-- type qs >= ps = (Subset ps qs ~ 'True)
-- type qs ~= ps = (Subset ps qs ~ 'True, Subset qs ps ~ 'True)

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
test :: forall k (a :: k) (b :: k) . (Typeable a, Typeable b) => Proxy a -> Proxy b -> Either (a :~: b) (a :/~: b)
test _ _ = case testEquality (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
    Just Refl -> Left Refl
    Nothing   -> Right (Unsafe.unsafeCoerce Refl)

-- | Check whether 'a' is an "element" of 'b' or not.
testElem :: forall k (a :: k) (b :: Qualifier k) . Typeable a => Proxy a -> QualRep b -> Either (Elem a b :~: 'True) (Elem a b :~: 'False)
testElem _ (QualNone) = Right Refl
testElem a (QualPred b bs) = case test a b of
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
-- ** ...

-- | ...
witQual :: QualRep qs -> Dict (Qual qs)
witQual (QualNone)      = Dict
witQual (QualPred _ qs) | Dict <- witQual qs = Dict

--------------------------------------------------------------------------------
-- Fin.
