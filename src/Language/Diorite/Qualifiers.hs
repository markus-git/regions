{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}

module Language.Diorite.Qualifiers
    (
    -- * Qualifiers.
      Qualifier(..)
    , Insert
    , Remove
    , Union
    , Difference
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
    -- * Existentials.
    , Exists(..)
    , SmartQual
    , Unique
    , ExRep(..)
    , Ex(..)
    -- ** ...
    , smartQual
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

-- | ...
type Difference :: forall p . Qualifier p -> Qualifier p -> Qualifier p
type family Difference ps qs where
  Difference ps ('None)    = ps
  Difference ps (q ':. qs) = Difference (Remove q ps) qs

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

-- | ...
insert :: Typeable p => Proxy p -> QualRep qs -> QualRep (Insert p qs)
insert p (QualNone)      = QualPred p QualNone
insert p (QualPred q qs) = case test p q of
    Left  Refl -> QualPred q qs
    Right Refl -> QualPred q (insert p qs)

-- | ...
remove :: Typeable p => Proxy p -> QualRep qs -> QualRep (Remove p qs)
remove _ (QualNone)      = QualNone
remove p (QualPred q qs) = case test p q of
    Left  Refl -> qs
    Right Refl -> QualPred q (remove p qs)

-- | ...
union :: QualRep ps -> QualRep qs -> QualRep (Union ps qs)
union (QualNone)      qs = qs
union (QualPred p ps) qs = QualPred p (union ps (remove p qs))

--------------------------------------------------------------------------------
-- *** Witness of ...

-- | ...
witInsIdem :: Typeable a => Proxy a -> QualRep b -> Insert a (Insert a b) :~: Insert a b
witInsIdem _ (QualNone) = Refl
witInsIdem a (QualPred b bs) | Refl <- witInsIdem a bs =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> Refl

-- | ...
witRemOrd :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> Remove a (Remove b c) :~: Remove b (Remove a c)
witRemOrd _ _ (QualNone) = Refl
witRemOrd a b (QualPred c cs) | Refl <- witRemOrd a b cs =
    case (test a c, test b c) of
        (Left  Refl, Left  Refl) -> Refl
        (Right Refl, Right Refl) -> Refl
        (Left  Refl, Right Refl) -> Refl
        (Right Refl, Left  Refl) -> Refl

-- | ...
witRemDist :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
witRemDist _ (QualNone) _ = Refl
witRemDist a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case (lhs, rhs) of
            (Refl, Refl) -> Refl
  where
    lhs :: (q ':. Remove a (Union qs (Remove q c))) :~: (q ':. Union (Remove a qs) (Remove a (Remove q c)))
    lhs = case witRemDist a bs (remove b c) of Refl -> Refl

    rhs :: Union (q ':. Remove a qs) (Remove a c) :~: (q ':. Union (Remove a qs) (Remove a (Remove q c)))
    rhs = case witRemOrd a b c of Refl -> Refl

-- | ...
witUniIdent :: QualRep a -> Union a 'None :~: a
witUniIdent (QualNone) = Refl
witUniIdent (QualPred _ as) | Refl <- witUniIdent as = Refl

-- | ...
witUniAssoc :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Union a (Union b c) :~: Union (Union a b) c
witUniAssoc (QualNone) _ _ = Refl
witUniAssoc (QualPred (a :: Proxy q) (as :: QualRep qs)) b c =
    case (lhs, rhs) of
        (Refl, Refl) -> Refl
  where
    lhs :: Union (q ':. qs) (Union b c) :~: (q ':. Union qs (Union (Remove q b) (Remove q c)))
    lhs = case witRemDist a b c of Refl -> Refl
    
    rhs :: Union (Union (q ':. qs) b) c :~: (q ':. Union qs (Union (Remove q b) (Remove q c)))
    rhs = case witUniAssoc as (remove a b) (remove a c) of Refl -> Refl

--------------------------------------------------------------------------------
-- * Exists-stuff
--
-- Since existential quantification isn't really a thing I have these.
-- Not sure this is the best way. Names are also a bit wierd.
--------------------------------------------------------------------------------

-- | ...
data Exists p = Empty | (Exists p) :- (Exists p) | p := (Exists p)

-- | ...
type Unique :: forall p . p -> Exists p -> *
type Unique q qs = Remove q (SmartQual qs) :~: (SmartQual qs)

--------------------------------------------------------------------------------

-- | ...
type ExRep :: Exists p -> *
data ExRep es where
    ExEmpty :: ExRep 'Empty
    ExUnion :: ExRep qs -> ExRep ps -> ExRep (qs ':- ps)
    ExPred  :: Typeable q => Unique q qs -> Proxy q -> ExRep qs -> ExRep (q ':= qs)

-- | ...
class Ex es where
    record :: ExRep es

instance Ex ('Empty) where
    record = ExEmpty

instance (Ex qs, Ex ps) => Ex (qs ':- ps) where
    record = ExUnion record record

instance (Typeable q, Remove q (SmartQual qs) ~ (SmartQual qs), Ex qs) => Ex (q ':= qs) where
    record = ExPred Refl Proxy record

--------------------------------------------------------------------------------
-- ** todo: smartqual is a bad name for these...

-- | ...
type SmartQual :: forall p . Exists p -> Qualifier p
type family SmartQual es where
    SmartQual ('Empty)    = 'None
    SmartQual (ps ':- qs) = Union (SmartQual ps) (SmartQual qs)
    SmartQual (_  ':= qs) = SmartQual qs

-- | ...
smartQual :: ExRep es -> QualRep (SmartQual es)
smartQual (ExEmpty)       = QualNone
smartQual (ExUnion qs ps) = union (smartQual qs) (smartQual ps)
smartQual (ExPred _ _ qs) = smartQual qs

--------------------------------------------------------------------------------
-- * ... type-level stuff ...
--------------------------------------------------------------------------------

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

-- | Short-hand for type inequality.
type (:/~:) :: forall k . k -> k -> *
type (:/~:) a b = (a == b) :~: 'False

-- | Check whether 'a' and 'b' are equal or not.
test :: forall k (a :: k) (b :: k) . (Typeable a, Typeable b) => Proxy a -> Proxy b -> Either (a :~: b) (a :/~: b)
test _ _ = case testEquality (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
    Just Refl -> Left Refl
    Nothing   -> Right (Unsafe.unsafeCoerce Refl)

--------------------------------------------------------------------------------
-- Fin.
