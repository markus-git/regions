{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fprint-explicit-foralls #-}

{-# LANGUAGE UndecidableInstances #-} -- hmm..

module Language.Diorite.Signatures
    (
    -- * Signatures.
      Signature(..)
    , Result
    , SigRep(..)
    , Sig(..)
    , testSig
    , witSig
    , witTypeable
    -- * Qualifiers.
    , Qualifier(..)
    , Insert
    , Union
    , Remove
    , QualRep(..)
    , Qual(..)
    , (:-)(..)
    , insert'
    , remove'
    , union'
    , witInsIdem
    , witRemOrd
    , witRemDist
    , witUniIdent
    , witUniAssoc
    -- * ???
    , Ext(..)
    , Flat
    , NotIn
    , ExtRep(..)
    , flatten'
    , ExtC(..)
    -- * ...
    , eqP
    ) where

import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..), testEquality)
import Data.Typeable (Typeable, eqT)
import Type.Reflection (TypeRep, typeRep)
-- Hmm..
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)
--import qualified GHC.Exts as Exts (Any)

--------------------------------------------------------------------------------
-- * ... type-level stuff ...
--------------------------------------------------------------------------------

-- | ...
type family (==) (a :: k) (b :: k) :: Bool where
    a == a = 'True
    _ == _ = 'False
  
-- | ... If-then-else ...
type family If (c :: Bool) (a :: k) (b :: k) where
    If 'True  a b = a
    If 'False a b = b

-- | Short-hand for type inequality.
type a :/~: b = (a == b) :~: 'False

-- | Get a proof of whether two types are equal or not
test :: forall k (a :: k) (b :: k) . (Typeable a, Typeable b) => Proxy a -> Proxy b -> Either (a :~: b) (a :/~: b)
test _ _ = case testEquality (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
    Just Refl -> Left Refl
    Nothing   -> Right (Unsafe.unsafeCoerce Refl)

--------------------------------------------------------------------------------
-- * Signatures.
--------------------------------------------------------------------------------

-- | Signature of a symbol.
data Signature p a =
      Const a
    | Signature p a :-> Signature p a
    | p :=> Signature p a

infixr 2 :->, :=>

-- | Denotational result of a symbol's signature.
type family Result (sig :: Signature p *) where
    Result ('Const a) = a
    Result (a ':-> b) = Result b
    Result (p ':=> a) = Result a

--------------------------------------------------------------------------------
-- ** Rep. of a valid signature.

-- | Witness of a symbol signature.
data SigRep (sig :: Signature p *) where
    SigConst :: Typeable a => SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Typeable q => Proxy q -> SigRep sig -> SigRep (q ':=> sig)

-- | Valid symbol signatures.
class Sig (sig :: Signature p *) where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance (Typeable p, Sig sig) => Sig (p ':=> sig) where
    signature = SigPred Proxy signature

--------------------------------------------------------------------------------

-- | Extract a witness of equality of two constant types.
testConst :: SigRep ('Const a) -> SigRep ('Const b) -> Maybe (a :~: b)
testConst SigConst SigConst = eqT

-- | Extract a witness of equality of two types.
testSig :: SigRep a -> SigRep b -> Maybe (a :~: b)
testSig a1@(SigConst) a2@(SigConst)
    | Just Refl <- testConst a1 a2
    = Just Refl
testSig (SigPart a1 b1) (SigPart a2 b2)
    | Just Refl <- testSig a1 a2
    , Just Refl <- testSig b1 b2
    = Just Refl
testSig (SigPred (_ :: Proxy x) a1) (SigPred (_ :: Proxy y) a2)
    | Just Refl <- eqT :: Maybe (x :~: y)
    , Just Refl <- testSig a1 a2
    = Just Refl
testSig _ _ = Nothing

-- | Any witness of a symbol signature is a valid symbol signature.
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred _ a) | Dict <- witSig a = Dict

-- | Any witness of a constant symbol signature is typeable.
witTypeable :: SigRep ('Const a) -> Dict (Typeable a)
witTypeable (SigConst) = Dict

--------------------------------------------------------------------------------
-- * Qualifiers.
--------------------------------------------------------------------------------

-- | Collection of predicates.
data Qualifier p =
      None
    | p :. Qualifier p

infixr 2 :.

-- | ...
type family Insert p qs where
    Insert p ('None)    = p ':. 'None
    Insert p (q ':. qs) = If (p == q) (q ':. qs) (q ':. Insert p qs)
  
-- | Remove a predicate from a set of qualifiers.
type family Remove p qs where
    Remove _ ('None)    = 'None
    Remove p (q ':. qs) = If (p == q) (qs) (q ':. Remove p qs)

-- | Join the predicates from two sets of qualifiers.
type family Union ps qs where
    Union ('None)    qs = qs
    Union (p ':. ps) qs = p ':. Union ps (Remove p qs)

--------------------------------------------------------------------------------
-- ** Rep. of a valid qualifier.

-- | Witness of a symbol qualifier.
data QualRep (qs :: Qualifier p) where
    QualNone  :: QualRep ('None)
    QualPred  :: Typeable q => Proxy q -> QualRep qs -> QualRep (q ':. qs)

-- | Valid symbol qualifiers.
class Qual (qs :: Qualifier p) where
    qualifier :: QualRep qs

instance Qual ('None) where
    qualifier = QualNone

instance (Typeable q, Qual qs) => Qual (q ':. qs) where
    qualifier = QualPred Proxy qualifier

--------------------------------------------------------------------------------

-- | ...
class qs :- q where
    entails :: QualRep qs -> Proxy q

instance {-# OVERLAPS #-} forall k (q :: k) (qs :: Qualifier k) . (q ':. qs) :- q where
    entails (QualPred p _) = p

instance {-# OVERLAPPABLE #-} forall k (q :: k) (qs :: Qualifier k) (p :: k) . (qs :- q) => (p ':. qs) :- q where
    entails (QualPred _ qs) = entails qs

--------------------------------------------------------------------------------
-- *** Implementation of ...

-- | Implementation of 'Insert'.
class Insertable p qs where
    insert :: Proxy p -> QualRep qs -> QualRep (Insert p qs)

instance Typeable p => Insertable p 'None where
    insert p (QualNone) = QualPred p QualNone

instance {-# OVERLAPS #-} Insertable p (p ':. qs) where
    insert _ (QualPred q qs) = QualPred q qs

instance {-# OVERLAPPABLE #-} (Insert p (q ':. qs) ~ (q ':. Insert p qs), Insertable p qs) => Insertable p (q ':. qs) where
    insert p (QualPred q qs) = QualPred q (insert p qs)

-- | Implementation of 'Remove'.
class Removeable p qs where
    remove :: Proxy p -> QualRep qs -> QualRep (Remove p qs)

instance Removeable p 'None where
    remove _ (QualNone) = QualNone

instance {-# OVERLAPS #-} Removeable p (p ':. qs) where
    remove _ (QualPred _ qs) = qs

instance {-# OVERLAPPABLE #-} (Remove p (q ':. qs) ~ (q ':. Remove p qs), Removeable p qs) => Removeable p (q ':. qs) where
    remove p (QualPred q qs) = QualPred q (remove p qs)

-- | Implementation of 'Union'.
class Unionable ps qs where
    union :: QualRep ps -> QualRep qs -> QualRep (Union ps qs)

instance Unionable 'None qs where
    union (QualNone) qs = qs

instance (Removeable p qs, Unionable ps (Remove p qs)) => Unionable (p ':. ps) qs where
    union (QualPred p ps) qs = QualPred p (union ps (remove p qs))

--------------------------------------------------------------------------------
-- ... or ...

insert' :: Typeable p => Proxy p -> QualRep qs -> QualRep (Insert p qs)
insert' p (QualNone)      = QualPred p QualNone
insert' p (QualPred q qs) = case test p q of
    Left  Refl -> QualPred q qs
    Right Refl -> QualPred q (insert' p qs)

remove' :: Typeable p => Proxy p -> QualRep qs -> QualRep (Remove p qs)
remove' _ (QualNone)      = QualNone
remove' p (QualPred q qs) = case test p q of
    Left  Refl -> qs
    Right Refl -> QualPred q (remove' p qs)

union' :: QualRep ps -> QualRep qs -> QualRep (Union ps qs)
union' (QualNone)      qs = qs
union' (QualPred p ps) qs = QualPred p (union' ps (remove' p qs))

--------------------------------------------------------------------------------
-- *** Witness of ...

witInsIdem :: Typeable a => Proxy a -> QualRep b -> Insert a (Insert a b) :~: Insert a b
witInsIdem _ (QualNone) = Refl
witInsIdem a (QualPred b bs) | Refl <- witInsIdem a bs =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> Refl

witRemOrd :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> QualRep c -> Remove a (Remove b c) :~: Remove b (Remove a c)
witRemOrd _ _ (QualNone) = Refl
witRemOrd a b (QualPred c cs) | Refl <- witRemOrd a b cs =
    case (test a c, test b c) of
        (Left  Refl, Left  Refl) -> Refl
        (Right Refl, Right Refl) -> Refl
        (Left  Refl, Right Refl) -> Refl
        (Right Refl, Left  Refl) -> Refl

witRemDist :: forall a b c . Typeable a => Proxy a -> QualRep b -> QualRep c -> Remove a (Union b c) :~: Union (Remove a b) (Remove a c)
witRemDist _ (QualNone) _ = Refl
witRemDist a (QualPred (b :: Proxy q) (bs :: QualRep qs)) c =
    case test a b of
        Left  Refl -> Refl
        Right Refl -> case (lhs, rhs) of
            (Refl, Refl) -> Refl
  where
    lhs :: (q ':. Remove a (Union qs (Remove q c))) :~: (q ':. Union (Remove a qs) (Remove a (Remove q c)))
    lhs = case witRemDist a bs (remove' b c) of Refl -> Refl

    rhs :: Union (q ':. Remove a qs) (Remove a c) :~: (q ':. Union (Remove a qs) (Remove a (Remove q c)))
    rhs = case witRemOrd a b c of Refl -> Refl

witUniIdent :: QualRep a -> Union a 'None :~: a
witUniIdent (QualNone) = Refl
witUniIdent (QualPred _ as) | Refl <- witUniIdent as = Refl

--witUniIns :: Typeable a => Proxy a -> QualRep b -> QualRep c -> Union (Insert a b) c :~: Insert a (Union b c)
--witUniIns _ (QualNone) _ = undefined

witUniAssoc :: forall a b c . QualRep a -> QualRep b -> QualRep c -> Union a (Union b c) :~: Union (Union a b) c
witUniAssoc (QualNone) _ _ = Refl
witUniAssoc (QualPred (a :: Proxy q) (as :: QualRep qs)) b c =
    case (lhs, rhs) of
        (Refl, Refl) -> Refl
  where
    lhs :: Union (q ':. qs) (Union b c) :~: (q ':. Union qs (Union (Remove q b) (Remove q c)))
    lhs = case witRemDist a b c of Refl -> Refl
    
    rhs :: Union (Union (q ':. qs) b) c :~: (q ':. Union qs (Union (Remove q b) (Remove q c)))
    rhs = case witUniAssoc as (remove' a b) (remove' a c) of Refl -> Refl

--------------------------------------------------------------------------------
-- * ???
--------------------------------------------------------------------------------

data Ext p = X | Y (Ext p) (Ext p) | Z p (Ext p)

type family Flat (ps :: Ext p) :: Qualifier p where
    Flat ('X)       = 'None
    Flat ('Y ps rs) = Union (Flat ps) (Flat rs)
    Flat ('Z p  rs) = Flat rs

type NotIn p ps = Remove p (Flat ps) :~: (Flat ps)

data ExtRep (ex :: Ext p) where
    ExtX :: ExtRep 'X
    ExtY :: ExtRep qs -> ExtRep ps -> ExtRep ('Y qs ps)
    ExtZ :: Typeable q => NotIn q qs -> Proxy q -> ExtRep qs -> ExtRep ('Z q qs)

flatten' :: ExtRep p -> QualRep (Flat p)
flatten' (ExtX)        = QualNone
flatten' (ExtY ps rs)  = union' (flatten' ps) (flatten' rs)
flatten' (ExtZ _ _ rs) = flatten' rs

class ExtC (ex :: Ext p) where
    ext :: ExtRep ex

instance ExtC ('X) where
    ext = ExtX

instance (ExtC ps, ExtC rs) => ExtC ('Y ps rs) where
    ext = ExtY ext ext

instance (Typeable p, Remove p (Flat rs) ~ (Flat rs), ExtC rs) => ExtC ('Z p rs) where
    ext = ExtZ Refl Proxy ext

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | ...
eqP :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> Maybe (a :~: b)
eqP _ _ = eqT

--------------------------------------------------------------------------------
-- Fin.
