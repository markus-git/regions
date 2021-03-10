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
    , Element
    , QualRep(..)
    , Qual(..)
    , (:-)(..)
--  , union
--  , remove
    , witUnionNone
    -- * ???
    , Ext(..)
    , Flat
    , ExtRep(..)
    , flatten
    ) where

import Data.Constraint (Dict(..), withDict)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)

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
    SigPred  :: Typeable p => Proxy p -> SigRep sig -> SigRep (p ':=> sig)

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
type family Insert q qs where
    Insert q ('None)    = q ':. 'None
    Insert q (q ':. qs) = q ':. qs
    Insert q (a ':. qs) = a ':. Insert q qs
  
-- | Join the predicates from two sets of qualifiers.
type family Union qs ps where
    Union ('None)    ps = ps
    Union (q ':. qs) ps = Insert q (Union qs ps)

-- | Remove a predicate from a set of qualifiers.
type family Remove q qs where
    Remove _ ('None)    = 'None
    Remove q (q ':. qs) = qs
    Remove q (a ':. qs) = a ':. Remove q qs

-- | ...
type family Element q qs where
    Element _ ('None)    = 'False
    Element q (q ':. qs) = 'True
    Element q (_ ':. qs) = Element q qs

--------------------------------------------------------------------------------
-- ** Rep. of a valid qualifier.

-- | Witness of a symbol qualifier.
data QualRep (qs :: Qualifier p) where
    QualNone  :: QualRep ('None)
    QualPred  :: Proxy q -> QualRep qs -> QualRep (q ':. qs)

-- | Valid symbol qualifiers.
class Qual (qs :: Qualifier p) where
    qualifier :: QualRep qs

instance Qual ('None) where
    qualifier = QualNone

instance Qual qs => Qual (q ':. qs) where
    qualifier = QualPred Proxy qualifier

-- | ...
class qs :- q where
    entails :: QualRep qs -> Proxy q

instance (q ':. qs) :- q where
    entails (QualPred p _) = p

instance (qs :- q) => (p ':. qs) :- q where
    entails (QualPred _ qs) = entails qs

--------------------------------------------------------------------------------

witUnionNone :: QualRep a -> Dict (Union a 'None ~ a)
witUnionNone (QualNone) = Dict
witUnionNone (QualPred a as)
    | Dict <- witUnionNone as
    = undefined

witUnionRefl :: QualRep a -> QualRep b -> Dict (Union a b ~ Union b a)
witUnionRefl (QualNone) b | Dict <- witUnionNone b = Dict
witUnionRefl (QualPred a as) b
    | Dict <- witUnionRefl as b
    = undefined

witUnionAssoc ::
     QualRep a
  -> QualRep b
  -> QualRep c
  -> Dict (Union a (Union b c) ~ Union (Union a b) c)
witUnionAssoc (QualNone) b c = Dict
witUnionAssoc (QualPred a as) b c
    | Dict <- witUnionAssoc as b c
    = undefined

{-
-- | Implementation of 'Both'.
class Union qs ps where
    union :: QualRep qs -> QualRep ps -> QualRep (Both qs ps)

instance Union 'None ps where
    union (QualNone) ps = ps

instance {-# OVERLAPS #-} Union qs ps => Union (q ':. qs) ps where
    union (QualPred q qs) ps = QualPred q (union qs ps)

-- | Implementation of 'Minus'.
class Remove qs q where
    remove :: QualRep qs -> Proxy q -> QualRep (Minus qs q)

instance Remove 'None q where
    remove QualNone Proxy = QualNone

instance {-# OVERLAPS #-} Remove qs q => Remove (q ':. qs) q where
    remove (QualPred _ qs) q = remove qs q

instance {-# OVERLAPPABLE #-} (Minus (p ':. qs) q ~ (p ':. Minus qs q), Remove qs q) => Remove (p ':. qs) q where
    remove (QualPred p qs) q = QualPred p (remove qs q)
-}

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

data Ext p = X | Y (Ext p) (Ext p) | Z p (Ext p)

type family Flat (ps :: Ext p) :: Qualifier p where
    Flat ('X)       = 'None
    Flat ('Y ps rs) = Union (Flat ps) (Flat rs)
    Flat ('Z p  rs) = Insert p (Flat rs)

data ExtRep (ex :: Ext p) where
    ExtX :: ExtRep 'X
    ExtY :: ExtRep qs -> ExtRep ps -> ExtRep ('Y qs ps)
    ExtZ :: Proxy q -> ExtRep qs -> ExtRep ('Z q qs)

flatten :: ExtRep p -> QualRep (Flat p)
flatten (ExtX)       = QualNone
--flatten (ExtY ps rs) = union (flatten ps) (flatten rs)
--flatten (ExtZ p  rs) = insert p (flatten rs)

--------------------------------------------------------------------------------
-- Fin.
