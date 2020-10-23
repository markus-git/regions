{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Qualifiers where
{-
    (
    -- * Qualifiers.
      Put(..)
    , Place
    , Qualifiers(..)
    , QualRep(..)
    , Qual(..)
    ) where
-}

import qualified Language.Diorite.Syntax as S (Signature(..), SigRep(..))

import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- * Qualifiers.
--------------------------------------------------------------------------------

-- | "Put" predicate, asserts that region 'r' is allocated.
data Put r = Put r

-- ...

--------------------------------------------------------------------------------
-- * Annotated signatures.
--------------------------------------------------------------------------------

data Annotation r a =
         Const a
       | Annotation r a :-> Annotation r a
       | Put r :=> Annotation r a
       | Annotation r a :^ r

infixr 2 :->, :=>
infixl 1 :^

-- | The 'erasure' of a annotated signature removes any constraints and labels.
type family Erasure (ann :: Annotation r *) where
    Erasure ('Const a) = 'Const a
    Erasure (a ':-> b) = Erasure a ':-> Erasure b
    Erasure (_ ':=> a) = Erasure a
    Erasure (a ':^ _)  = Erasure a

-- | ...
type family Strip (ann :: Annotation r *) :: S.Signature (Put r) * where
    Strip ('Const a) = 'S.Const a
    Strip (a ':-> b) = Strip a 'S.:-> Strip b
    Strip (p ':=> a) = p 'S.:=> Strip a
    Strip (a ':^ _)  = Strip a

--------------------------------------------------------------------------------

-- | ...
data AnnRep (ann :: Annotation r *) where
    AnnConst :: Typeable a => AnnRep ('Const a)
    AnnPart  :: AnnRep a -> AnnRep ann -> AnnRep (a ':-> ann)
    AnnPred  :: Proxy ('Put r) -> AnnRep ann -> AnnRep ('Put r ':=> ann)
    AnnAt    :: AnnRep ann -> AnnRep (ann ':^ r)

-- | ...
class Ann (ann :: Annotation * *) where
    annotation :: AnnRep ann

instance Typeable a => Ann ('Const a) where
    annotation = AnnConst

instance (Ann a, Ann ann) => Ann (a ':-> ann) where
    annotation = AnnPart annotation annotation

instance Ann ann => Ann ('Put r ':=> ann) where
    annotation = AnnPred Proxy annotation

instance Ann ann => Ann (ann ':^ r) where
    annotation = AnnAt annotation

-- | ...
erase :: AnnRep ann -> S.SigRep (Strip ann)
erase (AnnConst)    = S.SigConst
erase (AnnPart a b) = S.SigPart (erase a) (erase b)
erase (AnnPred p a) = S.SigPred p (erase a)
erase (AnnAt a)     = erase a

--------------------------------------------------------------------------------
{-
-- | Location names, associated with a "Put" predicate on an 'r'.
type Place r = Int

-- | Collection of predicates of a region-qualified symbol.
data Qualifiers r = Put r :- Qualifiers r | None
  -- todo: Use an actual collection, rather than a list.

infixr :-

-- | Witness of a symbol constraint.
data QualRep (ps :: Qualifiers *) where
    QualNone :: QualRep ('None)
    QualPred :: Proxy p -> QualRep ps -> QualRep ('Put p ':- ps)

-- | Valid symbol constraints.
class Qual (ps :: Qualifiers *) where
    qualifier :: QualRep ps

instance Qual ('None) where
    qualifier = QualNone

instance Qual ps => Qual ('Put p ':- ps) where
    qualifier = QualPred Proxy qualifier
-}
--------------------------------------------------------------------------------
