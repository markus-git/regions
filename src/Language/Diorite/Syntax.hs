{-# OPTIONS_GHC -Wall #-}

-- Related stuff:
--   https://github.com/Feldspar/feldspar-language
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

module Language.Diorite.Syntax
    ( Name
    , Place
    , Region
    , Put(..)
    , Signature(..)
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    -- 
    , SigRep(..)
    , Sig(..)
    , Sym(..)
    --
    , Empty
    , Ex(..)
    , liftE
    ) where

--import Data.Typeable (Typeable)

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Place names.
type Place = Name

-- | Name of a region, associated with one or more places.
type Region = Name

-- | "Put" predicate, asserts that a region is allocated.
data Put = Put
  -- todo: Add Phantom type to 'Put' for its region.

-- | Signature of a symbol.
data Signature a = Const a | Signature a :-> Signature a | Put :=> Signature a

infixr :->, :=>

-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym (sig :: Signature *) where
    Var  :: Name -> Beta sym sig
    Sym  :: sym sig -> Beta sym sig
    (:$) :: Beta sym (a ':-> sig) -> Eta sym a -> Beta sym sig
    (:#) :: Beta sym ('Put ':=> sig) -> Place -> Beta sym sig
  -- todo: Have Haskell handle regions a la "Typing Dynamic Typing"(?).

data Eta sym (sig :: Signature *) where
    (:\)  :: Name -> Eta sym sig -> Eta sym (a ':-> sig)
    (:\\) :: Place -> Eta sym sig -> Eta sym ('Put ':=> sig)
    Spine :: Beta sym ('Const sig) -> Eta sym ('Const sig)

infixl 1 :$, :#

infixr :\, :\\

-- | Generic AST, parameterized by a symbol domain.
type AST sym sig = Beta sym sig

-- | Fully applied AST (constant value).
type ASTF sym sig = Beta sym ('Const sig)

--------------------------------------------------------------------------------
-- ** Type/Signature witness.
--------------------------------------------------------------------------------

-- | Witness of a symbol signature.
data SigRep (sig :: Signature *) where
    SigConst :: SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: SigRep sig -> SigRep ('Put ':=> sig)

-- | Valid symbol signatures.
class Sig sig where
    signature :: SigRep sig

instance Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance Sig sig => Sig ('Put ':=> sig) where
    signature = SigPred signature

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

--------------------------------------------------------------------------------
-- ** Utils.
--------------------------------------------------------------------------------

-- | Empty symbol type
data Empty :: * -> *

-- | Existential quantification.
data Ex e where
    Ex :: e a -> Ex e

liftE :: (forall a . e a -> b) -> Ex e -> b
liftE f (Ex a) = f a

--------------------------------------------------------------------------------
-- Fin.
