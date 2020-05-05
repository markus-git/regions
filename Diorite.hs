{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

-- Related stuff:
--   https://github.com/Feldspar/feldspar-language
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

module Diorite where

--------------------------------------------------------------------------------
-- * Abstract syntax tree for source.
--------------------------------------------------------------------------------

-- | Signature of a symbol.
data Signature a = Const a | Signature a :-> Signature a

infixr :->

-- | Variable names.
type Name = Integer
  
-- | Generic abstact sytnax tree with beta-eta long normal form.
data Beta sym (sig :: Signature *) where
    Var  :: Name -> Beta sym sig
    Sym  :: sym sig -> Beta sym sig
    (:$) :: Beta sym (sig ':-> a) -> Eta sym sig -> Beta sym a

data Eta sym (sig :: Signature *) where
    Lam   :: Name -> Eta sym a -> Eta sym (sig ':-> a)
    Spine :: Beta sym ('Const sig) -> Eta sym ('Const sig)

infixl 1 :$

-- | Generic AST, parameterized by a symbol domain.
type AST sym sig  = Beta sym sig

-- | Fully applied AST (constant value).
type ASTF sym sig = Beta sym ('Const sig)

--------------------------------------------------------------------------------
-- * Sugar
--------------------------------------------------------------------------------

-- | Syntactic sugaring for AST embeddings.
class Syntactic a where
    type Domain a   :: Signature * -> *
    type Internal a :: Signature *
    sugar   :: Beta (Domain a) (Internal a) -> a
    desugar :: a -> Eta (Domain a) (Internal a)

-- | Syntactic type casting.
resugar ::
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    , Internal a ~ Internal b
    , Internal a ~ 'Const a
    )
    => a -> b
resugar = sugar . tail' . desugar
  where
    tail' :: Eta (Domain a) ('Const a) -> Beta (Domain a) ('Const a)
    tail' (Spine b) = b

instance Syntactic (Beta sym ('Const a)) where
    type Domain   (Beta sym ('Const a)) = sym
    type Internal (Beta sym ('Const a)) = 'Const a
    sugar   = id
    desugar = Spine

-- | Sugared symbol application.
sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym

instance Syntactic (Eta sym ('Const a)) where
    type Domain   (Eta sym ('Const a)) = sym
    type Internal (Eta sym ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id

-- | Get the highest name bound.
maxLamEta :: Eta sym a -> Name
maxLamEta (Lam n _) = n
maxLamEta (Spine b) = maxLamBeta b
  where
    maxLamBeta :: Beta sym b -> Name
    maxLamBeta (s :$ a) = maxLamBeta s `Prelude.max` maxLamEta a
    maxLamBeta _        = 0

-- | Interface for variable binding.
lam :: (Beta sym a -> Eta sym b) -> Eta sym (a ':-> b)
lam f = Lam v body
  where
    v    = maxLamEta body + 1
    body = f $ Var v

-- | Syntactic functions.
instance
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    )
    => Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a ':-> Internal b
    sugar   f = sugar . (f :$) . desugar
    desugar f = lam (desugar . f . sugar)

--------------------------------------------------------------------------------
-- * Decoration
--------------------------------------------------------------------------------

-- | Denotational result of signature.
type family Result a where
    Result ('Const a) = a
    Result (a ':-> b) = Result b

-- | Decorated symbol.
data (sym :&: info) a where
    (:&:) :: sym a -> info (Result a) -> (sym :&: info) a

--------------------------------------------------------------------------------
-- * Region labelling
--------------------------------------------------------------------------------

-- | Region names.
type Region = Name

-- | Signature of a symbol labelled with regions.
data Labeling a = Value a Region | Function (Labeling a) Region (Labeling a)

-- | Representation of supported types.
class Eq a => Primitive a where
    data Rep a :: *
    typeRep :: Rep a

--------------------------------------------------------------------------------
-- * Region annotation.
--------------------------------------------------------------------------------

-- | Place name (associated with a region).
newtype Place a = Place Name

infer :: ASTF sym sig -> ASTF (sym :&: Place) sig
infer = undefined

--------------------------------------------------------------------------------
-- * Example
--------------------------------------------------------------------------------

data Exp a where
    Int :: Num a => a -> Exp ('Const a)
    Let :: Exp ('Const a ':-> ('Const a ':-> 'Const b) ':-> 'Const b)

