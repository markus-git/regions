{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Sugar
    (
    -- * Syntactic sugaring.
      Syntactic(..)
    , resugar
    , sugarSym
    ) where

-- Related stuff:
--   https://emilaxelsson.github.io/documents/axelsson2013using.pdf

import Language.Diorite.Syntax
    ( Put(..), Qualifiers(..), Signature(..), Sig(..)
    , Name, Beta(..), Eta(..), lam)

--------------------------------------------------------------------------------
-- * Syntactic sugaring.
--------------------------------------------------------------------------------

-- | Syntactic sugaring for 'AST' embeddings.
class Syntactic a where
    type Domain a   :: Signature (Put *) * -> *
    type Internal a :: Signature (Put *) *
    sugar   :: Beta (Domain a) 'None (Internal a) -> a
    desugar :: a -> Eta (Domain a) 'None (Internal a)

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
    tail' :: Eta (Domain a) 'None ('Const a) -> Beta (Domain a) 'None ('Const a)
    tail' (Spine b) = b

instance Syntactic (Beta sym 'None ('Const a)) where
    type Domain   (Beta sym 'None ('Const a)) = sym
    type Internal (Beta sym 'None ('Const a)) = 'Const a
    sugar   = id
    desugar = Spine

instance Syntactic (Eta sym 'None ('Const a)) where
    type Domain   (Eta sym 'None ('Const a)) = sym
    type Internal (Eta sym 'None ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id

-- | Syntactic functions.
instance
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    , Sig (Internal a)
    )
    => Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a ':-> Internal b
    sugar   f = sugar . (f :$) . desugar
    desugar f = lam (desugar . f . sugar)

-- | Sugared symbol application.
sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym

--------------------------------------------------------------------------------
-- Fin.
