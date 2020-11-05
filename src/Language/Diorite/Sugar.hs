{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}

module Language.Diorite.Sugar
    (
    -- * Syntactic sugaring.
      Syntactic(..)
--    , resugar
    , sugarSym
    ) where

-- Related stuff:
--   https://emilaxelsson.github.io/documents/axelsson2013using.pdf

import Language.Diorite.Syntax
    (Signature(..), Pred, Sig(..), Beta(..), Eta(..), lam)

--------------------------------------------------------------------------------
-- * Syntactic sugaring.
--------------------------------------------------------------------------------

-- | Syntactic sugaring for 'AST' embeddings.
class Syntactic a where
    type Domain a   :: Signature p * -> *
    type Internal a :: Signature p *
    sugar   :: Beta (Domain a) (Internal a) -> a
    desugar :: a -> Eta (Domain a) (Internal a)

instance Syntactic (Beta sym ('Const a)) where
    type Domain (Beta sym ('Const a))   = sym
    type Internal (Beta sym ('Const a)) = 'Const a
    sugar   = id
    desugar = Spine

instance Syntactic (Eta sym ('Const a)) where
    type Domain (Eta sym ('Const a))   = sym
    type Internal (Eta sym ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id

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

-- | Syntactic type casting.
resugar ::
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    , Internal a ~ Internal b
    )
    => a -> b
resugar = sugar . tail' . desugar
  where
    tail' :: Eta (Domain a) ('Const a) -> Beta (Domain a) ('Const a)
    tail' (Spine b) = b

-- | Sugared symbol application.
sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym

--------------------------------------------------------------------------------
-- Fin.
