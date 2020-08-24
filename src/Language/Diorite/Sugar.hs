{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Sugar
    ( Syntactic(..)
    , resugar
    , sugarSym
    ) where

import Language.Diorite.Syntax (Beta(..), Eta(..), Signature(..), Name)

--------------------------------------------------------------------------------
-- * Syntactic sugaring.
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

instance Syntactic (Eta sym ('Const a)) where
    type Domain   (Eta sym ('Const a)) = sym
    type Internal (Eta sym ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id

-- | Get the highest name bound for \"Eta\" node.
maxLamEta :: Eta sym a -> Name
maxLamEta (n :\ _)  = n
maxLamEta (_ :\\ e) = maxLamEta e
maxLamEta (Spine b) = maxLamBeta b

-- | Get the highest name bound for \"Beta\" node.
maxLamBeta :: Beta sym a -> Name
maxLamBeta (b :$ e) = maxLamBeta b `Prelude.max` maxLamEta e
maxLamBeta (b :# _) = maxLamBeta b
maxLamBeta _        = 0

-- | Interface for variable binding.
lam :: (Beta sym a -> Eta sym b) -> Eta sym (a ':-> b)
lam f = v :\ body
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

-- | Sugared symbol application.
sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym

--------------------------------------------------------------------------------
-- Fin.
