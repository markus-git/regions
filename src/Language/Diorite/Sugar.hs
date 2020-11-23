{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE FunctionalDependencies #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}
--{-# LANGUAGE InstanceSigs #-}

module Language.Diorite.Sugar
    (
    -- * Syntactic sugaring.
--      Syntactic(..)
--    , resugar
--    , sugarSym
    ) where

-- Related stuff:
--   https://emilaxelsson.github.io/documents/axelsson2013using.pdf

import Language.Diorite.Syntax
    (Signature(..), Sig(..), Qualifier(..), Both, Beta(..), Eta(..), lam)

--------------------------------------------------------------------------------
-- * Syntactic sugaring.
--------------------------------------------------------------------------------
{-
type family Pred (qs :: Qualifier p) :: * where
    Pred (_ :: Qualifier p) = p
-}
-- | Syntactic sugaring for 'AST' embeddings.
class Syntactic a where
    type Domain a :: Signature p * -> *
    type Internal a :: Signature p *
    type Constraint a :: Qualifier p
    sugar :: Beta (Domain a) (Constraint a) (Internal a) -> a
--    desugar :: a -> Eta (Domain a) (Constraint a) (Internal a)

instance Syntactic (Beta sym 'None ('Const a)) where
    type Domain (Beta sym 'None ('Const a)) = sym
    type Internal (Beta sym 'None ('Const a)) = 'Const a
    type Constraint (Beta sym 'None ('Const a)) = 'None
    sugar = id
--    desugar = Spine

{-
instance Syntactic (Eta sym 'None ('Const a)) where
    type Domain (Eta sym 'None ('Const a))   = sym
    type Internal (Eta sym 'None ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id
-}
{-
instance
    ( Syntactic a
    , Syntactic b
    , (Domain a :: Signature p * -> *) ~ (Domain b :: Signature p * -> *)
    , Sig (Internal a :: Signature p *)
    )
    => Syntactic (a -> b)
  where
    type Domain (a -> b)    = Domain a
    type Internal (a -> b)  = Internal a ':-> Internal b
    sugar f   = sugar . (f :$) . desugar
    desugar f = lam (desugar . f . sugar)
-}
{-
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
    tail' :: Eta (Domain a) 'None ('Const a) -> Beta (Domain a) 'None ('Const a)
    tail' (Spine b) = b

-- | Sugared symbol application.
sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym
-}
--------------------------------------------------------------------------------
-- Fin.
