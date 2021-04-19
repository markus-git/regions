{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fprint-explicit-foralls #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE FunctionalDependencies #-}
--{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}

module Language.Diorite.Sugar
    (
    -- * Syntactic sugaring.
      Syntactic(..)
    , resugar
    , sugarSym
    ) where

-- Related stuff:
--   https://emilaxelsson.github.io/documents/axelsson2013using.pdf

import Language.Diorite.Signatures (Signature(..), Sig)
import Language.Diorite.Qualifiers (Qualifier(..), QualRep, Qual(..), witUniIdent)
import Language.Diorite.Syntax (Beta(..), Eta(..), lam)

import Data.Constraint (Constraint, withDict)
--import Data.Kind

--------------------------------------------------------------------------------
-- * Syntactic sugaring.
--------------------------------------------------------------------------------  

-- | Syntactic sugaring for 'AST' embeddings.
type Syntactic :: * -> Constraint
class Syntactic a where
    type Pred a     :: *
    type Domain a   :: Signature p * -> *
    type Context a  :: Qualifier p
    type Internal a :: Signature p *
    sugar   :: Pred a ~ p => Beta @p (Domain @p a) (Context @p a) (Internal @p a) -> a
    desugar :: Pred a ~ p => a -> Eta @p (Domain @p a) (Context @p a) (Internal @p a)

instance Syntactic (Beta @p sym qs ('Const a)) where
    type Pred     (Beta sym qs ('Const a)) = p
    type Domain   (Beta sym qs ('Const a)) = sym
    type Context  (Beta sym qs ('Const a)) = qs
    type Internal (Beta sym qs ('Const a)) = 'Const a
    sugar   = id
    desugar = Spine

instance Syntactic (Eta @p sym qs ('Const a)) where
    type Pred     (Eta sym qs ('Const a)) = p
    type Domain   (Eta sym qs ('Const a)) = sym
    type Context  (Eta sym qs ('Const a)) = qs
    type Internal (Eta sym qs ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id

instance
    ( Syntactic a
    , Syntactic b
    , Pred a ~ Pred b
    , Domain  @(Pred a) a ~ Domain @(Pred a) b
    , Context @(Pred a) a ~ 'None
    , Sig  (Internal @(Pred a) a)
    , Qual (Context  @(Pred a) b)
    )
    => Syntactic (a -> b)
  where
    type Pred     (a -> b) = Pred b
    type Domain   (a -> b) = Domain b
    type Context  (a -> b) = Context b
    type Internal (a -> b) = Internal a ':-> Internal b
    sugar f = withDict wit sugar . (f :$) . desugar
        where wit = witUniIdent (qualifier :: QualRep (Context @(Pred a) b))
    desugar f = lam (desugar . f . sugar)

-- | Syntactic type casting.
resugar :: forall a b c.
    ( Syntactic a
    , Syntactic b
    , Pred a ~ Pred b
    , Domain   @(Pred a) a ~ Domain   @(Pred a) b
    , Internal @(Pred a) a ~ Internal @(Pred a) b
    , Context  @(Pred a) a ~ Context  @(Pred a) b
    , Internal @(Pred a) a ~ 'Const c
    )
    => a -> b
resugar = sugar . tail' . desugar
  where
    tail' :: Eta @p (Domain a) (Context a) ('Const c) -> Beta @p (Domain a) (Context a) ('Const c)
    tail' (Spine b) = b

-- | Sugared symbol application.
sugarSym :: (Syntactic a, Context @(Pred a) a ~ 'None) => (Domain a) (Internal @(Pred a) a) -> a
sugarSym = sugar . Sym

--------------------------------------------------------------------------------
-- Fin.
