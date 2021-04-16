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
    -- , resugar
    -- , sugarSym
    ) where

-- Related stuff:
--   https://emilaxelsson.github.io/documents/axelsson2013using.pdf

import Language.Diorite.Signatures (Signature(..), Sig, Qualifier(..), Union, Difference)
import Language.Diorite.Syntax (Beta(..), Eta(..), lam)

import Data.Constraint (Constraint)
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

-- (qs :: Qualifier p)
instance forall p a b .
    ( Syntactic a
    , Syntactic b
    , p ~ Pred b
    , Pred a ~ Pred b
    , Domain @p a ~ Domain @p b
--    , Context @p b ~ Union qs (Context @p a)
--    , qs ~ Difference (Context @p b) (Context @p a)
    , Sig (Internal @p a)
    )
    => Syntactic (a -> b)
  where
    type Pred     (a -> b) = Pred a
    type Domain   (a -> b) = Domain a
    type Context  (a -> b) = Context @p b --Difference (Context @p b) (Context @p a)
    type Internal (a -> b) = Internal a ':-> Internal b
    -- sugar f   = sugar . (f :$) . desugar
    -- desugar f = lam (desugar . f . sugar)
    sugar f = \a ->
      let a0 = a :: a in
      let f0 = f :: Beta @p (Domain @p (a->b)) (Context @p (a->b)) (Internal @p (a->b)) in
      -- (:$) :: Beta s qs (a->b) -> Eta s ps a -> Beta s (Union qs ps) b
      let f1 = f0 :: Beta @p (Domain @p a) (Context @p (a->b)) (Internal @p a ':-> Internal @p b) in
      -- f1 > Domain   (a->b) ~ Domain a
      --    > Internal (a->b) ~ Internal a -> Internal b
      let a1 = desugar a0 :: Eta @p (Domain @p a) (Context @p a) (Internal @p a) in
      let b0 = f1 :$ a1   :: Beta @p (Domain @p a) (Union (Context @p (a->b)) (Context @p a)) (Internal @p b) in
      -- ?? > Context b ~ Union (Context (a->b)) (Context a)
      let res = sugar (undefined :: Beta @p (Domain @p b) (Context @p b) (Internal @p b)) :: b in
      res
    desugar f =
      lam (\a ->
        let a0 = a :: Beta @p (Domain @p a) (Context @p a) (Internal @p a) in
        let f0 = f :: a -> b in
        -- lam :: (Beta s ps a -> Eta s qs b) -> Eta s qs (a->b)
        let a1 = sugar a0   :: a in
        let b0 = f0 a1      :: b in
        let b1 = desugar b0 :: Eta @p (Domain @p b) (Context @p b) (Internal @p b) in
        -- ?? > Context b ~ Context (a->b)
        let res = undefined :: Eta @p (Domain @p b) (Context @p (a->b)) (Internal @p b) in
        res)

-- -- | Syntactic type casting.
-- resugar ::
--     ( Syntactic a
--     , Syntactic b
--     , Domain a ~ Domain b
--     , Internal a ~ Internal b
--     )
--     => a -> b
-- resugar = sugar . tail' . desugar
--   where
--     tail' :: Eta (Domain a) 'None ('Const a) -> Beta (Domain a) 'None ('Const a)
--     tail' (Spine b) = b

-- | Sugared symbol application.
-- sugarSym :: (Syntactic p a, (Context a :: Qualifier p) ~ 'None) => (Domain a :: Signature p * -> *) (Internal a :: Signature p *) -> a
-- sugarSym = sugar . Sym

--------------------------------------------------------------------------------
-- Fin.
