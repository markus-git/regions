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
    sugar   :: forall p . Pred a ~ p => Beta @p (Domain @p a) (Context @p a) (Internal @p a) -> a
    desugar :: forall p . Pred a ~ p => a -> Eta @p (Domain @p a) (Context @p a) (Internal @p a)

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

instance forall p (qs :: Qualifier p) a b .
    ( Syntactic a
    , Syntactic b
    , p ~ Pred b
    , Pred a ~ Pred b
    , Domain @p a ~ Domain @p b
    , Context @p b ~ Union qs (Context @p a)
    , qs ~ Difference (Context @p b) (Context @p a)
    , Sig (Internal @p a)
    )
    => Syntactic (a -> b)
  where
    type Pred     (a -> b) = Pred a
    type Domain   (a -> b) = Domain a
    type Context  (a -> b) = Difference (Context @p b) (Context @p a)
    type Internal (a -> b) = Internal a ':-> Internal b
    -- sugar f   = sugar . (f :$) . desugar
    -- desugar f = lam (desugar . f . sugar)
    sugar f = \a ->
        -- > desugar 'a' into arg.
      let x0 = desugar a :: Eta @p (Domain @p a) (Context @p a) (Internal @p a) in
        -- > rewrite 'f' to fit 'a' arg.
      let x1 = f :: Beta @p (Domain @p (a->b)) (Context @p (a->b)) (Internal @p (a->b)) in
        -- D (a->b) ~ D a
        -- I (a->b) ~ I a :-> I b
      let x2 = x1 :: Beta @p (Domain @p a) (Context @p (a->b)) (Internal @p a ':-> Internal @p b) in
        -- > apply 'f' to 'a'.
      let x3 = x2 :$ x0 :: Beta @p (Domain @p a) (Union (Context @p (a->b)) (Context @p a)) (Internal @p b) in
        -- D a ~ D b
        -- C b ~ Union qs (C a)
      let x4 = x3 :: Beta @p (Domain @p b) (Union qs (Context @p a)) (Internal @p b) in
        -- ...
      let x5 = sugar x4 :: b in
        -- ...
      x5
    desugar f =
      lam (\a ->
          -- sugar 'a' into ast. arg.
        let x0 = sugar a :: a in
          -- apply 'f' to arg.
        let x1 = f x0 :: b in
          -- desugar and rewrite 'x1' into result.
        let x2 = desugar x1 :: Eta @p (Domain @p b) (Context @p b) (Internal @p b) in
          -- C b ~ Union qs (C a)
        let x3 = x2 :: Eta @p (Domain @p b) (Union qs (Context @p a)) (Internal @p b) in
          -- hmm... how to get from 'x3' to 'x8'... or did I do something wrong?
        let x8 = undefined :: Eta @p (Domain @p (a->b)) (Context @p (a->b)) (Internal @p b) in
          -- D (a->b) ~ D a
        let x9 = x8 :: Eta @p (Domain @p a) qs (Internal @p b) in
        x9)

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
