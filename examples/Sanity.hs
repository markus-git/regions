{-# OPTIONS_GHC -Wall #-}

module Sanity where

import Language.Diorite.Syntax
import Language.Diorite.Interpretation

--------------------------------------------------------------------------------
-- * Sanity test.
--------------------------------------------------------------------------------

data Put a

data S a where
    X :: S ('Const Int ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)
    Y :: S ((('Const Int ':-> 'Const Int) ':-> 'Const Int) ':-> 'Const Int)
    Z :: S (('Const Int ':->  ('Const Int ':-> 'Const Int)) ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"
    renderSym (Y) = "Y"
    renderSym (Z) = "Z"

type B a = Beta S ('None :: Qualifier (Put *)) a

--------------------------------------------------------------------------------

x, xs :: B ('Const Int) -> (B ('Const Int) -> B ('Const Int)) -> B ('Const Int)
x  = \a -> \f -> Sym X :$ Spine a :$ (lam (\v -> Spine (f v)))
xs = smartSym' X

y, ys :: ((B ('Const Int) -> B ('Const Int)) -> B ('Const Int)) -> B ('Const Int)
y  = \f -> Sym Y :$ (lam (\v -> Spine (f (\b -> v :$ (Spine b)))))
ys = smartSym' Y

z, zs :: (B ('Const Int) -> (B ('Const Int) -> B ('Const Int))) -> B ('Const Int)
z  = \f -> Sym Z :$ (lam (\b1 -> (lam (\b2 -> Spine (f b1 b2)))))
zs = smartSym' Z

--------------------------------------------------------------------------------

yt :: B ('Const Int)
yt = ys (\f -> f var)
  where
    var :: B ('Const Int)
    var = Var 9

--------------------------------------------------------------------------------
-- Fin.
