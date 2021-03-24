{-# OPTIONS_GHC -Wall #-}

module SmartSym where

import Language.Diorite.Signatures (Signature(..), Qualifier(..))
import Language.Diorite.Syntax
import Language.Diorite.Interpretation

--------------------------------------------------------------------------------
-- * 'smartSym' translations without qualifiers.
--------------------------------------------------------------------------------

data Put a

data S a where
    X :: S ('Const Int ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)
    Y :: S ((('Const Int ':-> 'Const Int) ':-> 'Const Int) ':-> 'Const Int)
    Z :: S (('Const Int ':-> ('Const Int ':-> 'Const Int)) ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"
    renderSym (Y) = "Y"
    renderSym (Z) = "Z"

type B' a = Beta S ('None :: Qualifier (Put *)) a
type B  a = B' ('Const a)

--------------------------------------------------------------------------------

x, xs :: B Int -> (B Int -> B Int) -> B Int
x  = \a -> \f -> Sym X :$ Spine a :$ (lam (\v -> Spine (f v)))
xs = undefined --smartSym' X

y, ys :: ((B Int -> B Int) -> B Int) -> B Int
y  = \f -> Sym Y :$ lam (\(v :: B' ('Const Int ':-> 'Const Int)) -> Spine (f (\b -> v :$ (Spine b))))
ys = undefined --smartSym' Y

z, zs :: (B Int -> (B Int -> B Int)) -> B Int
z  = \f -> Sym Z :$ lam (\b1 -> (lam (\b2 -> Spine (f b1 b2))))
zs = undefined --smartSym' Z

--------------------------------------------------------------------------------

xp, yp, zp :: B Int
xp = x (Var 0) (\b -> b)
yp = y (\f -> f (Var 0))
zp = z (\v -> (\_ -> v))

--------------------------------------------------------------------------------
-- Fin.
