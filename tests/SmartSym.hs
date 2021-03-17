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
    Z :: S (('Const Int ':->  ('Const Int ':-> 'Const Int)) ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"
    renderSym (Y) = "Y"
    renderSym (Z) = "Z"

type B a = Beta S ('None :: Qualifier (Put *)) ('Const a)

--------------------------------------------------------------------------------

x, xs :: B Int -> (B Int -> B Int) -> B Int
x  = \a -> \f -> Sym X :$ Spine a :$ (lam (\v -> Spine (f v)))
xs = smartSym' X

y, ys :: ((B Int -> B Int) -> B Int) -> B Int
y  = \f -> Sym Y :$ lam (\v -> Spine (f (\b -> v :$ (Spine b))))
ys = smartSym' Y

z, zs :: (B Int -> (B Int -> B Int)) -> B Int
z  = \f -> Sym Z :$ lam (\b1 -> (lam (\b2 -> Spine (f b1 b2))))
zs = smartSym' Z

--------------------------------------------------------------------------------

yt :: B Int
yt = ys (\f -> f var)
  where
    var :: B Int
    var = Var 9

--------------------------------------------------------------------------------
-- Fin.
