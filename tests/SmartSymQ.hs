{-# OPTIONS_GHC -Wall #-}

module SmartSymQ where

import Language.Diorite.Signatures (Signature(..), Qualifier(..))
import Language.Diorite.Syntax
import Language.Diorite.Interpretation

import Data.Typeable (Typeable)

--------------------------------------------------------------------------------
-- * 'smartSym' translations with qualifiers.
--------------------------------------------------------------------------------

data Put a

data S a where
    X :: S (Put r1 ':=> (Put r2 ':=> 'Const Int) ':-> 'Const Int)
    Y :: S (((Put r ':=> 'Const Int) ':-> 'Const Int) ':-> 'Const Int)
    Z :: S ((Put r1 ':=> (Put r2 ':=> 'Const Int)) ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"
    renderSym (Y) = "Y"
    renderSym (Z) = "Z"

type P  r   = Ev (Put r)
type B' q a = Beta S q a
type B  q a = B' q ('Const a)

--------------------------------------------------------------------------------

x, xs :: forall k (r1 :: k) (r2 :: k) . (Typeable k, Typeable r1, Typeable r2)
    => P r1 -> (P r2 -> B (Put r2 ':. 'None) Int) -> B (Put r1 ':. 'None) Int
x  = \r1 -> \f -> Sym X :# r1 :$ (elam (\r2 -> Spine (f r2)))
xs = undefined

y, ys :: forall k (r :: k) . (Typeable k, Typeable r)
    => ((P r -> B (Put r ':. 'None) Int) -> B 'None Int) -> B 'None Int
y  = \f -> Sym Y :$ lam (\g -> Spine (f (\r -> g :# r)))
ys = undefined

z, zs :: forall k (r1 :: k) (r2 :: k) . (Typeable k, Typeable r1, Typeable r2)
    => ((P r1 -> (P r2 -> B (Put r1 ':. Put r2 ':. 'None) Int)) -> B 'None Int)
z  = undefined
zs = undefined

--------------------------------------------------------------------------------

data R1
data R2

xp :: B (Put R1 ':. 'None) Int
xp = x (Ev 0) (\r1 -> (Var 0 :: B' 'None (Put R1 ':=> 'Const Int)) :# r1)

yp :: B 'None Int
yp = y (\(f :: P R2 -> B (Put R2 ':. None) Int) -> Spine (elam (\(r1 :: Ev (Put R1)) -> _)) :# (Ev 0))
  -- y (\f -> (Var 0 :: B' (Put R1 ':. 'None) sig) :$ (Spine (f (Ev 0 :: Ev (Put R1)))))

--------------------------------------------------------------------------------
-- Fin.
