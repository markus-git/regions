{-# OPTIONS_GHC -Wall #-}

module SmartSymQ where

import Language.Diorite.Signatures (Signature(..), Qualifier(..))
import Language.Diorite.Syntax
import Language.Diorite.Interpretation
import qualified Language.Diorite.Signatures as E

import Data.Typeable (Typeable)
--import Data.Proxy (Proxy(..))
--import Data.Type.Equality ((:~:)(..))

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

--------------------------------------------------------------------------------

x, xs :: forall k (r1 :: k) (r2 :: k) . (Typeable k, Typeable r1, Typeable r2) => P r1 -> (P r2 -> B (Put r2 ':. 'None) Int) -> B (Put r1 ':. 'None) Int
x  = \r1 -> \f -> Sym X :# r1 :$ (elam (\r2 -> Spine (f r2)))
xs = smartSym' E.ext X

y, ys :: forall k (r :: k) . (Typeable k, Typeable r) => ((P r -> B (Put r ':. 'None) Int) -> B 'None Int) -> B 'None Int
y  = \f -> Sym Y :$ lam (\g -> Spine (f (\r -> g :# r)))
ys = smartSym' E.ext Y

z, zs :: forall k (r1 :: k) (r2 :: k) . (Typeable k, Typeable r1, Typeable r2) => (P r1 -> P r2 -> B (Put r2 ':. Put r1 ':. 'None) Int) -> B 'None Int
z  = \f -> Sym Z :$ elam (\(r1 :: P r1) -> elam (\(r2 :: P r2) -> Spine (f r1 r2)))
zs = smartSym' E.ext Z

--------------------------------------------------------------------------------

data R1
data R2

xp :: B (Put R1 ':. 'None) Int
xp = xs (Ev 0) (\r1 -> (Var 0 :: B' 'None (Put R1 ':=> 'Const Int)) :# r1)

yp :: B 'None Int
yp = ys (\(f :: P R2 -> B (Put R2 ':. 'None) Int) -> (\_ -> Var 0) (f (Ev 0)))

zp :: B 'None Int
zp = zs (\(r1 :: P R1) (r2 :: P R2) -> Var 0 :# r1 :# r2)

--------------------------------------------------------------------------------
-- Fin.
