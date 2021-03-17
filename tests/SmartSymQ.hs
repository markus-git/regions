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
    X :: S (Put r ':=> 'Const Int)
    Y :: S (((Put r ':=> 'Const Int) ':-> 'Const Int) ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"
    renderSym (Y) = "Y"

type P r = Ev (Put r)
type B q a = Beta S (q :: Qualifier *) ('Const a)

--------------------------------------------------------------------------------

x, xs :: forall r . P r -> B (Put r ':. 'None) Int
x  = undefined
xs = \r -> Sym X :# r

y, ys :: forall k (r :: k) . (Typeable k, Typeable r) => ((P r -> B (Put r ':. 'None) Int) -> B 'None Int) -> B 'None Int
y  = undefined
ys = \f -> Sym Y :$ lam (\v -> Spine (f (\e -> v :# e)))

--------------------------------------------------------------------------------
-- Fin.
