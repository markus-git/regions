-- {-# OPTIONS_GHC -Wall #-}

module Small where

import Language.Diorite
--import Language.Diorite.Region

import Data.List (partition)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, eqT)
import Data.Type.Equality ((:~:)(..), TestEquality(..))
import Data.Constraint (Dict(..))

import Control.Monad.State (State)
import qualified Control.Monad.State as S (get, put, evalState)

--------------------------------------------------------------------------------
-- * Simple language without qualifiers.
--------------------------------------------------------------------------------

data Prim a where
    Int :: Int -> Prim ('Const Int)
    Add :: Prim ('Const Int ':-> 'Const Int ':-> 'Const Int)
    Let :: Prim ('Const Int ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)

instance Sym Prim where
    symbol (Int _) = signature
    symbol (Add)   = signature
    symbol (Let)   = signature

instance Render Prim where
    renderSym (Int i) = "i" ++ show i
    renderSym (Add)   = "(+)"
    renderSym (Let)   = "let"

type Exp a = ASTF Prim 'None a

int :: Int -> Exp Int
int = smartSym' . Int

add :: Exp Int -> Exp Int -> Exp Int
add = smartSym' Add

share :: Exp Int -> (Exp Int -> Exp Int) -> Exp Int
share = smartSym' Let

example :: Exp Int
example = share (int 2) (\x -> add x x)

--------------------------------------------------------------------------------
-- Fin.
