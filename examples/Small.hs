-- {-# OPTIONS_GHC -Wall #-}

module Small where

import Language.Diorite.Syntax
import Language.Diorite.Interpretation
--import Language.Diorite.Region

import Data.List (partition)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, eqT)
import Data.Type.Equality ((:~:)(..), TestEquality(..))
import Data.Constraint (Dict(..))

import Control.Monad.State (State)
import qualified Control.Monad.State as S (get, put, evalState)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Source language.
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

int   = smartSym' . Int
add   = smartSym' Add
share = smartSym' Let

--------------------------------------------------------------------------------

data Rgn a where
    


--------------------------------------------------------------------------------
-- Fin.
