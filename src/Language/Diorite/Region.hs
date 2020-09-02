--{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region where

import Language.Diorite.Syntax
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Traversal (Args(..))

import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * Region inference.
--------------------------------------------------------------------------------

-- | Local region-bindings.
data Local sig where
    Local :: Place -> Local sig

instance Render Local where
    renderSym (Local p) = "local " ++ show p

--------------------------------------------------------------------------------

-- | Erasure of any "Put" predicates of a symbol's signature.
type family Erasure a where
    Erasure ('Const a)    = 'Const a
    Erasure (a ':-> b)    = Erasure a ':-> Erasure b
    Erasure ('Put ':=> a) = Erasure a

-- | Witness of equality under "Erasure" of second signature.
newtype sig :~~: sig' = Erased (sig :~: Erasure sig')

infixr :~~:

--------------------------------------------------------------------------------

  
--------------------------------------------------------------------------------
-- Fin.
