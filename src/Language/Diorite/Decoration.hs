{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Decoration
    ( (:&:)(..)
    ) where

import Language.Diorite.Syntax (Sym(..))
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Traversal (Result)

--------------------------------------------------------------------------------
-- * Decorated symbols.
--------------------------------------------------------------------------------

-- | Decorating symbols with additional information.
data (sym :&: info) sig where
    (:&:) :: { _sym   :: sym sig
             , _decor :: info (Result sig)
             }
          -> (sym :&: info) sig

instance Render sym => Render (sym :&: info) where
    renderSym     = renderSym . _sym
    renderArgs as = renderArgs as . _sym

instance Sym sym => Sym (sym :&: info) where
    symbol = symbol . _sym

--------------------------------------------------------------------------------
-- ** ...
--------------------------------------------------------------------------------

-- todo: Smart functions and stuff.

--------------------------------------------------------------------------------
-- Fin.
