{-# OPTIONS_GHC -Wall #-}

module Annotate where

import Language.Diorite.Syntax
import Language.Diorite.Interpretation
import Language.Diorite.Region.Annotation (Put(..))
import qualified Language.Diorite.Region.Annotation as A

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

data S a where
    X :: S ('Put a ':=> 'Const Int)
--    Y :: S (Put a ':=> 'Const Int ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"
--    renderSym (Y) = "Y"

type B qs a = Beta S qs ('Const a)

--------------------------------------------------------------------------------

--x :: 

--------------------------------------------------------------------------------
-- Fin.
