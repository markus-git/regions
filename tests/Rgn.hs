{-# OPTIONS_GHC -Wall #-}

module Rgn where

import Language.Diorite.Signatures
import Language.Diorite.Syntax
import Language.Diorite.Interpretation
import qualified Language.Diorite.Signatures as S
import qualified Language.Diorite.Region.Annotation as A

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

data SL a where
    SX :: SL ('S.Const Int 'S.:-> 'S.Const Int)
    SY :: SL ('S.Const Int 'S.:-> 'S.Const Int 'S.:-> 'S.Const Int)

instance Render SL where
    renderSym (SX) = "SX"
    renderSym (SY) = "SY"

type BS a = Beta SL 'None ('S.Const a)

--------------------------------------------------------------------------------

data TL a where
    TX :: TL ( 'A.Put r1 'A.:=>
               'A.Put r2 'A.:=>
               'A.Const Int 'A.:^ r1 'A.:->
               'A.Const Int 'A.:^ r2 )
    TY :: TL ( 'A.Put r1 'A.:=>
               'A.Put r2 'A.:=>
               'A.Put r3 'A.:=>
               'A.Const Int 'A.:^ r1 'A.:->
               'A.Const Int 'A.:^ r2 'A.:->
               'A.Const Int 'A.:^ r3 )

instance Render TL where
    renderSym (TX) = "TX"
    renderSym (TY) = "TY"

type BT qs a = Beta () qs ('S.Const a)

--------------------------------------------------------------------------------
-- Fin.
