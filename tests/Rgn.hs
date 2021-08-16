{-# OPTIONS_GHC -Wall #-}

module Rgn where

import Language.Diorite.Signatures
--import qualified Language.Diorite.Signatures as S
import Language.Diorite.Qualifiers
import Language.Diorite.Syntax
import Language.Diorite.Decoration
import Language.Diorite.Interpretation
import qualified Language.Diorite.Region.Annotate as A

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

data D a where
    X :: Int -> D ('Const Int)
    Y :: D ('Const Int ':-> 'Const Int)
    Z :: D ('Const Int ':-> 'Const Int ':-> 'Const Int)

instance Sym D where
    symbol (X _) = signature
    symbol (Y)   = signature
    symbol (Z)   = signature

instance Render D where
    renderSym (X i) = show i
    renderSym (Y)   = "-"
    renderSym (Z)   = "+"

type B :: * -> *
type B a = Beta D ('None :: Qualifier (A.Put *)) ('Const a)

--------------------------------------------------------------------------------

int :: Int -> B Int
int = smartSym' . X

neg :: B Int -> B Int
neg = smartSym' Y

add :: B Int -> B Int -> B Int
add = smartSym' Z

ex :: B Int
ex = add (int 1) (neg (int 2))

--------------------------------------------------------------------------------

type E a = A.ExLBeta (D :&: A.LBeta) ((A.>=) 'None) ('Const a :: Signature (A.Put *) *)

ann :: B Int -> E Int
ann x = let (b, _) = A.annotate x in b

pr :: E Int -> String
pr (A.ExLBeta b _) = show b

--------------------------------------------------------------------------------
-- Fin.
