{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Rgn where

import Language.Diorite.Signatures
--import qualified Language.Diorite.Signatures as S
import Language.Diorite.Qualifiers
import Language.Diorite.Syntax
import Language.Diorite.Decoration
import Language.Diorite.Interpretation
import qualified Language.Diorite.Region.Annotation as A
import qualified Language.Diorite.Region.Labels as L

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

data D a where
    X :: Int -> D ('Const Int)
    Y :: D ('Const Int ':-> 'Const Int)
    Z :: D ('Const Int ':-> 'Const Int ':-> 'Const Int)
    --
    A :: D ('Const Int ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)

instance Sym D where
    symbol (X _) = signature
    symbol (Y)   = signature
    symbol (Z)   = signature
    symbol (A)   = signature

instance Render D where
    renderSym (X i) = show i
    renderSym (Y)   = "-"
    renderSym (Z)   = "+"
    renderSym (A)   = "let"

type B :: * -> *
type B a = Beta D ('None :: Qualifier (L.Put *)) ('Const a)

--------------------------------------------------------------------------------

int :: Int -> B Int
int = smartSym' . X

neg :: B Int -> B Int
neg = smartSym' Y

add :: B Int -> B Int -> B Int
add = smartSym' Z

share :: B Int -> (B Int -> B Int) -> B Int
share = smartSym' A

ex1 :: B Int
ex1 = add (int 1) (neg (int 2))

ex2 :: B Int
ex2 = share (int 2) (\x -> add (int 1) x)

--------------------------------------------------------------------------------

type E a = A.EBeta (D :&: A.Ann) ((A.>=) 'None) ('Const @(L.Put *) a)

ann :: B Int -> E Int
ann = A.annotate

pr :: E Int -> IO ()
pr (A.EBeta b _) = putStrLn (show b)

--------------------------------------------------------------------------------
-- Fin.
