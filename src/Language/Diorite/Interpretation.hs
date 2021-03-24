{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Interpretation
    (
    -- * Rendering.
      Render(..)
    , renderBeta
    , renderEta
    -- * Evaluation.
    , Denotation
    ) where

import Language.Diorite.Signatures (Signature(..))
import Language.Diorite.Syntax (Ev(..), Beta(..), Eta(..), (:+:)(..))

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Rendering.
--------------------------------------------------------------------------------

-- | Render a symbol as concrete syntax.
class Render sym where
    renderSym  :: sym sig -> String
    renderArgs :: [String] -> sym sig -> String
    renderArgs []   s = renderSym s
    renderArgs args s = "(" ++ unwords (renderSym s : args) ++ ")"

instance (Render sym1, Render sym2) => Render (sym1 :+: sym2) where
    renderSym (InjL l) = renderSym l
    renderSym (InjR r) = renderSym r
    renderArgs args (InjL l) = renderArgs args l
    renderArgs args (InjR r) = renderArgs args r

instance Render Ev where
    renderSym (Ev n) = show n

instance Render (A.Const String) where
    renderSym = A.getConst

--------------------------------------------------------------------------------

-- | Render a 'Beta' tree as concrete syntax.
renderBeta :: Render sym => [String] -> Beta sym qs a -> String
renderBeta args (Var n)  = renderArgs args (A.Const ('v' : show n))
renderBeta args (Sym s)  = renderArgs args s
renderBeta args (s :$ e) = renderBeta (renderEta e : args) s
renderBeta args (s :# p) = renderBeta (('r' : renderSym p) : args) s

-- | Render an 'Eta' spine as concrete syntax.
renderEta :: Render sym => Eta sym qs a -> String
renderEta (Spine b) = renderBeta [] b
renderEta (n :\ e)  = "(\\" ++ ('v' : show n) ++ ". " ++ renderEta e ++ ")"
renderEta (p :\\ e) = "(/\\" ++ ('r' : renderSym p) ++ ". " ++ renderEta e ++ ")"

instance Render sym => Show (Beta sym qs a) where
    show = renderBeta []

instance Render sym => Show (Eta sym qs a) where
    show = renderEta

--------------------------------------------------------------------------------
-- * Evaluation.
--------------------------------------------------------------------------------

-- | Denotation of a symbol's signature.
type family Denotation sig where
    Denotation ('Const a) = a
    Denotation (a ':-> b) = Denotation a -> Denotation b
--  Denotation (p ':=> a) = Name -> Denotation a

--------------------------------------------------------------------------------
