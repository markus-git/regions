module Language.Diorite.Interpretation
    ( Render(..)
    , renderBeta
    , renderEta
    --
    , Denotation
    ) where

import Language.Diorite.Syntax (Name, Put(..), Signature(..), Beta(..), Eta(..))

--------------------------------------------------------------------------------
-- * Rendering.
--------------------------------------------------------------------------------

-- | Render a symbol as concrete syntax.
class Render sym where
    renderSym  :: sym sig -> String
    renderArgs :: [String] -> sym sig -> String
    renderArgs []   s = renderSym s
    renderArgs args s = "(" ++ unwords (renderSym s : args) ++ ")"

-- | Render a 'Beta' tree as concrete syntax.
renderBeta :: Render sym => [String] -> Beta sym a -> String
renderBeta _    (Var n)  = show n
renderBeta args (Sym s)  = renderArgs args s
renderBeta args (s :$ e) = renderBeta (renderEta e : args) s
renderBeta args (s :# p) = renderBeta (("<" ++ show p ++ ">") : args) s

-- | Render an 'Eta' spine as concrete syntax.
renderEta :: Render sym => Eta sym a -> String
renderEta (n :\ e)  = "(\\" ++ show n ++ ". " ++ renderEta e ++ ")"
renderEta (p :\\ e) = "(/\\" ++ show p ++ ". " ++ renderEta e ++ ")"
renderEta (Spine b) = renderBeta [] b

instance Render sym => Show (Beta sym a) where
    show = renderBeta []

instance Render sym => Show (Eta sym a) where
    show = renderEta

--------------------------------------------------------------------------------
-- * Evaluation.
--------------------------------------------------------------------------------

-- | Denotation of a symbol's signature.
type family Denotation sig where
    Denotation ('Const a)    = a
    Denotation (a ':-> b)    = Denotation a -> Denotation b
    Denotation ('Put ':=> a) = Name -> Denotation a

-- todo.

--------------------------------------------------------------------------------
