{-# OPTIONS_GHC -Wall #-}

-- Related stuff:
--   https://github.com/Feldspar/feldspar-language
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

module Language.Diorite.Syntax
    ( Put(..)
    , Signature(..)
    , Name
    , Place
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    -- 
    , Render(..)
    , renderBeta
    , renderEta
    --
    , Region
    , SigRep(..)
    , Sig(..)
    , Sym(..)
    --
    , Empty
    , Ex(..)
    , liftE
    ) where

--import Data.Type.Equality ((:~:)(..))
--import Data.Typeable (Typeable, eqT)

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | \"Put\" predicate, asserts that a region is allocated.
data Put = Put

-- | Signature of a symbol.
data Signature a = Const a | Signature a :-> Signature a | Put :=> Signature a

infixr :->, :=>

-- | Variable names.
type Name = Int

-- | Place names.
type Place = Name

-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym (sig :: Signature *) where
    Var  :: Name -> Beta sym sig
    Sym  :: sym sig -> Beta sym sig
    (:$) :: Beta sym (a ':-> sig) -> Eta sym a -> Beta sym sig
    (:#) :: Beta sym ('Put ':=> sig) -> Place -> Beta sym sig

data Eta sym (sig :: Signature *) where
    (:\)  :: Name -> Eta sym sig -> Eta sym (a ':-> sig)
    (:\\) :: Place -> Eta sym sig -> Eta sym ('Put ':=> sig)
    Spine :: Beta sym ('Const sig) -> Eta sym ('Const sig)

infixl 1 :$, :#

infixr :\, :\\

-- | Generic AST, parameterized by a symbol domain.
type AST sym sig = Beta sym sig

-- | Fully applied AST (constant value).
type ASTF sym sig = Beta sym ('Const sig)

--------------------------------------------------------------------------------
-- ** Evaluation.
--------------------------------------------------------------------------------

type family Denotation sig where
    Denotation ('Const a)    = a
    Denotation (a ':-> b)    = Denotation a -> Denotation b
    Denotation ('Put ':=> a) = Name -> Denotation a

-- todo.

--------------------------------------------------------------------------------
-- ** Rendering.
--------------------------------------------------------------------------------

-- | Render a symbol as concrete syntax.
class Render sym where
    renderSym  :: sym sig -> String
    renderArgs :: [String] -> sym sig -> String
    renderArgs []   s = renderSym s
    renderArgs args s = "(" ++ unwords (renderSym s : args) ++ ")"

-- | Render a \"Beta\" tree as concrete syntax.
renderBeta :: Render sym => [String] -> Beta sym a -> String
renderBeta _    (Var n)  = show n
renderBeta args (Sym s)  = renderArgs args s
renderBeta args (s :$ e) = renderBeta (renderEta e : args) s
renderBeta args (s :# p) = renderBeta (("<" ++ show p ++ ">") : args) s

-- | Render an \"Eta\" spine as concrete syntax.
renderEta :: Render sym => Eta sym a -> String
renderEta (n :\ e)  = "(\\" ++ show n ++ ". " ++ renderEta e ++ ")"
renderEta (p :\\ e) = "(/\\" ++ show p ++ ". " ++ renderEta e ++ ")"
renderEta (Spine b) = renderBeta [] b

instance Render sym => Show (Beta sym a) where
    show = renderBeta []

instance Render sym => Show (Eta sym a) where
    show = renderEta

--------------------------------------------------------------------------------
-- ** Type/Signature witness.
--------------------------------------------------------------------------------

-- | Name of a region, associated with one or more places.
type Region = Name

-- | Witness of a symbol signature.
data SigRep (sig :: Signature *) where
    SigConst :: SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: SigRep sig -> SigRep ('Put ':=> sig)

-- | Valid symbol signatures.
class Sig sig where
    signature :: SigRep sig

instance Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance Sig sig => Sig ('Put ':=> sig) where
    signature = SigPred signature

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

--------------------------------------------------------------------------------
-- ** Utils.
--------------------------------------------------------------------------------

-- | Empty symbol type
data Empty :: * -> *

-- | Existential quantification.
data Ex e where
    Ex :: e a -> Ex e

liftE :: (forall a . e a -> b) -> Ex e -> b
liftE f (Ex a) = f a

--------------------------------------------------------------------------------
-- Fin.
