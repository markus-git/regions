{-# OPTIONS_GHC -Wall #-}

-- Related stuff:
--   https://github.com/Feldspar/feldspar-language
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

module Language.Diorite.Syntax
    ( Put(..), Signature(..), Name, Place, Beta(..), Eta(..)
    -- 
    , Render(..)
    , renderBeta, renderEta
    --
    , Prim, Region, SigRep(..), Sig(..), Sym(..)
    , eqST
    --
    , Ex(..)
    , liftE
    ) where

import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)

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
    (:$) :: Beta sym (sig ':-> a) -> Eta sym sig -> Beta sym a
    (:#) :: Beta sym ('Put ':=> sig) -> Place -> Beta sym sig

data Eta sym (sig :: Signature *) where
    Lam   :: Name -> Eta sym a -> Eta sym (sig ':-> a)
    ELam  :: Place -> Eta sym sig -> Eta sym ('Put ':=> sig)
    Spine :: Beta sym ('Const sig) -> Eta sym ('Const sig)

infixl 1 :$, :#

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
    -- ...

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
renderEta (Lam n e)  = "(\\" ++ show n ++ ". " ++ renderEta e ++ ")"
renderEta (ELam p e) = "(/\\" ++ show p ++ ". " ++ renderEta e ++ ")"
renderEta (Spine b)  = renderBeta [] b

instance Render sym => Show (Beta sym a) where
    show = renderBeta []

instance Render sym => Show (Eta sym a) where
    show = renderEta

--------------------------------------------------------------------------------
-- ** Type/Signature witness.
--------------------------------------------------------------------------------

-- | Labelling of primitive types.
class (Eq a, Show a, Typeable a) => Prim a

-- | Name of a region, associated with one or more places.
type Region = Name

-- | Witness of a symbol signature.
data SigRep (sig :: Signature *) where
    SigConst :: Prim a => SigRep ('Const a)
    SigPart  :: Region -> SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Region -> SigRep sig -> SigRep ('Put ':=> sig)
  -- todo: added 'SigRep a' to 'SigPart' since arguments can be extended with
  -- evidence as well, might be a smarter way of doing it.

-- | Extract a witness of equality of two signatures' types.
eqST :: forall sig sig' . SigRep sig -> SigRep sig' -> Maybe (sig :~: sig')
eqST (SigConst) (SigConst)
    | Just Refl <- eqT :: Maybe (sig :~: sig') = Just Refl
eqST (SigPart _ a sig) (SigPart _ a' sig')
    | Just Refl <- eqST a a', Just Refl <- eqST sig sig' = Just Refl
eqST (SigPred _ sig) (SigPred _ sig')
    | Just Refl <- eqST sig sig' = Just Refl
eqST _ _ = Nothing

-- | Valid symbol signatures.
class Sig sig where
    represent :: SigRep sig
  -- todo: not sure what to do with the regions.

instance Prim a => Sig ('Const a) where
    represent = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    represent = SigPart undefined represent represent

instance Sig sig => Sig ('Put ':=> sig) where
    represent = SigPred undefined represent

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

--------------------------------------------------------------------------------
-- ** Utils.
--------------------------------------------------------------------------------

-- | Existential quantification.
data Ex e where
    Ex :: e a -> Ex e

liftE :: (forall a . e a -> b) -> Ex e -> b
liftE f (Ex a) = f a

--------------------------------------------------------------------------------
-- Fin.
