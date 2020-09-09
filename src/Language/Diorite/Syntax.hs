{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Syntax
    (
    -- Signatures.
      Put(..)
    , Signature(..)
    , SigRep(..)
    , Sig(..)
    -- Abstract syntax trees.
    , Name
    , Place
    , Region
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    , Sym(..)
    , lam
    -- Open symbol domains.
    , smartSym
    -- Utilities.
    , Empty
    , Ex(..)
    , liftE
    ) where

-- Related stuff:
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

import Data.Typeable (Typeable)

--------------------------------------------------------------------------------
-- * Signatures.
--------------------------------------------------------------------------------

-- | "Put" predicate, asserts that a region is allocated.
data Put = Put
  -- todo: Add phantom region.

-- | Signature of a symbol.
data Signature a = Const a | Signature a :-> Signature a | Put :=> Signature a

infixr :->, :=>

-- | Witness of a symbol signature.
data SigRep (sig :: Signature *) where
    SigConst :: Typeable a => SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: SigRep sig -> SigRep ('Put ':=> sig)
  -- todo: 'Typeable' feels arbitrary here but it is needed for rgn. inference.

-- | Valid symbol signatures.
class Sig sig where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance Sig sig => Sig ('Put ':=> sig) where
    signature = SigPred signature

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Place names.
type Place = Name

-- | Name of a region, associated with one or more places.
type Region = Name

-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym (sig :: Signature *) where
    Var  :: Sig sig => Name -> Beta sym sig
    Sym  :: sym sig -> Beta sym sig
    (:$) :: Beta sym (a ':-> sig) -> Eta sym a -> Beta sym sig
    (:#) :: Beta sym ('Put ':=> sig) -> Place -> Beta sym sig
  -- todo: Have Haskell handle region inference a la "Typing Dynamic Typing"(?).

data Eta sym (sig :: Signature *) where
    (:\)  :: Sig a => Name -> Eta sym sig -> Eta sym (a ':-> sig)
    (:\\) :: Place -> Eta sym sig -> Eta sym ('Put ':=> sig)
    Spine :: Beta sym ('Const a) -> Eta sym ('Const a)

infixl 1 :$, :#

infixr :\, :\\

-- | Generic AST, parameterized by a symbol domain.
type AST sym sig = Beta sym sig

-- | Fully applied AST (constant value).
type ASTF sym sig = Beta sym ('Const sig)

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

instance Sym SigRep where
    symbol = id

-- | Get the highest name bound for 'Eta' node.
maxLamEta :: Eta sym a -> Name
maxLamEta (n :\ _)  = n
maxLamEta (_ :\\ e) = maxLamEta e
maxLamEta (Spine b) = maxLamBeta b

-- | Get the highest name bound for 'Beta' node.
maxLamBeta :: Beta sym a -> Name
maxLamBeta (b :$ e) = maxLamBeta b `Prelude.max` maxLamEta e
maxLamBeta (b :# _) = maxLamBeta b
maxLamBeta _        = 0

-- | Interface for variable binding.
lam :: Sig a => (Beta sym a -> Eta sym b) -> Eta sym (a ':-> b)
lam f = v :\ body
  where
    v    = maxLamEta body + 1
    body = f $ Var v

--------------------------------------------------------------------------------
-- ** Open symbol domains.
--------------------------------------------------------------------------------

-- | Maps a symbol to its corresponding "smart" constructor.
type family SmartBeta (sym :: Signature * -> *) (sig :: Signature *)
type instance SmartBeta sym ('Const a)      = Beta sym ('Const a)
type instance SmartBeta sym (a ':-> sig)    = SmartBeta sym a -> SmartBeta sym sig
-- type instance SmartBeta sym ('Put ':=> sig) = ... => SmartBeta sym sig

-- | Maps a "smart" constructor to its corresponding symbol's signature.
type family SmartSig f :: Signature *
type instance SmartSig (Beta sym a) = a
type instance SmartSig (a -> f)     = SmartSig a ':-> SmartSig f
-- type instance SmartSig (... => f) = 'Put ':=> SmartSig f

-- | Returns the resulting 'sym' of a "smart" constructor.
type family SmartSym f :: Signature * -> *
type instance SmartSym (Beta sym a) = sym
type instance SmartSym (a -> f)     = SmartSym f
-- type instance SmartSym (... => f) = SmartSym f

-- | Make a "smart" constructor for a symbol.
--
-- > smartSym :: sym (Const a :-> (Const a :-> Const b) :-> Const b)
-- >          -> (ASTF sym a -> (ASTF sym a -> ASTF sym b) -> ASTF sym b)
smartSym :: forall sym sig f
    .  ( Sig sig
       , f   ~ SmartBeta sym sig
       , sig ~ SmartSig f
       , sym ~ SmartSym f
       )
    => sym sig -> f
smartSym sym = smartBeta (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall a . SigRep a -> Beta sym a -> SmartBeta sym a
    smartBeta (SigConst)      ast = ast
    smartBeta (SigPart a sig) ast = \f -> smartBeta sig (ast :$ smartEta a f)
  -- smartBeta (SigPred sig) ast = \r -> smartBeta sig (ast :# r)

    smartEta :: forall a . SigRep a -> SmartBeta sym a -> Eta sym a
    smartEta (SigConst)      f = Spine f
    smartEta (SigPart a sig) f = lam (\b -> smartEta sig (f b))
  -- smartEta (SigPred sig) f = ...

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
