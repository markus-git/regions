{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Language.Diorite.Syntax
    (
    -- * Signatures.
      Put(..)
    , Signature(..)
    , SigRep(..)
    , Sig(..)
    , witSig
    -- * Abstract syntax trees.
    , Name
    , Place
    , Region
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    , Sym(..)
    , lam
    -- * "Smart" constructors.
    , SmartBeta
    , SmartEta
    , SmartSig
    , SmartSym
    , smartSym'
    -- * Open symbol domains.
    , Empty
    , (:+:)(..)
    , Project(..)
    , (:<:)(..)
    , smartSym
    -- * Utilities.
    , Ex(..)
    , liftE
    ) where

-- Related stuff:
--   https://emilaxelsson.github.io/documents/axelsson2012generic.pdf

import Data.Constraint (Dict(..))
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
  -- todo: 'Typeable' feels arbitrary here but is needed to look up variables.

-- | Valid symbol signatures.
class Sig sig where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance Sig sig => Sig ('Put ':=> sig) where
    signature = SigPred signature

-- | Witness ...
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred a)   | Dict <- witSig a = Dict

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
  -- todo: (:#) :: ... Puts r p => sym ('Put r ':=> sig) -> Place p -> sym sig
  --       class Puts r p | p -> r where locate :: Place p -> Dict r

data Eta sym (sig :: Signature *) where
    (:\)  :: Sig a => Name -> Eta sym sig -> Eta sym (a ':-> sig)
    (:\\) :: Place -> Eta sym sig -> Eta sym ('Put ':=> sig)
    Spine :: Beta sym ('Const a) -> Eta sym ('Const a)
  -- todo: (:\\) :: ... Place p -> sym sig -> sym ('Put r ':=> sig)

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
-- ** "Smart" constructors.
--------------------------------------------------------------------------------

-- | Maps a symbol to its corresponding "smart" constructor.
type family SmartBeta (sym :: Signature * -> *) (sig :: Signature *)
type instance SmartBeta sym ('Const a)      = Beta sym ('Const a)
type instance SmartBeta sym (a ':-> sig)    = SmartEta sym a -> SmartBeta sym sig
-- type instance SmartBeta sym ('Put ':=> sig) = ... => SmartBeta sym sig

-- | Maps a function to its corresponding "
type family SmartEta (sym :: Signature * -> *) (sig :: Signature *)
type instance SmartEta sym ('Const a)   = Beta sym ('Const a)
type instance SmartEta sym (a ':-> sig) = Beta sym a -> SmartEta sym sig

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
smartSym' :: forall sym sig f
    .  ( Sig sig
       , f   ~ SmartBeta sym sig
       , sig ~ SmartSig f
       , sym ~ SmartSym f
       )
    => sym sig -> f
smartSym' sym = smartBeta (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall a . SigRep a -> Beta sym a -> SmartBeta sym a
    smartBeta (SigConst)      ast = ast
    smartBeta (SigPart a sig) ast = \f -> smartBeta sig (ast :$ smartEta a f)
    smartBeta (SigPred _)     _   = undefined

    smartEta :: forall a . SigRep a -> SmartEta sym a -> Eta sym a
    smartEta (SigConst)      f = Spine f
    smartEta (SigPart a sig) f | Dict <- witSig a = lam (smartEta sig . f)
    smartEta (SigPred _)     _ = undefined

--------------------------------------------------------------------------------
-- * Open symbol domains.
--------------------------------------------------------------------------------

-- | Empty symbol type.
data Empty :: * -> *

-- | Direct sum of two symbol domains.
data (sym1 :+: sym2) sig
  where
    InjL :: sym1 a -> (sym1 :+: sym2) a
    InjR :: sym2 a -> (sym1 :+: sym2) a
  deriving (Functor, Foldable, Traversable)

infixr :+:

instance (Sym sym1, Sym sym2) => Sym (sym1 :+: sym2)
  where
    symbol (InjL s) = symbol s
    symbol (InjR s) = symbol s

-- | Partial symbol projection.
class Project sub sup where
    prj :: sup a -> Maybe (sub a)

instance Project sub sup => Project sub (Beta sup) where
    prj (Sym s) = prj s
    prj _       = Nothing

instance {-# OVERLAPS #-} Project sym sym where
    prj = Just

instance {-# OVERLAPS #-} Project sym1 (sym1 :+: sym2) where
    prj (InjL a) = Just a
    prj _        = Nothing

instance {-# OVERLAPS #-} Project sym1 sym3 => Project sym1 (sym2 :+: sym3) where
    prj (InjR a) = prj a
    prj _        = Nothing

-- | Symbol injection.
class Project sub sup => sub :<: sup where
    inj :: sub a -> sup a

instance {-# OVERLAPS #-} (sub :<: sup) => (sub :<: Beta sup) where
    inj = Sym . inj

instance {-# OVERLAPS #-} (sym :<: sym) where
    inj = id

instance {-# OVERLAPS #-} (sym1 :<: (sym1 :+: sym2)) where
    inj = InjL

instance {-# OVERLAPS #-} (sym1 :<: sym3) => (sym1 :<: (sym2 :+: sym3)) where
    inj = InjR . inj

-- | Make a "smart" constructor for a symbol.
smartSym :: forall sup sub sig f
    .  ( Sig sig
       , f   ~ SmartBeta sup sig
       , sig ~ SmartSig f
       , sup ~ SmartSym f
       , sub :<: sup
       )
    => sub sig -> f
smartSym = smartSym' . inj

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
