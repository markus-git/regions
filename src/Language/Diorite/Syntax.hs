{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Language.Diorite.Syntax
    (
    -- * Signatures.
      Signature(..)
    , Result
    , Pred
    , SigRep(..)
    , Sig(..)
    , witSig
    , witTypeable
    -- * Abstract syntax trees.
    , Name
    , Ev
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

import Data.Constraint (Dict(..), withDict)
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- * Signatures.
--------------------------------------------------------------------------------

-- | Signature of a symbol.
data Signature p a =
         Const a
       | Signature p a :-> Signature p a
       | p :=> Signature p a

infixr 2 :->, :=>

-- | Denotational result of a symbol's signature.
type family Result (sig :: Signature p *) where
    Result ('Const a) = a
    Result (a ':-> b) = Result b
    Result (p ':=> a) = Result a

-- | Predicates associated with a signature.
type family Pred (sig :: Signature p *) :: * where
    Pred (sig :: Signature p *) = p

--------------------------------------------------------------------------------

-- | Witness of a symbol signature.
data SigRep (sig :: Signature p *) where
    SigConst :: Typeable a => SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Proxy p -> SigRep sig -> SigRep (p ':=> sig)

-- | Valid symbol signatures.
class Sig (sig :: Signature p *) where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance Sig sig => Sig (p ':=> sig) where
    signature = SigPred Proxy signature

-- | Any witness of a symbol signature is a valid symbol signature.
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred _ a) | Dict <- witSig a = Dict

-- | Any witness of a constant symbol signature is typeable.
witTypeable :: SigRep ('Const a) -> Dict (Typeable a)
witTypeable (SigConst) = Dict

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Evidence variable names, associated with a predicate 'p'.
type Ev p = Name

-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym (sig :: Signature p *) where
    -- ^ Variable.
    Var   :: Sig sig => Name -> Beta sym sig
    -- ^ Symbol.
    Sym   :: sym sig -> Beta sym sig
    -- ^ Application.
    (:$)  :: Beta sym (a ':-> sig) -> Eta sym a -> Beta sym sig
    -- ^ Evidence-application.
    (:#)  :: Beta sym (p ':=> sig) -> Ev p -> Beta sym sig

data Eta sym (sig :: Signature p *) where
    -- ^ Body.
    Spine :: Beta sym ('Const a) -> Eta sym ('Const a)
    -- ^ Abstraction.
    (:\)  :: Sig a => Name -> Eta sym sig -> Eta sym (a ':-> sig)
    -- ^ Evidence-abstraction.
    (:\\) :: Ev p -> Eta sym sig -> Eta sym (p ':=> sig)

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

--------------------------------------------------------------------------------

-- | Get the highest name bound for 'Eta' node.
maxLamEta :: Eta sym a -> Name
maxLamEta (n :\ _)  = n
maxLamEta (_ :\\ e) = maxLamEta e
maxLamEta (Spine b) = maxLamBeta b
  where
    maxLamBeta :: Beta sym a -> Name
    maxLamBeta (beta :$ eta) = maxLamBeta beta `Prelude.max` maxLamEta eta
    maxLamBeta (beta :# _)   = maxLamBeta beta
    maxLamBeta _             = 0

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
type family SmartBeta (sym :: Signature p * -> *) (sig :: Signature p *) where
    SmartBeta sym ('Const a)   = ASTF sym a
    SmartBeta sym (a ':-> sig) = SmartEta sym a -> SmartBeta sym sig
--  SmartBeta sym (p ':=> sig) = p => SmartBeta sym sig

-- | ...
type family SmartEta (sym :: Signature p * -> *) (sig :: Signature p *) where
    SmartEta sym ('Const a)   = ASTF sym a
    SmartEta sym (a ':-> sig) = AST sym a -> SmartEta sym sig
--  SmartEta sym (p ':=> sig) = p => SmartEta sym sig

-- | Maps a "smart" constructor to its corresponding symbol's signature.
type family SmartSig f :: Signature p * where
    SmartSig (AST sym a) = a
    SmartSig (a -> f)    = SmartSig a ':-> SmartSig f
--  SmartSig (Ev p -> f) = p ':=> SmartSig f

-- | Returns the resulting 'sym' of a "smart" constructor.
type family SmartSym f :: Signature p * -> * where
    SmartSym (AST sym a) = sym
    SmartSym (a -> f)    = SmartSym f
--  SmartSym (p => f)    = SmartSym f

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
    smartBeta (SigPred _ _)   _   = error "todo."

    smartEta :: forall a . SigRep a -> SmartEta sym a -> Eta sym a
    smartEta (SigConst)      f = Spine f
    smartEta (SigPart a sig) f = withDict (witSig a) (lam (smartEta sig . f))
    smartEta (SigPred _ _)   _ = error "todo."

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

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

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
