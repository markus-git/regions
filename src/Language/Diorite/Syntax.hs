{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Language.Diorite.Syntax
    (
    -- * Qualifiers.
      Put(..)
    , Place
    , Qualifiers(..)
--    , Both
    -- * Signatures.
    , Signature(..)
    , Result
    , SigRep(..)
    , Sig(..)
    , witSig
    , witTypeable
    -- * Abstract syntax trees.
    , Name
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

--------------------------------------------------------------------------------
-- * Qualifiers.
--------------------------------------------------------------------------------

-- | "Put" predicate, asserts that region 'r' is allocated.
data Put r = Put r

-- | Location names, associated with a "Put" predicate on an 'r'.
type Place r = Int

-- | Collection of predicates of a region-qualified symbol.
data Qualifiers r = Put r :- Qualifiers r | None
  -- todo: Ordering should not important(?).

infixr :-
{-
-- | Joins two collections of qualifiers.
type family Both (ps :: Qualifiers put) (qs :: Qualifiers put) where
    Both ('None)    qs = qs
    Both (p ':- ps) qs = p ':- (Both ps qs)
-}  
--------------------------------------------------------------------------------
-- * Signatures.
--------------------------------------------------------------------------------

-- | Signature of a symbol.
data Signature r a = Const a | Signature r a :-> Signature r a | Put r :=> Signature r a

infixr :->, :=>

-- | Denotational result of a symbol's signature.
type family Result sig where
    Result ('Const a) = a
    Result (a ':-> b) = Result b
    Result (p ':=> a) = Result a
  
-- | Witness of a symbol signature.
data SigRep (sig :: Signature (Put *) *) where
    SigConst :: Typeable a => SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: SigRep sig -> SigRep ('Put r ':=> sig)
  -- todo: 'Typeable' feels arbitrary here but is needed to look up variables.

-- | Valid symbol signatures.
class Sig (sig :: Signature (Put *) *) where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance Sig sig => Sig ('Put r ':=> sig) where
    signature = SigPred signature

-- | Any witness of a symbol signature is a valid symbol signature.
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred a)   | Dict <- witSig a = Dict

-- | ...
witTypeable :: SigRep ('Const a) -> Dict (Typeable a)
witTypeable (SigConst) = Dict

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym rs (sig :: Signature (Put *) *) where
    Var  :: Sig sig => Name -> Beta sym rs sig
    Sym  :: sym sig -> Beta sym 'None sig
    (:$) :: Beta sym rs (a ':-> sig) -> Eta sym rs a -> Beta sym rs sig
    (:#) :: Beta sym rs ('Put r ':=> sig) -> Place r -> Beta sym ('Put r ':- rs) sig

data Eta sym rs (sig :: Signature (Put *) *) where
    Spine :: Beta sym rs ('Const a) -> Eta sym rs ('Const a)
    (:\)  :: Sig a => Name -> Eta sym rs sig -> Eta sym rs (a ':-> sig)
    (:\\) :: Place r -> Eta sym ('Put r ':- rs) sig -> Eta sym rs ('Put r ':=> sig)

infixl 1 :$, :#

infixr :\, :\\

-- | Generic AST, parameterized by a symbol domain.
type AST sym sig = Beta sym 'None sig

-- | Fully applied AST (constant value).
type ASTF sym sig = Beta sym 'None ('Const sig)

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

instance Sym SigRep where
    symbol = id

--------------------------------------------------------------------------------

-- | Get the highest name bound for 'Eta' node.
maxLamEta :: Eta sym rs a -> Name
maxLamEta (n :\ _)  = n
maxLamEta (_ :\\ e) = maxLamEta e
maxLamEta (Spine b) = maxLamBeta b

-- | Get the highest name bound for 'Beta' node.
maxLamBeta :: Beta sym rs a -> Name
maxLamBeta (b :$ e) = maxLamBeta b `Prelude.max` maxLamEta e
maxLamBeta (b :# _) = maxLamBeta b
maxLamBeta _        = 0

-- | Interface for variable binding.
lam :: Sig a => (Beta sym rs a -> Eta sym rs b) -> Eta sym rs (a ':-> b)
lam f = v :\ body
  where
    v    = maxLamEta body + 1
    body = f $ Var v

--------------------------------------------------------------------------------
-- ** "Smart" constructors.
--------------------------------------------------------------------------------

-- | Maps a symbol to its corresponding "smart" constructor.
type family SmartBeta (sym :: Signature (Put *) * -> *) (sig :: Signature (Put *) *)
type instance SmartBeta sym ('Const a)      = ASTF sym a
type instance SmartBeta sym (a ':-> sig)    = SmartEta sym a -> SmartBeta sym sig

-- | Maps a function to its corresponding "
type family SmartEta (sym :: Signature (Put *) * -> *) (sig :: Signature (Put *) *)
type instance SmartEta sym ('Const a)   = ASTF sym a
type instance SmartEta sym (a ':-> sig) = AST sym a -> SmartEta sym sig

-- | Maps a "smart" constructor to its corresponding symbol's signature.
type family SmartSig f :: Signature (Put *) *
type instance SmartSig (AST sym a) = a
type instance SmartSig (a -> f)    = SmartSig a ':-> SmartSig f

-- | Returns the resulting 'sym' of a "smart" constructor.
type family SmartSym f :: Signature (Put *) * -> *
type instance SmartSym (AST sym a) = sym
type instance SmartSym (a -> f)    = SmartSym f

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
    smartBeta :: forall a . SigRep a -> Beta sym 'None a -> SmartBeta sym a
    smartBeta (SigConst)      ast = ast
    smartBeta (SigPart a sig) ast = \f -> smartBeta sig (ast :$ smartEta a f)
    smartBeta (SigPred _)     _   = error "Qualifiers in source exp."

    smartEta :: forall a . SigRep a -> SmartEta sym a -> Eta sym 'None a
    smartEta (SigConst)      f = Spine f
    smartEta (SigPart a sig) f = withDict (witSig a) (lam (smartEta sig . f))
    smartEta (SigPred _)     _ = error "Qualifiers in source exp."
  -- note/todo: No qualifiers in source expressions, for now at least.

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

instance Project sub sup => Project sub (Beta sup rs) where
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

instance {-# OVERLAPS #-} (sub :<: sup) => (sub :<: Beta sup 'None) where
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
