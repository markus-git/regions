{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Language.Diorite.Syntax
    (
    -- * Signatures.
      Signature(..)
    , Result
    , SigRep(..)
    , Sig(..)
    , testSig
    , witSig
    , witTypeable
    -- * Qualifiers.
    , Qualifier(..)
    , Both
    , Minus
    , QualRep(..)
    , Qual(..)
    , (:-)(..)
    , union
    , remove
    -- * Abstract syntax trees.
    , Name
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    , Sym(..)
    , lam
    -- * "Smart" constructors.
    , SmartFun
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
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)

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

--------------------------------------------------------------------------------
-- ** Rep. of a valid signature.

-- | Witness of a symbol signature.
data SigRep (sig :: Signature p *) where
    SigConst :: Typeable a => SigRep ('Const a)
    SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Typeable p => Proxy p -> SigRep sig -> SigRep (p ':=> sig)

-- | Valid symbol signatures.
class Sig (sig :: Signature p *) where
    signature :: SigRep sig

instance Typeable a => Sig ('Const a) where
    signature = SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    signature = SigPart signature signature

instance (Typeable p, Sig sig) => Sig (p ':=> sig) where
    signature = SigPred Proxy signature

-- | ...
testSig :: forall (a :: Signature p *) (b :: Signature p *) . SigRep a -> SigRep b -> Maybe (a :~: b)
testSig x@(SigConst) y@(SigConst)
    | Just Refl <- eq x y = Just Refl
  where
    eq :: forall x y . (Typeable x, Typeable y) => SigRep ('Const x) -> SigRep ('Const y) -> Maybe (x :~: y)
    eq _ _ = eqT
testSig (SigPart a1 b1) (SigPart a2 b2)
    | Just Refl <- testSig a1 a2, Just Refl <- testSig b1 b2 = Just Refl
testSig (SigPred (_ :: Proxy x) a1) (SigPred (_ :: Proxy y) a2)
    | Just (Refl :: x :~: y) <- eqT, Just Refl <- testSig a1 a2 = Just Refl
testSig _ _ = Nothing
-- todo: Why oh why can't I give 'x' a type 'Const x1'?

-- | Any witness of a symbol signature is a valid symbol signature.
witSig :: SigRep a -> Dict (Sig a)
witSig (SigConst)    = Dict
witSig (SigPart a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (SigPred _ a) | Dict <- witSig a = Dict

-- | Any witness of a constant symbol signature is typeable.
witTypeable :: SigRep ('Const a) -> Dict (Typeable a)
witTypeable (SigConst) = Dict

--------------------------------------------------------------------------------
-- * Qualifiers.
--------------------------------------------------------------------------------

-- | Collection of predicates.
data Qualifier p = p :. Qualifier p | None

infixr 2 :.

-- | Joins the predicates from two sets of qualifiers.
type family Both qs ps where
    Both ('None)    ps = ps
    Both (q ':. qs) ps = q ':. Both qs ps
-- todo: Could remove duplicates with '~'.

-- | Delete a predicate from a set of qualifiers.
type family Minus qs q where
    Minus ('None)    _ = 'None
    Minus (q ':. qs) q = Minus qs q
    Minus (p ':. qs) q = p ':. Minus qs q

--------------------------------------------------------------------------------
-- ** Rep. of a valid qualifier.

-- | Witness of a symbol qualifier.
data QualRep (qs :: Qualifier p) where
    QualNone :: QualRep ('None)
    QualPred :: Proxy p -> QualRep qs -> QualRep (p ':. qs)
-- todo: Swap 'Proxy' for 'Dict'?

-- | Valid symbol qualifiers.
class Qual (qs :: Qualifier p) where
    qualifier :: QualRep qs

instance Qual ('None) where
    qualifier = QualNone

instance Qual qs => Qual (p ':. qs) where
    qualifier = QualPred Proxy qualifier

-- | ...
class qs :- q where
    entails :: QualRep qs -> Proxy q

instance (q ':. qs) :- q where
    entails (QualPred p _) = p

instance (qs :- q) => (p ':. qs) :- q where
    entails (QualPred _ qs) = entails qs

--------------------------------------------------------------------------------

-- | Implementation of 'Both'.
class Union qs ps where
    union :: QualRep qs -> QualRep ps -> QualRep (Both qs ps)

instance Union 'None ps where
    union (QualNone) ps = ps

instance {-# OVERLAPS #-} Union qs ps => Union (q ':. qs) ps where
    union (QualPred q qs) ps = QualPred q (union qs ps)

-- | Implementation of 'Minus'.
class Remove qs q where
    remove :: QualRep qs -> Proxy q -> QualRep (Minus qs q)

instance Remove 'None q where
    remove QualNone Proxy = QualNone

instance {-# OVERLAPS #-} Remove qs q => Remove (q ':. qs) q where
    remove (QualPred _ qs) q = remove qs q

instance {-# OVERLAPPABLE #-} (Minus (p ':. qs) q ~ (p ':. Minus qs q), Remove qs q) => Remove (p ':. qs) q where
    remove (QualPred p qs) q = QualPred p (remove qs q)

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym (qs :: Qualifier p) (sig :: Signature p *) where
    -- ^ Variable.
    Var   :: Sig sig => Name -> Beta sym qs sig
    -- ^ Symbol.
    Sym   :: sym sig -> Beta sym 'None sig
    -- ^ Application.
    (:$)  :: Beta sym qs (a ':-> sig) -> Eta sym ps a -> Beta sym (Both qs ps) sig
    -- ^ Evidence-application.
    (:#)  :: Beta sym qs (p ':=> sig) -> Name -> Beta sym (p ':. qs) sig

data Eta sym (qs :: Qualifier p) (sig :: Signature p *) where
    -- ^ Body.
    Spine :: Beta sym qs ('Const a) -> Eta sym qs ('Const a)
    -- ^ Abstraction.
    (:\)  :: Sig a => Name -> Eta sym qs sig -> Eta sym qs (a ':-> sig)
    -- ^ Evidence-abstraction.
    (:\\) :: (Qual qs, qs :- p) => Name -> Eta sym qs sig -> Eta sym (Minus qs p) (p ':=> sig)

infixl 1 :$, :#
infixr 9 :\, :\\

-- | Generic AST, parameterized by a symbol domain.
type AST sym qs sig = Beta sym qs sig

-- | Fully applied AST (constant value).
type ASTF sym qs sig = Beta sym qs ('Const sig)

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

--------------------------------------------------------------------------------
-- ** ...

-- | Get the highest name bound for 'Eta' node.
maxLamEta :: Eta sym qs a -> Name
maxLamEta (n :\ _)  = n
maxLamEta (_ :\\ e) = maxLamEta e
maxLamEta (Spine b) = maxLamBeta b
  where
    maxLamBeta :: Beta sym qs a -> Name
    maxLamBeta (beta :$ eta) = maxLamBeta beta `Prelude.max` maxLamEta eta
    maxLamBeta (beta :# _)   = maxLamBeta beta
    maxLamBeta _             = 0

-- | Interface for variable binding.
lam :: Sig a => (Beta sym qs a -> Eta sym qs b) -> Eta sym qs (a ':-> b)
lam f = v :\ body
  where
    v    = maxLamEta body + 1
    body = f $ Var v

--------------------------------------------------------------------------------
-- ** "Smart" constructors.

-- | Map a symbol to its corresponding "smart" constructor.
type family SmartFun (sym :: Signature p * -> *) (sig :: Signature p *) where
    SmartFun sym ('Const a) = Beta sym 'None ('Const a)
    SmartFun sym (a ':-> b) = SmartFun sym a -> SmartFun sym b
--  SmartFun sym (p ':=> a) = p => SmartFun sym a

-- | Reconstruct a symbol's signature.
type family SmartSig f :: Signature p * where
    SmartSig (AST s q a) = a
    SmartSig (a -> f)    = SmartSig a ':-> SmartSig f
--  SmartSig (p => f)    = SmartSig f

-- | Fetch the symbol of a "smart" constructor.
type family SmartSym f :: Signature p * -> * where
    SmartSym (AST s q a) = s
    SmartSym (a -> f)    = SmartSym f
--  SmartSym (p => f)    = SmartSym f

-- | Make a "smart" constructor for a symbol.
smartSym' :: forall sym sig f
    .  ( Sig sig
       , f   ~ SmartFun sym sig
       , sig ~ SmartSig f
       , sym ~ SmartSym f
       )
    => sym sig -> f
smartSym' sym = smartBeta (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall a . SigRep a -> Beta sym 'None a -> SmartFun sym a
    smartBeta (SigConst)    ast = ast
    smartBeta (SigPart a b) ast = \f -> smartBeta b (ast :$ smartEta a f)
    smartBeta (SigPred _ _) _   = error "todo:smartSym'"

    smartEta :: forall a . SigRep a -> SmartFun sym a -> Eta sym 'None a
    smartEta (SigConst)    f = Spine f
    smartEta (SigPart a b) f = withDict (witSig a) (lam (smartEta b . f . smartBeta a))
    smartEta (SigPred _ _) _ = error "todo:smartSym'"

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

instance Project sub sup => Project sub (Beta sup qs) where
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
       , f   ~ SmartFun sup sig
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
