{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fprint-explicit-foralls #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-} -- hmm..

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
    , Insert
    , Union
    , Remove
    , Element
    , QualRep(..)
    , Qual(..)
    , (:-)(..)
--  , union
--  , remove
    -- * Abstract syntax trees.
    , Name
    , Ev(..)
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    , Sym(..)
    , lam
    , elam
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
--  , smartSym
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

--------------------------------------------------------------------------------

-- | Extract a witness of equality of two constant types.
testConst :: SigRep ('Const a) -> SigRep ('Const b) -> Maybe (a :~: b)
testConst SigConst SigConst = eqT

-- | Extract a witness of equality of two types.
testSig :: SigRep a -> SigRep b -> Maybe (a :~: b)
testSig a1@(SigConst) a2@(SigConst)
    | Just Refl <- testConst a1 a2
    = Just Refl
testSig (SigPart a1 b1) (SigPart a2 b2)
    | Just Refl <- testSig a1 a2
    , Just Refl <- testSig b1 b2
    = Just Refl
testSig (SigPred (_ :: Proxy x) a1) (SigPred (_ :: Proxy y) a2)
    | Just Refl <- eqT :: Maybe (x :~: y)
    , Just Refl <- testSig a1 a2
    = Just Refl
testSig _ _ = Nothing

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
data Qualifier p =
      None
    | p :. Qualifier p

infixr 2 :.

-- | ...
type family Insert q qs where
    Insert q ('None)    = q ':. 'None
    Insert q (q ':. qs) = q ':. qs
    Insert q (a ':. qs) = a ':. Insert q qs
  
-- | Join the predicates from two sets of qualifiers.
type family Union qs ps where
    Union ('None)    ps = ps
    Union (q ':. qs) ps = q ':. Union qs ps
--  Union (q ':. qs) ps = Insert q (Union qs ps)

-- | Delete a predicate from a set of qualifiers.
type family Remove q qs where
    Remove _ ('None)    = 'None
    Remove q (q ':. qs) = qs
    Remove q (a ':. qs) = a ':. Remove q qs

-- | ...
type family Element q qs where
    Element _ ('None)    = 'False
    Element q (q ':. qs) = 'True
    Element q (_ ':. qs) = Element q qs

--------------------------------------------------------------------------------
-- ** Rep. of a valid qualifier.

-- | Witness of a symbol qualifier.
data QualRep (qs :: Qualifier p) where
    QualNone  :: QualRep ('None)
    QualPred  :: Proxy q -> QualRep qs -> QualRep (q ':. qs)

-- | Valid symbol qualifiers.
class Qual (qs :: Qualifier p) where
    qualifier :: QualRep qs

instance Qual ('None) where
    qualifier = QualNone

instance Qual qs => Qual (q ':. qs) where
    qualifier = QualPred Proxy qualifier

-- | ...
class qs :- q where
    entails :: QualRep qs -> Proxy q

instance (q ':. qs) :- q where
    entails (QualPred p _) = p

instance (qs :- q) => (p ':. qs) :- q where
    entails (QualPred _ qs) = entails qs

--------------------------------------------------------------------------------
{-
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
-}
--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Evidence names, associated with some 'q'.
newtype Ev q = Ev Name

--------------------------------------------------------------------------------

-- | Generic abstract syntax tree with beta-eta long normal form.
data Beta sym (qs :: Qualifier p) (sig :: Signature p *) where
    -- ^ Variable.
    Var   :: Sig sig => Name -> Beta sym qs sig
    -- ^ Symbol.
    Sym   :: sym sig -> Beta sym 'None sig
    -- ^ Application.
    (:$)  :: Beta sym qs (a ':-> sig) -> Eta sym ps a -> Beta sym (Union qs ps) sig
    -- ^ Evidence-application.
    (:#)  :: Beta sym qs (q ':=> sig) -> Ev q -> Beta sym (q ':. qs) sig

data Eta sym (qs :: Qualifier p) (sig :: Signature p *) where
    -- ^ Body.
    Spine :: Beta sym qs ('Const a) -> Eta sym qs ('Const a)
    -- ^ Abstraction.
    (:\)  :: Sig a => Name -> Eta sym qs sig -> Eta sym qs (a ':-> sig)
    -- ^ Evidence-abstraction.
    (:\\) :: (Qual qs, qs :- q) => Ev q -> Eta sym qs sig -> Eta sym (Remove q qs) (q ':=> sig)

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

-- | Get the highest variable name bound for 'Eta' node.
maxNameEta :: Eta sym qs a -> Name
maxNameEta (n :\ _)  = n
maxNameEta (_ :\\ e) = maxNameEta e
maxNameEta (Spine b) = maxNameBeta b
  where
    maxNameBeta :: Beta sym qs a -> Name
    maxNameBeta (beta :$ eta) = maxNameBeta beta `Prelude.max` maxNameEta eta
    maxNameBeta (beta :# _)   = maxNameBeta beta
    maxNameBeta _             = 0

-- | Interface for variable binding.
lam :: Sig a => (Beta sym qs a -> Eta sym qs b) -> Eta sym qs (a ':-> b)
lam f = v :\ body
  where
    v    = maxNameEta body + 1
    body = f $ Var v

--------------------------------------------------------------------------------

-- | Get the highest evidence name bound for 'Eta' node.
maxEvEta :: Eta sym qs a -> Name
maxEvEta (_ :\ e)     = maxEvEta e
maxEvEta (Ev n :\\ _) = n
maxEvEta (Spine b)    = maxEvBeta b
  where
    maxEvBeta :: Beta sym qs a -> Name
    maxEvBeta (beta :$ eta) = maxEvBeta beta `Prelude.max` maxEvEta eta
    maxEvBeta (beta :# _)   = maxEvBeta beta
    maxEvBeta _             = 0

-- | Interface for evidence binding.
elam :: (Qual qs, qs :- q) => (Ev q -> Eta sym qs b) -> Eta sym (Remove q qs) (q ':=> b)
elam f = Ev v :\\ body
  where
    v    = maxEvEta body + 1
    body = f $ Ev v

--------------------------------------------------------------------------------
-- ** "Smart" constructors.

--  SmartFun' (sym :: Signature p * -> *) (sig :: Signature p *) where
--  SmartFun' sym ('Const a) = \qs . Beta sym qs ('Const a)
--  SmartFun' sym (a ':-> b) = \qs . (exists ps . (SmartFun' sym a) ps -> (SmartFun' sym b) (Union ps qs))
--  SmartFun' sym (q ':=> b) = \qs . Ev q -> (SmartFun sym b) (Insert q qs)

-- | Map a symbol to its corresponding "smart" constructor.
type family SmartFun (sym :: Signature p * -> *) (qs :: Qualifier p) (sig :: Signature p *) where
    SmartFun sym qs ('Const a) = Beta sym qs ('Const a)
    SmartFun sym qs (a ':-> b) = SmartFun sym ? a -> SmartFun sym (Union qs ?) b
    SmartFun sym qs (q ':=> b) = Ev q -> SmartFun sym (Insert q qs) b

-- | Reconstruct a symbol's signature.
type family SmartSig f :: Signature p * where
    SmartSig (AST _ _ a) = a
    SmartSig (Ev q -> f) = q ':=> SmartSig f
    SmartSig (a -> f)    = SmartSig a ':-> SmartSig f

-- | ...
type family SmartQual f :: Qualifier p where
    SmartQual (AST _ q _) = q
    SmartQual (Ev q -> f) = SmartQual f
    SmartQual (a -> f)    = SmartQual f

-- | Fetch the symbol of a "smart" constructor.
type family SmartSym f :: Signature p * -> * where
    SmartSym (AST s _ _) = s
    SmartSym (Ev _ -> f) = SmartSym f
    SmartSym (_ -> f)    = SmartSym f

--------------------------------------------------------------------------------

-- | Make a "smart" constructor for a symbol.
smartSym' :: forall sym (sig :: Signature p *) f
    .  ( Sig sig
       , f   ~ SmartFun sym sig
       , sig ~ SmartSig  f
       , sym ~ SmartSym  f
       )
    => sym sig -> f
smartSym' sym = smartBeta (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall a . SigRep a -> Beta sym 'None a -> SmartFun sym a
    smartBeta (SigConst)    ast = ast
    smartBeta (SigPart a b) ast = \f -> smartBeta b (ast :$ smartEta a f)
--  smartBeta (SigPred p b) ast = \e -> smartBeta b (ast :# e)

    smartEta :: forall a . SigRep a -> SmartFun sym a -> Eta sym 'None a
    smartEta (SigConst)    f = Spine f
    smartEta (SigPart a b) f = withDict (witSig a) (lam (smartEta b . f . smartBeta a))
--  smartEta (SigPred p b) f = undefined

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
{-
-- | Make a "smart" constructor for a symbol.
smartSym :: forall p sup sub (sig :: Signature p *) f
    .  ( Sig sig
       , f   ~ SmartFun sup sig
       , sig ~ SmartSig f
       , sup ~ SmartSym f
       , sub :<: sup
       )
    => sub sig -> f
smartSym = smartSym' . inj
-}
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
