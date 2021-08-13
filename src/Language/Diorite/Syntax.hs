{-# OPTIONS_GHC -Wall #-}
--{-# OPTIONS_GHC -fprint-explicit-foralls #-}
--{-# OPTIONS_GHC -fprint-explicit-kinds #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Diorite.Syntax
    (
    -- * Abstract syntax trees.
      Name
    , Ev(..)
    , Symbol
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    , Sym(..)
    , lam
    , elam
    -- * "Smart" constructors.
    , Exists(..)
    , Ex(..)
    , SmartBeta
    , SmartSig
    , SmartQual
    , SmartEx
    , SmartSym
    , smartSym'
    , smartQual
    -- * Open symbol domains.
    , Empty
    , (:+:)(..)
    , Project(..)
    , (:<:)(..)
    , smartSym
    -- * Utilities.
    , (|-)
    , eqP
    ) where

-- Related:
--   https://emilaxelsson.github.io/documents/axelsson2012generic.pdf

import Language.Diorite.Signatures
import Language.Diorite.Qualifiers
import Language.Diorite.Qualifiers.Witness

import Data.Constraint (withDict, HasDict, Constraint)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, eqT)
import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Evidence names, associated with some 'q'.
newtype Ev q = Ev Name

-- | Kind short-hand for symbols.
type Symbol p a = Signature p a -> a

-- | Generic abstract syntax tree with beta-eta long normal form.
type Beta :: forall p . Symbol p * -> Qualifier p -> Signature p * -> *
data Beta sym qs sig where
    -- ^ Variable.
    Var   :: (Qual qs, Sig sig) => Name -> Beta sym qs sig
    -- ^ Symbol.
    Sym   :: sym sig -> Beta sym 'None sig
    -- ^ Application.
    (:$)  :: Beta sym qs (a ':-> sig) -> Eta sym ps a -> Beta sym (Union qs ps) sig
    -- ^ Evidence-application.
    (:#)  :: Beta sym qs (q ':=> sig) -> Ev q -> Beta sym (q ':. qs) sig

type Eta :: forall p . Symbol p * -> Qualifier p -> Signature p * -> *
data Eta sym qs sig where
    -- ^ Body.
    Spine :: Beta sym qs ('Const a) -> Eta sym qs ('Const a)
    -- ^ Abstraction.
    (:\)  :: Sig a => Name -> Eta sym qs sig -> Eta sym qs (a ':-> sig)
    -- ^ Evidence-abstraction.
--  (:\\) :: Ev q -> Eta sym (q ':. qs) sig -> Eta sym qs (q ':=> sig) 
    (:\\) :: (Elem q qs ~ 'True, Typeable q) => Ev q -> Eta sym qs sig -> Eta sym (Remove q qs) (q ':=> sig)
-- todo: clean up the new constraints.
-- todo: does ev-abs. not also abs. qualifiers assoc. with 'a'? No... right?

infixl 1 :$, :#
infixr 9 :\, :\\

-- | Generic AST, parameterized by a symbol domain.
type AST sym qs sig = Beta sym qs sig

-- | Fully applied AST (constant value).
type ASTF sym qs a = Beta sym qs ('Const a)

-- | Symbol with a valid signature.
type  Sym :: forall p . Symbol p * -> Constraint
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
lam :: Sig a => (Beta sym 'None a -> Eta sym qs b) -> Eta sym qs (a ':-> b)
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
elam :: Typeable q => (Ev q -> Eta sym (q ':. qs) b) -> Eta sym qs (q ':=> b)
elam f = Ev v :\\ body
  where
    v    = maxEvEta body + 1
    body = f $ Ev v

--------------------------------------------------------------------------------
-- ** "Smart" constructors.

-- | ...
type Exists :: * -> *
data Exists p = Empty | Fun (Exists p) (Exists p) | Pre p (Exists p)
-- note: Since existential quantification isn't really a thing in Haskell I have
--       these 'Exists' like types to distribute qualifiers. Not sure what a
--       better named for it would be...

-- | ...
type Unique :: forall p . p -> Exists p -> *
type Unique q qs = Remove q (SmartQual qs) :~: (SmartQual qs)
-- todo: Turn this into a class constraint?

-- | ...
type ExRep :: forall p . Exists p -> *
data ExRep es where
    ExEmpty :: ExRep 'Empty
    ExUnion :: ExRep qs -> ExRep ps -> ExRep ('Fun qs ps)
    ExPred  :: Typeable q => Unique q qs -> Proxy q -> ExRep qs -> ExRep ('Pre q qs)

class Ex es where
    record :: ExRep es

instance Ex ('Empty) where
    record = ExEmpty

instance (Ex qs, Ex ps) => Ex ('Fun qs ps) where
    record = ExUnion record record

instance (Typeable q, Remove q (SmartQual qs) ~ (SmartQual qs), Ex qs) => Ex ('Pre q qs) where
    record = ExPred Refl Proxy record

--------------------------------------------------------------------------------

-- | Map a symbol to its corresponding "smart" constructor.
type SmartBeta :: forall p . Symbol p * -> Qualifier p -> Exists p -> Signature p * -> *
type family SmartBeta sym qs ex sig where
    SmartBeta sym qs ('Empty)     ('Const a) = Beta sym qs ('Const a)
    SmartBeta sym qs ('Fun ps rs) (a ':-> b) = SmartBeta sym 'None ps a -> SmartBeta sym (Union qs (SmartQual ps)) rs b
    SmartBeta sym qs ('Pre q rs)  (q ':=> b) = Ev q -> SmartBeta sym (q ':. qs) rs b

-- | Reconstruct a symbol's signature.
type SmartSig :: forall p . * -> Signature p *
type family SmartSig f where
    SmartSig (AST _ _ a) = a
    SmartSig (Ev q -> f) = q ':=> SmartSig f
    SmartSig (a -> f)    = SmartSig a ':-> SmartSig f

-- | ...
type SmartQual :: forall p . Exists p -> Qualifier p
type family SmartQual es where
    SmartQual ('Empty)     = 'None
    SmartQual ('Fun ps qs) = Union (SmartQual ps) (SmartQual qs)
    SmartQual ('Pre _  qs) = SmartQual qs

-- | ...
type SmartEx :: forall p . * -> Exists p
type family SmartEx f where
    SmartEx (AST _ _ _) = 'Empty
    SmartEx (Ev p -> f) = 'Pre p (SmartEx f)
    SmartEx (a -> f)    = 'Fun (SmartEx a) (SmartEx f)

-- | Fetch the symbol of a "smart" constructor.
type SmartSym :: forall p . * -> Symbol p *
type family SmartSym f where
    SmartSym (AST s _ _) = s
    SmartSym (Ev _ -> f) = SmartSym f
    SmartSym (_ -> f)    = SmartSym f

-- | ...
smartQual :: ExRep es -> QualRep (SmartQual es)
smartQual (ExEmpty)       = QualNone
smartQual (ExUnion qs ps) = union (smartQual qs) (smartQual ps)
smartQual (ExPred _ _ qs) = smartQual qs

--------------------------------------------------------------------------------

-- | Make a "smart" constructor for a symbol.
smartSym' :: forall p (es :: Exists p) (sym :: Symbol p *) (sig :: Signature p *) (f :: *)
    .  ( Sig sig
       , Ex es
       , f   ~ SmartBeta sym 'None es sig
       , es  ~ SmartEx  f
       , sig ~ SmartSig f
       , sym ~ SmartSym f
       )
    => sym sig -> f
smartSym' sym = smartBeta (record :: ExRep es) (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall e q a . ExRep e -> SigRep a -> Beta sym q a -> SmartBeta sym q e a
    smartBeta (ExEmpty) (SigConst) ast = ast
    smartBeta (ExUnion x y) (SigPart a b) ast =
        \f -> smartBeta y b (ast :$ smartEta x QualNone a f)
    smartBeta (ExPred _ p y) (SigPred p' b) ast | Just Refl <- eqP p p' =
        \e -> smartBeta y b (ast :# e)
    smartBeta _ _ _ = error "What?!"

    smartEta :: forall e q a . ExRep e -> QualRep q -> SigRep a -> SmartBeta sym q e a -> Eta sym (Union q (SmartQual e)) a
    smartEta (ExEmpty) q (SigConst) f =
        witUniIdent q |- Spine f
    smartEta (ExUnion (x :: ExRep x) (y :: ExRep y)) q (SigPart a b) f =
        witSig a |- witUniAssoc q fx fy |- lam (smartEta y (union q fx) b . f . smartBeta x a)
      where
        fx = smartQual x
        fy = smartQual y
    smartEta (ExPred Refl (p :: Proxy x) y) q (SigPred p' b) f | Just Refl <- eqP p p' =
        elam (smartEta y (QualPred p q) b . f)
    smartEta _ _ _ _ = error "What?!"

--------------------------------------------------------------------------------
-- * Open symbol domains.
--------------------------------------------------------------------------------

-- | Empty symbol type.
data Empty :: * -> *

-- | Direct sum of two symbol domains.
type (:+:) :: forall k . (k -> *) -> (k -> *) -> k -> *
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
type  Project :: forall k. (k -> *) -> (k -> *) -> Constraint
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
type (:<:) :: forall k. (k -> *) -> (k -> *) -> Constraint
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
smartSym :: forall p (es :: Exists p) sup sub (sig :: Signature p *) f
    .  ( Sig sig
       , Ex es
       , f   ~ SmartBeta sup 'None es sig
       , es  ~ SmartEx  f
       , sig ~ SmartSig f
       , sup ~ SmartSym f
       , sub :<: sup
       )
    => sub sig -> f
smartSym = smartSym' . inj

--------------------------------------------------------------------------------
-- ** Utils.
--------------------------------------------------------------------------------

(|-) :: HasDict c e => e -> (c => r) -> r
(|-) = withDict

infixr 1 |-

eqP :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> Maybe (a :~: b)
eqP _ _ = eqT

--------------------------------------------------------------------------------
-- Fin.
