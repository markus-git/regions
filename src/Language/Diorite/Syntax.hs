{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fprint-explicit-foralls #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-} -- hmm..

module Language.Diorite.Syntax
    (
    -- * Abstract syntax trees.
      Name
    , Ev(..)
    , Beta(..)
    , Eta(..)
    , AST
    , ASTF
    , Sym(..)
    , lam
    , elam
    -- * "Smart" constructors.
    , SmartBeta
    , SmartSig
    , SmartQual
    , SmartExt
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

import Language.Diorite.Signatures

import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | Variable names.
type Name = Int

-- | Evidence names, associated with some 'q'.
newtype Ev q = Ev Name

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
    (:\\) :: Ev q -> Eta sym (q ':. qs) sig -> Eta sym qs (q ':=> sig)

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
lam :: Sig a => (Beta sym ps a -> Eta sym qs b) -> Eta sym qs (a ':-> b)
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
elam :: (Ev q -> Eta sym (q ':. qs) b) -> Eta sym qs (q ':=> b)
elam f = Ev v :\\ body
  where
    v    = maxEvEta body + 1
    body = f $ Ev v

--------------------------------------------------------------------------------
-- ** "Smart" constructors.

-- | Map a symbol to its corresponding "smart" constructor.
type family SmartBeta (sym :: Signature p * -> *) (qs :: Qualifier p) (ex :: Ext p) (sig :: Signature p *) where
    SmartBeta sym qs ('X)       ('Const a) = Beta sym qs ('Const a)
    SmartBeta sym qs ('Y ps rs) (a ':-> b) = SmartBeta sym 'None ps a -> SmartBeta sym (Union qs (Flat ps)) rs b
    SmartBeta sym qs ('Z q rs)  (q ':=> b) = Ev q -> SmartBeta sym (q ':. qs) rs b

-- | Reconstruct a symbol's signature.
type family SmartSig f :: Signature p * where
    SmartSig (AST _ _ a) = a
    SmartSig (Ev q -> f) = q ':=> SmartSig f
    SmartSig (a -> f)    = SmartSig a ':-> SmartSig f

-- | Feth the qualifiers of a "smart" constructor.
type family SmartQual f :: Qualifier p where
    SmartQual (AST _ q _) = q
    SmartQual (Ev _ -> f) = SmartQual f
    SmartQual (_ -> f)    = SmartQual f

-- | ...
type family SmartExt f :: Ext p where
    SmartExt (AST _ _ _) = 'X
    SmartExt (Ev p -> f) = 'Z p (SmartExt f)
    SmartExt (a -> f)    = 'Y (SmartExt a) (SmartExt f)

-- | Fetch the symbol of a "smart" constructor.
type family SmartSym f :: Signature p * -> * where
    SmartSym (AST s _ _) = s
    SmartSym (Ev _ -> f) = SmartSym f
    SmartSym (_ -> f)    = SmartSym f

--------------------------------------------------------------------------------

-- | Make a "smart" constructor for a symbol.
smartSym' :: forall (ex :: Ext p) sym (sig :: Signature p *) f
    .  ( Sig sig
       , f   ~ SmartBeta sym 'None ex sig
       , ex  ~ SmartExt f
       , sig ~ SmartSig f
       , sym ~ SmartSym f
       )
    => ExtRep ex -> sym sig -> f
smartSym' ex sym = smartBeta ex (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall e q a . ExtRep e -> SigRep a -> Beta sym q a -> SmartBeta sym q e a
    smartBeta (ExtX) (SigConst) ast = ast
    smartBeta (ExtY x y) (SigPart a b) ast =
        \f -> smartBeta y b (ast :$ smartEta x QualNone a f)
    smartBeta (ExtZ _ p y) (SigPred p' b) ast | Just Refl <- eqP p p' =
        \e -> smartBeta y b (ast :# e)
    smartBeta _ _ _ = error "What?!"

    smartEta :: forall e q a . ExtRep e -> QualRep q -> SigRep a -> SmartBeta sym q e a -> Eta sym (Union q (Flat e)) a
    smartEta (ExtX) q (SigConst) f =
        withDict (witUniIdent q) $
        Spine f
    smartEta (ExtY (x :: ExtRep x) (y :: ExtRep y)) q (SigPart a b) f =
        let fx = flatten' x in
        let fy = flatten' y in
        withDict (witSig a) $
        withDict (witUniAssoc q fx fy) $
        lam (\(v :: Beta sym 'None v) -> smartEta y (union' q fx) b $ f $ smartBeta x a v)
    smartEta (ExtZ Refl (p :: Proxy x) (y :: ExtRep y)) q (SigPred p' (b :: SigRep b)) f | Just Refl <- eqP p p' =
        elam (\(e :: Ev x) -> smartEta y (QualPred p q) b (f e))
    smartEta _ _ _ _ = error "What?!"

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
       , f   ~ SmartBeta sup sig
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
