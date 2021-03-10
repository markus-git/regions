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
    , SmartFun
    , SmartSig
    , SmartSym
--  , smartSym'
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

import Data.Constraint (Dict(..), withDict)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)

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
elam :: (Qual qs, qs :- q) => (Ev q -> Eta sym qs b) -> Eta sym (Remove q qs) (q ':=> b)
elam f = Ev v :\\ body
  where
    v    = maxEvEta body + 1
    body = f $ Ev v

--------------------------------------------------------------------------------
-- ** "Smart" constructors.

--  # Original idea.
--  SmartFun' (sym :: Signature p * -> *) (sig :: Signature p *) where
--  SmartFun' sym ('Const a) = \qs . Beta sym qs ('Const a)
--  SmartFun' sym (a ':-> b) = \qs . (exists ps . (SmartFun' sym a) ps -> (SmartFun' sym b) (Union ps qs))
--  SmartFun' sym (q ':=> b) = \qs . Ev q -> (SmartFun sym b) (Insert q qs)
--
--  # Functions merged with 'SmartFun'.
--  SmartFun (sym :: Signature p * -> *) (qs :: Qualifier p) (sig :: Signature p *) where
--  SmartFun sym qs ('Const a) = Beta sym qs ('Const a)
--  SmartFun sym qs (a ':-> b) = (exists ps . SmartFun sym ps a -> SmartFun sym (Union qs ps) b)
--  SmartFun sym qs (q ':=> b) = Ev q -> SmartFun sym (Insert q qs) b
--
-- # Swap 'exists' for 'forall' arg?

-- | Map a symbol to its corresponding "smart" constructor.
type family SmartFun (sym :: Signature p * -> *)
                     (qs :: Qualifier p)
                     (ex :: Ext p)
                     (sig :: Signature p *)
  where
    SmartFun sym qs ('X)       ('Const a) = Beta sym qs ('Const a)
    SmartFun sym qs ('Y ps rs) (a ':-> b) = SmartFun sym 'None ps a -> SmartFun sym (Union qs (Flat ps)) rs b
    SmartFun sym qs ('Z q rs)  (q ':=> b) = Ev q -> SmartFun sym (q ':. qs) rs b

--------------------------------------------------------------------------------

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

-- | Fetch the symbol of a "smart" constructor.
type family SmartSym f :: Signature p * -> * where
    SmartSym (AST s _ _) = s
    SmartSym (Ev _ -> f) = SmartSym f
    SmartSym (_ -> f)    = SmartSym f

--------------------------------------------------------------------------------

-- # Original idea.
-- smartSym' :: forall sym (sig :: Signature p *) f
--    .  ( Sig sig
--        , f   ~ SmartFun sym sig
--        , sig ~ SmartSig  f
--        , sym ~ SmartSym  f
--        )
--     => sym sig -> f
-- smartSym' sym = smartBeta (signature :: SigRep sig) (Sym sym)
--   where
--     smartBeta :: forall a . SigRep a -> Beta sym 'None a -> SmartFun sym a
--     smartBeta (SigConst)    ast = ast
--     smartBeta (SigPart a b) ast = \f -> smartBeta b (ast :$ smartEta a f)

--     smartEta :: forall a . SigRep a -> SmartFun sym a -> Eta sym 'None a
--     smartEta (SigConst)    f = Spine f
--     smartEta (SigPart a b) f = withDict (witSig a)
--         (lam (smartEta b . f . smartBeta a))
--
-- # ...

-- | Make a "smart" constructor for a symbol.
smartSym' :: forall (ex :: Ext p) sym (sig :: Signature p *) f
    .  ( Sig sig
       , f   ~ SmartFun sym 'None ex sig
       , sig ~ SmartSig  f
       , sym ~ SmartSym  f
       )
    => ExtRep ex -> sym sig -> f
smartSym' ex sym = smartBeta ex (signature :: SigRep sig) (Sym sym)
  where
    smartBeta :: forall e q a .
           ExtRep e
        -> SigRep a
        -> Beta sym q a
        -> SmartFun sym q e a
    smartBeta (ExtX) (SigConst) ast = ast
    -- Beta q a -> SF q e a?
    --   > a ~ (Const a?), e ~ X
    -- Beta q (Const a?) -> SF q X (Const a?)
    --   > expand SF def.
    -- Beta q (Const a?) -> Beta q (Const a?)
    --  ^^^^^^^^^^^^^^^^
    --        ast
    -- =>
    -- 1 : ast :: Beta q (Const a?)
    --
    smartBeta (ExtY x y) (SigPart a b) ast =
        \f -> smartBeta y b (ast :$ smartEta x QualNone a f)
    -- Beta q a -> SF q e a
    --   > a ~ (a? -> b?), e ~ (Y x? y?) ~ x? + y?
    -- Beta q (a? -> b?) -> SF q (x? + y?) (a? -> b?)
    --   > expand SF def.
    -- Beta q (a? -> b?) -> SF 'None x? a? -> SF (q + x?) y? b?
    --  ^^^^^^^^^^^^^^^^     ^^^^^^^^^^^^
    --        ast                  f
    -- =>
    -- 1 : smartEta f  :: Eta ('None + x?) a? ~ Eta x? a?
    -- 2 : ast :$ 1    :: Beta (q + x?) b?
    -- 3 : smartBeta 2 :: SF (q + x?) y? b?
    --
    smartBeta (ExtZ p y) (SigPred p' b) ast | Just Refl <- eqP p p' =
        \e -> smartBeta y b (ast :# e)
    -- Beta q a? -> SF q e a
    --   > a ~ (p? => b?), e ~ (Z p? y?)
    -- Beta q (p? => b?) -> SF q (Z p? y?) (p? => b?)
    --   > expand SF def.
    -- Beta q (p? => b?) -> Ev p? -> SF (p? : q) y? b?
    --  ^^^^^^^^^^^^^^^      ^^^
    --        ast             e
    -- =>
    -- 1 : ast :# e    :: Beta (p? : q) b?
    -- 2 : smartBeta 1 :: SF (p? : q) y? b?
    --
    smartBeta _ _ _ = error "What?!"

    smartEta :: forall e q a .
           ExtRep e
        -> QualRep q
        -> SigRep a
        -> SmartFun sym q e a
        -> Eta sym (Union q (Flat e)) a
    smartEta (ExtX) q (SigConst) f =
        withDict (witUnionNone q) $
        Spine f
    -- SF q e a -> Eta (q + e) a
    --   > a ~ (Const a?), e ~ X
    -- SF q X (Const a?) -> Eta (q + X) (Const a?)
    --   > q + X ~ q, expand SF def.
    -- Beta q (Const a?) -> Eta q (Const a?)
    --  ^^^^^^^^^^^^^^^^
    --         f
    -- =>
    -- 1 : Spine f :: Eta q (Const a?)
    --
    smartEta (ExtY x y) q (SigPart a b) f =
        withDict (witSig a) $
        withDict (witUnionAssoc q (flatten x) (flatten y)) $
        lam (\(v :: Beta sym 'None x) -> smartEta y (smartQ x) b $ f $ smartBeta x a v)
      where
        smartQ :: forall x . ExtRep x -> QualRep (Union q (Flat x))
        smartQ = undefined
    -- SF q e a -> Eta (q + e) a
    --   > a ~ (a? -> b?), e ~ (Y x? y?) ~ x? + y?
    -- SF q (Y x? y?) (a? -> b?) -> Eta (q + x? + y?) (a? -> b?)
    --   > expand SF def.
    -- (SF None x? a? -> SF (q + x?) y? b?) -> Eta (q + x? + y?) (a? -> b?)
    --  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    --                  f
    -- =>
    -- eta constructed with 'lam' => new goal: sugar f into
    -- Beta 'None a? -> Eta (q + x? + y?) b?
    --  ^^^^^^^^^^^
    --      ast
    -- =>
    -- 1 : smartBeta ast :: SF None x? a?
    -- 2 : f 2           :: SF (q + x?) y? b?
    -- 3 : smartEta 3    :: Eta (q + x? + y?) b?
    --
    -- ! not accounted for: assoc of + and flattening of x? & y? !
    -- 3    :: Eta (U (U q (F x?)) (F y?)) _
    -- goal :: Eta (U q (U (F x?) (F y?))) _
    -- =>
    -- 1 : F a ~ a
    -- 2 : (U (U a b) c) ~ (U a (U b c)
    --
    smartEta (ExtZ p y) q (SigPred p' b) f | Just Refl <- eqP p p' =
        undefined
    -- SF q e a -> Eta (q + e) a
    --   > a ~ (p? => b?), e ~ (Z p? y?)
    -- SF q (Z p? y?) (p? => b?) -> Eta (q + (Z p? y?)) (p? => b?)
    --   > (Z p? y?) ~ p? : y?, expand SF def.
    -- Ev p? -> SF (p? : q) y? b? -> Eta (q + (p? : y?)) (p? => b?)
    --  ^^^      ^^^^^^^^^^^^^^^
    --   e              f
    -- =>
    -- 

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
