{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Decoration
    (
    -- * Symbol decorations.
      (:&:)(..)
    , decorate
    , strip
    , smartSymDecor
    ) where

import Language.Diorite.Syntax
    ( Sig, Sym(..), Beta(..), Eta(..)
    , SmartBeta, SmartSig, SmartSym
    , Project(..), (:<:)(..), smartSym')
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Traversal (Result)

--------------------------------------------------------------------------------
-- * Decorated symbols.
--------------------------------------------------------------------------------

-- | Decorating symbols with additional information.
data (sym :&: info) sig where
    (:&:) :: { _sym   :: sym sig
             , _decor :: info (Result sig)
             }
          -> (sym :&: info) sig

instance Render sym => Render (sym :&: info) where
    renderSym     = renderSym . _sym
    renderArgs as = renderArgs as . _sym

instance Sym sym => Sym (sym :&: info) where
    symbol = symbol . _sym

instance Project sub sup => Project sub (sup :&: info) where
    prj = prj . _sym

--------------------------------------------------------------------------------

-- | Decorate every node in an "AST" according to 'f'.
decorate :: forall sym info rs sig
    .  (forall a . sym a -> info (Result a))
    -> Beta sym rs sig -> Beta (sym :&: info) rs sig
decorate _ (Var n)     = Var n
decorate f (Sym s)     = Sym (s :&: f s)
decorate f (b :# p)    = decorate f b :# p
decorate f (b :$ e)    = decorate f b :$ decorateEta e
  where
    decorateEta :: forall p a . Eta sym p a -> Eta (sym :&: info) p a
    decorateEta (n :\  e') = n :\  decorateEta e'
    decorateEta (p :\\ e') = p :\\ decorateEta e'
    decorateEta (Spine b') = Spine (decorate f b')
decorate f (Local b p) = Local (decorate f b) p

-- | Strip decorations from every node in an "AST".
strip :: Beta (sym :&: info) rs sig -> Beta sym rs sig
strip (Var n)  = Var n
strip (Sym s)  = Sym (_sym s)
strip (b :# p) = strip b :# p
strip (b :$ e) = strip b :$ stripEta e
  where
    stripEta :: Eta (sym :&: info) rs sig -> Eta sym rs sig
    stripEta (n :\  e') = n :\  stripEta e'
    stripEta (p :\\ e') = p :\\ stripEta e'
    stripEta (Spine b') = Spine (strip b')
strip (Local b p) = Local (strip b) p

-- | Make a "smart" constructor for a symbol decorated with some information.
smartSymDecor :: forall sup sub info sig f
    .  ( Sig sig
       , f              ~ SmartBeta (sup :&: info) sig
       , sig            ~ SmartSig f
       , (sup :&: info) ~ SmartSym f
       , sub :<: sup
       )
    => info (Result sig) -> sub sig -> f
smartSymDecor d = smartSym' . (:&: d) . inj

--------------------------------------------------------------------------------
-- Fin.
