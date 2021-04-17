{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Decoration
    (
    -- * Symbol decorations.
      (:&:)(..)
    , decorate
    , strip
    , smartSymDecor
    ) where

import Language.Diorite.Signatures (Signature, Result, Sig, Qualifier(..), Exists, Ex)
import Language.Diorite.Syntax (Beta(..), Eta(..), Sym(..), SmartBeta, SmartEx, SmartSig, SmartSym, Project(..), (:<:)(..), smartSym')
import Language.Diorite.Interpretation (Render(..))

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

-- | Make a "smart" constructor for a symbol decorated with some information.
smartSymDecor :: forall p (es :: Exists p) sup sub info (sig :: Signature p *) f
    .  ( Sig sig
       , Ex es
       , f              ~ SmartBeta (sup :&: info) 'None es sig
       , es             ~ SmartEx  f
       , sig            ~ SmartSig f
       , (sup :&: info) ~ SmartSym f
       , sub :<: sup
       )
    => info (Result sig) -> sub sig -> f
smartSymDecor d = smartSym' . (:&: d) . inj

--------------------------------------------------------------------------------

-- | Decorate every symbol node according to 'f'.
decorate :: forall sym info qs sig
    .  (forall a . sym a -> info (Result a))
    -> Beta sym qs sig
    -> Beta (sym :&: info) qs sig
decorate _ (Var n)     = Var n
decorate f (Sym s)     = Sym (s :&: f s)
decorate f (b :# p)    = decorate f b :# p
decorate f (b :$ e)    = decorate f b :$ decorateEta e
  where
    decorateEta :: forall ps a . Eta sym ps a -> Eta (sym :&: info) ps a
    decorateEta (n :\  e') = n :\  decorateEta e'
    decorateEta (p :\\ e') = p :\\ decorateEta e'
    decorateEta (Spine b') = Spine (decorate f b')

-- | Strip decorations from every symbol node.
strip :: Beta (sym :&: info) qs sig -> Beta sym qs sig
strip (Var n)  = Var n
strip (Sym s)  = Sym (_sym s)
strip (b :# p) = strip b :# p
strip (b :$ e) = strip b :$ stripEta e
  where
    stripEta :: Eta (sym :&: info) qs sig -> Eta sym qs sig
    stripEta (n :\  e') = n :\  stripEta e'
    stripEta (p :\\ e') = p :\\ stripEta e'
    stripEta (Spine b') = Spine (strip b')

--------------------------------------------------------------------------------
-- Fin.
