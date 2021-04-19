{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Label
    (
    -- * ...
      Rgn(..)
    , local
    , at
    ) where

import Language.Diorite.Signatures (Qualifier(..))
import Language.Diorite.Syntax (Beta(..), Eta(..), AST, ASTF, elam, (:<:)(..))
import Language.Diorite.Region.Annotation (Put(..))
import qualified Language.Diorite.Signatures as S (Signature(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Annotated AST.
type LAST sym qs sig = AST sym qs sig

--------------------------------------------------------------------------------
-- ** ...

data Rgn a where
    Local :: Rgn (('Put r 'S.:=> a) 'S.:-> a)
    At    :: Rgn (a 'S.:-> a)

local :: forall sym r qs a . Rgn :<: sym
    => ASTF sym ('Put r ':. qs) a
    -> ASTF sym qs a
local b = loc :$ elam (const (Spine b))
  where
    loc :: AST sym 'None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    loc = inj Local

at :: ASTF sym qs a -> ASTF sym qs a
at = id

--------------------------------------------------------------------------------
-- Fin.
