{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Annotation where

import Language.Diorite.Syntax (Signature(..), Name, Beta(..), Eta(..))
import Language.Diorite.Region.Qualifiers (Put(..))

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | ...
data Place (sig :: Signature (Put r) *) where
    Loc :: Name -> Place sig
    At  :: Name -> Place sig

app :: Beta sym (a ':-> sig) -> Eta sym a -> Beta sym sig
app b e = b :$ e

--------------------------------------------------------------------------------
