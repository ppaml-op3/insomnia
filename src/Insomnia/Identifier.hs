-- | An Insomnia identifier stands for a path, which is itself
-- either an identifier or a projection from an identifier.
--
-- The idea is that in the course of typechecking a model, we
-- will need to substitute paths for certain identifiers (ie those that
-- stand for arguments or for submodules).
{-# LANGUAGE DeriveFunctor, DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses
    #-}
module Insomnia.Identifier (
  Identifier,
  Field,
  Path(..),
  pathHeadSkelForm,
  headSkelFormToPath,
  lastOfPath
  ) where

import Data.Function (on)
import Data.Monoid ((<>), Endo(..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Unify (UVar)

-- | Identifiers are have a global identity in a freshness monad.
type Identifier = Name Path

type Field = String

-- | A path selects a component of a module.
data Path =
  IdP Identifier 
  | ProjP Path Field
  deriving (Show, Typeable, Generic)

instance Alpha Path

instance Eq Path where
  (==) = aeq

instance Ord Path where
  -- if same head and identical skeleton prefixes, then
  -- shorter name preceeds the longer one.
  -- so A.B.C is GT than A.B is GT than A
  compare = compare `on` pathHeadSkelForm

type HeadSkelForm = (Identifier, [Field])

-- | Get the last field of a path or the name of the head identifier
-- for a simple path.
lastOfPath :: Path -> Field
lastOfPath (ProjP _ fld) = fld
lastOfPath (IdP ident) = name2String ident

-- | A path in head and skeleton form.
-- hs (ident) = (ident, [])
-- hs (p.f) = (ident, skel ++ [f]) where hs(p) = (ident,skel)
pathHeadSkelForm :: Path -> HeadSkelForm
pathHeadSkelForm = \p -> let
  (ident, endo) = go p
  in (ident, appEndo endo [])
  where
    go (IdP ident) = (ident, Endo id)
    go (ProjP p f) = let
      (ident, endo) = go p
      in (ident, endo <> Endo (f:))

headSkelFormToPath :: HeadSkelForm -> Path
headSkelFormToPath = \(h, fs) -> go fs (IdP h)
  where
    go [] p = p
    go (f:fs) p = go fs $! ProjP p f

instance Subst Path Path where
  isvar (IdP i) = Just (SubstName i)
  isvar _ = Nothing

instance Subst Path (UVar a) where
  subst _ _ = id
  substs _ = id
