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
  SigIdentifier,
  Field,
  Path(..),
  SigPath(..),
  pathHeadSkelForm,
  headSkelFormToPath,
  lastOfPath
  ) where

import Data.Function (on)
import Data.Monoid ((<>), Endo(..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal
import Insomnia.Unify (UVar)

-- | Identifiers are have a global identity in a freshness monad.  The
-- identifiers are associated with models, but they stand for model
-- paths (that is, they are /symbols/ rather than variables).
type Identifier = Name Path

-- | SigIdentifiers are associated with model types (but the name
-- SigIdentifier is nicer than "model type identifier").  Unlike models, model types are in a flat
-- namespace, so SigPaths are simpler.
type SigIdentifier = Name SigPath

type Field = String

-- | A path selects a model sub-component of a parent model.
data Path =
  IdP !Identifier 
  | ProjP !Path !Field
  deriving (Show, Typeable, Generic)

-- | A signature path identifies a model type.  The namespace for
-- model types is flat, so this is a particularly degenerate representation.
newtype SigPath = SigIdP SigIdentifier
  deriving (Show, Typeable, Generic)

instance Alpha Path
instance Alpha SigPath

instance Eq Path where
  (==) = aeq

instance Ord Path where
  -- if same head and identical skeleton prefixes, then
  -- shorter name preceeds the longer one.
  -- so A.B.C is GT than A.B is GT than A
  compare = compare `on` pathHeadSkelForm


instance Eq SigPath where
  (==) = aeq

instance Ord SigPath where
  (SigIdP sid1) `compare` (SigIdP sid2) = sid1 `compare` sid2

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

instance Subst Path (UVar w a) where
  subst _ _ = id
  substs _ = id

instance Subst Path Literal where
  subst _ _ = id
  substs _ = id
