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
  TopRef,
  TopPath(..),
  Path(..),
  SigPath(..),
  pathHeadSkelForm,
  headSkelFormToPath,
  lastOfPath
  ) where

import Data.Function (on)
import Data.Monoid (Monoid(..), (<>), Endo(..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal
import Insomnia.Common.SampleParameters
import Insomnia.Unify (UVar)

-- | Identifiers are have a global identity in a freshness monad.  The
-- identifiers are associated with models, but they stand for model
-- paths (that is, they are /symbols/ rather than variables).
type Identifier = Name Path

-- | a "TopRef" names a toplevel (for the purposes of imports).
-- By convention these names have a "^" at the front.
type TopRef = Name TopPath

data TopPath = TopPath TopRef
             deriving (Show, Typeable, Generic)

-- | SigIdentifiers are associated with model types (but the name
-- SigIdentifier is nicer than "model type identifier").  Unlike models, model types are in a flat
-- namespace, so SigPaths are simpler.
type SigIdentifier = Name SigPath

type Field = String

-- | A path selects a model sub-component of a parent model.
data Path =
  IdP !Identifier 
  | TopRefP !TopRef
  | ProjP !Path !Field
  deriving (Show, Typeable, Generic)

-- | A signature path identifies a model type.  The namespace for
-- model types is flat, except by reference into another toplevel.
data SigPath = SigIdP SigIdentifier
             | SigTopRefP !TopRef !Field
  deriving (Show, Typeable, Generic)

instance Alpha TopPath
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
  compare = acompare

type HeadSkelForm = (Either TopRef Identifier, [Field])

-- | Get the last field of a path or the name of the head identifier
-- for a simple path.
lastOfPath :: Path -> Field
lastOfPath (ProjP _ fld) = fld
lastOfPath (IdP ident) = name2String ident
lastOfPath (TopRefP tr) = error $ "lastOfPath of a bare toplevel reference " ++ show tr

-- | A path in head and skeleton form.
-- hs (ident) = (ident, [])
-- hs (p.f) = (ident, skel ++ [f]) where hs(p) = (ident,skel)
pathHeadSkelForm :: Path -> HeadSkelForm
pathHeadSkelForm = \p -> let
  (ident, endo) = go p
  in (ident, appEndo endo [])
  where
    go (IdP ident) = (Right ident, mempty)
    go (TopRefP tr) = (Left tr, mempty)
    go (ProjP p f) = let
      (ident, endo) = go p
      in (ident, endo <> Endo (f:))

headSkelFormToPath :: HeadSkelForm -> Path
headSkelFormToPath = \(h, fs) -> go fs (mkH h)
  where
    mkH (Right ident) = IdP ident
    mkH (Left tr) = TopRefP tr
    go [] p = p
    go (f:fs) p = go fs $! ProjP p f

instance Subst TopPath TopPath where
  isvar (TopPath i) = Just (SubstName i)

instance Subst TopPath Path
instance Subst TopPath SigPath

instance Subst Path SigPath

instance Subst Path Path where
  isvar (IdP i) = Just (SubstName i)
  isvar _ = Nothing

instance Subst SigPath SigPath where
  isvar (SigIdP i) = Just (SubstName i)
  isvar _ = Nothing

instance Subst TopPath (UVar w a) where
  subst _ _ = id
  substs _ = id

instance Subst Path (UVar w a) where
  subst _ _ = id
  substs _ = id

instance Subst TopPath Literal where
  subst _ _ = id
  substs _ = id

instance Subst Path Literal where
  subst _ _ = id
  substs _ = id

instance Subst TopPath SampleParameters where
  subst _ _ = id
  substs _ = id

instance Subst Path SampleParameters where
  subst _ _ = id
  substs _ = id
