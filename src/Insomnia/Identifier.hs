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
  Path(..)
  ) where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

-- | Identifiers are have a global identity in a freshness monad.
type Identifier = Name Path

type Field = String

-- | A path selects a component of a module.
data Path =
  IdP Identifier 
  | ProjP Path Field
  deriving (Show, Typeable, Generic)

instance Alpha Path

instance Subst Path Path where
  isvar (IdP i) = Just (SubstName i)
  isvar _ = Nothing
