{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses, FlexibleInstances #-}
module Insomnia.Common.Stochasticity where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Common.ModuleKind

-- | In Insomnia, we have two sorts of term-level definitions:
-- deterministicc parameters and random variables.
data Stochasticity = DeterministicParam | RandomVariable
                   deriving (Show, Eq, Ord, Typeable, Generic)


instance Alpha Stochasticity

-- | Substituting into Stochasticity is the identity for all possible
-- substitution operations that we may attempt.
instance Subst a Stochasticity where
  subst _ _ = id
  substs _ = id

stochasticityForModule :: ModuleKind -> Stochasticity
stochasticityForModule ModuleMK = DeterministicParam
stochasticityForModule ModelMK = RandomVariable

