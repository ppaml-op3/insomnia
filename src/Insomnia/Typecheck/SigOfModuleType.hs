{-# LANGUAGE ViewPatterns #-}
module Insomnia.Typecheck.SigOfModuleType where

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Telescope
import Insomnia.ModuleType (ModuleType(..), ModuleTypeNF(..),
                            FunctorArgument(..))


import Insomnia.Typecheck.Env
import Insomnia.Typecheck.ReduceWhereClause (whnfModuleType)


signatureOfModuleType :: ModuleType -> TC ModuleTypeNF
signatureOfModuleType = whnfModuleType
