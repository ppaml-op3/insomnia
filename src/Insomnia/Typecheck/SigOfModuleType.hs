{-# LANGUAGE ViewPatterns #-}
module Insomnia.Typecheck.SigOfModuleType where

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Telescope
import Insomnia.ModuleType (ModuleType(..), ModuleTypeNF(..),
                            FunctorArgument(..))


import Insomnia.Typecheck.Env


signatureOfModuleType :: ModuleType -> TC ModuleTypeNF
signatureOfModuleType (SigMT sigv) = return $ SigMTNF sigv
signatureOfModuleType (IdentMT msigId) = lookupModuleType msigId
signatureOfModuleType (FunMT bnd) =
  U.lunbind bnd $ \(args, body) -> do
    functorArgumentsNF args $ \argsnf -> do
      bodynf <- signatureOfModuleType body
      return $ FunMTNF $ U.bind argsnf bodynf

functorArgumentsNF :: Telescope (FunctorArgument ModuleType)
                      -> (Telescope (FunctorArgument ModuleTypeNF)
                          -> TC a)
                      -> TC a
functorArgumentsNF = traverseTelescopeContT functorArgumentNF

functorArgumentNF :: FunctorArgument ModuleType
                     -> (FunctorArgument ModuleTypeNF -> TC a)
                     -> TC a
functorArgumentNF (FunctorArgument paramIdent modK (U.unembed -> modTy)) kont = do
  modTyNF <- signatureOfModuleType modTy
  kont $ FunctorArgument paramIdent modK $ U.embed modTyNF
