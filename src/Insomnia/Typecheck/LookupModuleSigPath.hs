{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Insomnia.Typecheck.LookupModuleSigPath (lookupModuleSigPath) where

import Control.Lens
import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.ModuleType (SigV(..), sigVSig, Signature(..))
import Insomnia.Types (TypeConstructor(..), TypePath(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SigOfModuleType (signatureOfModuleType)

lookupModuleSigPath :: Path -> TC (SigV Signature)
lookupModuleSigPath (IdP ident) = lookupModuleSig ident
lookupModuleSigPath (ProjP pmod fieldName) = do
  sigV <- lookupModuleSigPath pmod
  projectModuleField pmod fieldName sigV

projectModuleField :: Path -> Field -> (SigV Signature) -> TC (SigV Signature)
projectModuleField pmod fieldName = go
  where
    go :: SigV Signature -> TC (SigV Signature)
    go =  go' . view sigVSig
    go' :: Signature -> TC (SigV Signature)
    go' UnitSig = typeError ("The module " <> formatErr pmod
                            <> " does not have a submodule named "
                            <> formatErr fieldName)
    go' (ValueSig _ _ mrest) = go' mrest
    go' (TypeSig fld' bnd) =
      U.lunbind bnd $ \((tycon', _), mrest_) ->
      -- slightly tricky - we have to replace the tycon' in the rest
      -- of the module by the selfified name of the component so that
      -- once we finally find the signature that we need, it will
      -- refer to earlier components of its parent module by the
      -- correct name.
      let mrest = U.subst tycon' (TCGlobal $ TypePath pmod fld') mrest_
      in go' mrest
    go' (SubmoduleSig fld' bnd) =
      if fieldName /= fld'
      then
        U.lunbind bnd $ \((ident', _), mrest_) ->
        let mrest = U.subst ident' (ProjP pmod fld') mrest_
        in go' mrest
      else
        U.lunbind bnd $ \((_, U.unembed -> modTy), _) ->
        signatureOfModuleType modTy
