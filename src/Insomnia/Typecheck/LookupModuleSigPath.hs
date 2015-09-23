{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Insomnia.Typecheck.LookupModuleSigPath (lookupModuleSigPath, projectModuleField) where

import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Common.ModuleKind
import Insomnia.ModuleType (ToplevelSummary(..), ModuleTypeNF(..), SigV(..), Signature(..))
import Insomnia.Types (TypeConstructor(..), TypePath(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.WhnfModuleType (whnfModuleType)

lookupModuleSigPath :: Path -> TC ModuleTypeNF
lookupModuleSigPath (IdP ident) = lookupModuleSig ident
lookupModuleSigPath (TopRefP tr) = typeError ("unexepected bare toplevel reference " <> formatErr tr)
lookupModuleSigPath (ProjP (TopRefP tr) f) = do
  tsum <- lookupToplevelSummary tr
  projectToplevelModuleField (TopRefP tr) tsum f
lookupModuleSigPath (ProjP pmod fieldName) = do
  modnf <- lookupModuleSigPath pmod
  case modnf of
   SigMTNF (SigV sig ModuleMK) -> projectModuleField pmod fieldName sig
   SigMTNF (SigV _sig ModelMK) ->
     typeError ("unexpected model when projecting " <> formatErr fieldName
                <> " from " <> formatErr pmod)
   FunMTNF {} -> typeError ("unexpected functor when projecting " <> formatErr fieldName
                            <> " from " <> formatErr pmod)

projectToplevelModuleField :: Path -> ToplevelSummary -> Field -> TC ModuleTypeNF
projectToplevelModuleField pmod UnitTS fld =
  typeError ("toplevel " <> formatErr pmod <> " does not have a module " <> formatErr fld)
projectToplevelModuleField pmod (SignatureTS _ bnd) fld =
  U.lunbind bnd $ \((_sigId, _sigmt), rest) -> projectToplevelModuleField pmod rest fld
projectToplevelModuleField pmod (ModuleTS fld' bnd) fld =
  U.lunbind bnd $ \((modId, U.unembed -> modTy), rest) ->
  if fld == fld'
  then return modTy
  else let rest' = U.subst modId (ProjP pmod fld') rest
       in projectToplevelModuleField pmod rest' fld

projectModuleField :: Path -> Field -> Signature -> TC ModuleTypeNF
projectModuleField pmod fieldName = go
  where
    go :: Signature -> TC ModuleTypeNF
    go UnitSig = typeError ("The module " <> formatErr pmod
                            <> " does not have a submodule named "
                            <> formatErr fieldName)
    go (ValueSig _ _ mrest) = go mrest
    go (TypeSig fld' bnd) =
      U.lunbind bnd $ \((tycon', _), mrest_) ->
      -- slightly tricky - we have to replace the tycon' in the rest
      -- of the module by the selfified name of the component so that
      -- once we finally find the signature that we need, it will
      -- refer to earlier components of its parent module by the
      -- correct name.
      
      -- Note that there is no need to extend env with this type since
      -- we started with a module that was already in the environment,
      -- and the invariant that the environment maintains is that all
      -- of its projectable types have already been added to the env.
      let mrest = U.subst tycon' (TCGlobal $ TypePath pmod fld') mrest_
      in go mrest
    go (SubmoduleSig fld' bnd) =
      if fieldName /= fld'
      then
        U.lunbind bnd $ \((ident', _), mrest_) ->
        -- No need to extend env with this module's type since any
        -- reference to it in mrest will call "LookupModuleSigPath" again,
        -- and we'll pull it out from the parent module at that point.
        let mrest = U.subst ident' (ProjP pmod fld') mrest_
        in go mrest
      else
        U.lunbind bnd $ \((_, U.unembed -> modTy), _) ->
        whnfModuleType modTy <??@ ("while projecting "
                                   <> formatErr fieldName
                                   <> " near " <> formatErr pmod)
