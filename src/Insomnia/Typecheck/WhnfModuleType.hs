-- | Weak head normalization of module types to module types in normal form.
--  Among other things, it eliminates "SIG where type p = ty" signatures by patching
-- the signature with the type of the RHS.
{-# LANGUAGE ViewPatterns, OverloadedStrings #-}
module Insomnia.Typecheck.WhnfModuleType (whnfModuleType, reduceWhereModuleTypeNF) where

import Control.Applicative
import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier
import Insomnia.ModuleType
import Insomnia.TypeDefn (TypeAlias(..))
import Insomnia.Types

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (inferType)

-- | Dig through a module until we're 'Here'.
-- Unlike a 'Path', we go from the outside
data DigModule =
  Here
  | There !Field !DigModule

-- | Dig through a module until we find a type.
data DigType = DigType !DigModule !Field

-- | Once we find a type, here's what to replace it with.
data PatchTypeField = PatchTypeField !Field !Type !Kind

pathToDig :: Path -> DigModule
pathToDig = go Here 
  where go d (IdP _dontCare) = d
        go d (ProjP p fldLast) =
          go (There fldLast d) p
  
typePathToDig :: TypePath -> DigType
typePathToDig (TypePath p tyFld) = DigType (pathToDig p) tyFld

reduceWhereModuleTypeNF :: ModuleTypeNF -> WhereClause -> TC ModuleTypeNF
reduceWhereModuleTypeNF unpatched (WhereTypeCls bnd tyHead) = do
  digType <- U.lunbind bnd $ \(_dkId, tyPath) -> return (typePathToDig tyPath)
  startDiggingMTNF unpatched digType tyHead

startDiggingMTNF :: ModuleTypeNF -> DigType -> Type -> TC ModuleTypeNF
startDiggingMTNF unpatched (DigType digModule tyFld) tyHead = do
  (tyHead', tyK) <- inferType tyHead
  let
    patch = PatchTypeField tyFld tyHead' tyK
  downMTNF unpatched digModule patch
  <??@ ("while computing where clause signature for type " <> formatErr tyFld)

downMTNF :: ModuleTypeNF -> DigModule -> PatchTypeField -> TC ModuleTypeNF
downMTNF mtnf Here p =
  case mtnf of
   SigMTNF (SigV sig ModuleMK) -> (SigMTNF . flip SigV ModuleMK) <$> patchSig sig p
   SigMTNF (SigV _ ModelMK) -> typeError ("expected a module signature, bug got a model signature")
   FunMTNF {} -> typeError ("expected a module signature, but got a functor")
downMTNF mtnf (There modFld dig) p =
  case mtnf of
   SigMTNF (SigV sig ModuleMK) ->
     (SigMTNF . flip SigV ModuleMK) <$> (acrossSig sig modFld (\mt -> downMT mt dig p)
                                         <??@ ("while computing a where clause signature for submodule "
                                               <> formatErr modFld))
   SigMTNF (SigV _ ModelMK) ->
     typeError ("expected a module signature, but got a model signature")
   FunMTNF {} -> typeError ("expected a module signature, but got a functor")

acrossSig :: Signature -> Field -> (ModuleType -> TC ModuleType) -> TC Signature
acrossSig sig modFld k =
  case sig of
   UnitSig -> typeError ("expected to find submodule " <> formatErr modFld
                         <> ", but it's not present in the signature")
   ValueSig vFld ty rest -> 
     ValueSig vFld ty <$>  acrossSig rest modFld k
   TypeSig tyFld bnd ->
     U.lunbind bnd $ \(typeStuff, rest) -> do
       rest' <- acrossSig rest modFld k
       return $ TypeSig tyFld $ U.bind typeStuff rest'
   SubmoduleSig modCand bnd ->
     U.lunbind bnd $ \((modId, U.unembed -> mt), rest) ->
     if modCand `U.aeq` modFld
     then do
       -- XXX blah: what i really need to do here is apply some kinda continuation.
       mt' <- k mt
       return $ SubmoduleSig modCand $ U.bind (modId, U.embed mt') rest
     else do
       rest' <- acrossSig rest modFld k
       return $ SubmoduleSig modCand $ U.bind (modId, U.embed mt) rest'

downMT :: ModuleType -> DigModule -> PatchTypeField -> TC ModuleType
downMT mt digMod p = do
  mtnf <- whnfModuleType mt
  patchedMtnf <- downMTNF mtnf digMod p
  return $ moduleTypeNormalFormEmbed patchedMtnf

patchSig :: Signature -> PatchTypeField -> TC Signature
patchSig sig ptf@(PatchTypeField fldPatch _ _) =
  case sig of
   UnitSig -> typeError ("where clause modifies field " <> formatErr fldPatch
                         <> " that isn't present in the signature")
   ValueSig f t rest -> do
     rest' <- patchSig rest ptf
     return $ ValueSig f t rest'
   SubmoduleSig modf bnd ->
     U.lunbind bnd $ \(modStuff, rest) -> do
     rest' <- patchSig rest ptf
     return $ SubmoduleSig modf $ U.bind modStuff rest'
   TypeSig fldTy bnd ->
     U.lunbind bnd $ \((tyCon, U.unembed -> tsd), rest) ->
     if fldTy `U.aeq` fldPatch
     then do
       tsd' <- patchTypeSigDecl tsd ptf
       return $ TypeSig fldTy $ U.bind (tyCon, U.embed tsd') rest
     else do
       rest' <- patchSig rest ptf
       return $ TypeSig fldTy $ U.bind (tyCon, U.embed tsd) rest'

patchTypeSigDecl :: TypeSigDecl -> PatchTypeField -> TC TypeSigDecl
patchTypeSigDecl tsd ptf@(PatchTypeField fldPatch _ kPatch) =
  case tsd of
   AbstractTypeSigDecl kCand ->
     if kPatch `U.aeq` kCand
     then AliasTypeSigDecl <$> patchToAlias ptf
     else typeError ("the where clause for field " <> formatErr fldPatch
                     <> " expects a type of kind " <> formatErr kPatch
                     <> " but it is specified in the signature as abstract of kind "
                     <> formatErr kCand)
   ManifestTypeSigDecl {} ->
     typeError ("the where clause for field " <> formatErr fldPatch
               <> " expected to manifest an abstract type, but the signature already has a manifest declaration.")
   AliasTypeSigDecl {} ->
     -- TODO: If the aliases are equivalent, is it okay to just be idempotent here?
     typeError ("the where clause for field " <> formatErr fldPatch
                <> " expected to manifest an abstract type, but the signature already has a manifest declaration.")

patchToAlias :: PatchTypeField -> TC TypeAlias
patchToAlias (PatchTypeField _fld ty_ k_) = do
  (bs, ty) <- go k_ ([], ty_)
  return $ TypeAlias $ U.bind bs ty
  where
    go KType acc = return acc
    go (KArr k1 ks) (bs, ty) = do
      vfresh <- U.lfresh (U.s2n "α")
      let b1 = (vfresh, k1)
          tv1 = TV vfresh
          ty' = ty `TApp` tv1
      go ks $! (b1:bs, ty')



whnfModuleType :: ModuleType -> TC ModuleTypeNF
whnfModuleType (SigMT sigv) = return (SigMTNF sigv)
whnfModuleType (IdentMT modId) = lookupModuleType modId
whnfModuleType (FunMT bnd) =
  U.lunbind bnd $ \(tele, body) ->
  whnfTelescope tele $ \telenf -> do
    bodynf <- whnfModuleType body
    return (FunMTNF $ U.bind telenf bodynf)
whnfModuleType (WhereMT mt whClause) = do
  mtnf <- whnfModuleType mt
  reduceWhereModuleTypeNF mtnf whClause

whnfTelescope :: Telescope (FunctorArgument ModuleType)
                 -> (Telescope (FunctorArgument ModuleTypeNF) -> TC a)
                 -> TC a
whnfTelescope tele =
  traverseTelescopeContT whnfFunctorArgument tele

whnfFunctorArgument :: FunctorArgument ModuleType
                       -> (FunctorArgument ModuleTypeNF -> TC a)
                       -> TC a
whnfFunctorArgument (FunctorArgument argId modK (U.unembed -> mt)) k = do
  mtnf <- whnfModuleType mt
  k $ FunctorArgument argId modK $ U.embed mtnf


                 
