-- | Compute the natural signature of a module expression.
--
-- The natural signature can be read off from a structure by giving the types of all its fields.
-- The natural signature of a path is the signature of the corresponding module.
-- The natural signature of a sealed module is the ascribed signature.
-- The natural signature of a functor application is the result of the application.
-- The natural signature of a functor abstraction is a dependent signature from the argument type
--  to the natural signature of the result.
-- The natural signature of a model is the natural signature of the underling structure.
-- The natural signature of a "local ... in Mdl : Mty" model expression is Mty.
--
-- It so happens (by design) that the natural signature is also the
-- principal signature of a module expression, in the sense that any
-- other model type that may be ascribed to the module would have the
-- natural signature as a subsignature.
{-# LANGUAGE ViewPatterns, OverloadedStrings, FlexibleContexts #-}
module Insomnia.Typecheck.NaturalSignature (naturalSignature,
                                            naturalSignatureModuleExpr) where

import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier
import Insomnia.ModuleType
import Insomnia.Module
import Insomnia.Types (TypeConstructor (..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.LookupModuleSigPath (lookupModuleSigPath)
import Insomnia.Typecheck.ModuleType (extendModuleCtxFunctorArgs)
import Insomnia.Typecheck.ExtendModuleCtx (extendModuleCtxNF)
import Insomnia.Typecheck.WhnfModuleType (whnfModuleType)
import Insomnia.Typecheck.TypeDefn (extendTypeDefnCtx, extendTypeAliasCtx)

-- | Returns the "natural" signature of a module.
-- This is a signature in which all type equations are preserved, all
-- type definitions are manifest, and all value signatures are provided.
naturalSignature :: Module -> TC Signature
naturalSignature = go . moduleDecls
  where
    go :: [Decl] -> TC Signature
    go [] = return UnitSig
    go (decl:decls) = do
      goDecl decl (go decls)
    goDecl :: Decl -> TC Signature -> TC Signature
    goDecl decl kont =
      case decl of
        ValueDecl _fld (FunDecl {}) -> kont
        ValueDecl _fld (ValDecl {}) -> kont
        ValueDecl _fld (SampleDecl {}) -> kont
        ValueDecl _fld (ParameterDecl {}) -> kont
        ValueDecl _fld (TabulatedSampleDecl {}) -> kont
        ValueDecl fld (SigDecl _stoch ty) -> do
          sig' <- kont
          return (ValueSig fld ty sig')
        ImportDecl {} ->
          error ("internal error: naturalSignature.goDecl did not expect to see an ImportDecl")
        TypeDefn fld defn -> do
          let ident = U.s2n fld
              tsd = ManifestTypeSigDecl defn
          sig' <- extendTypeDefnCtx (TCLocal ident) defn kont
          return $ TypeSig fld (U.bind (ident, U.embed tsd) sig')
        TypeAliasDefn fld alias -> do
          let ident = U.s2n fld
          sig' <- extendTypeAliasCtx (TCLocal ident) alias kont
          let tsd = AliasTypeSigDecl alias
          return $ TypeSig fld (U.bind (ident, U.embed tsd) sig')
        SubmoduleDefn fld moduleExpr -> do
          -- TODO: proper error message
          submodNF <- naturalSignatureModuleExpr moduleExpr
          let ident = U.s2n fld
          sig' <- extendModuleCtxNF (IdP ident) submodNF $ kont 
          let moduleTy = moduleTypeNormalFormEmbed submodNF
          return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
        SampleModuleDefn fld moduleExpr -> do
          subSigV <- naturalSignatureModuleExpr moduleExpr
          case subSigV of
           (SigMTNF (SigV subSig ModelMK)) -> do
             let ident = U.s2n fld
                 moduleTy = SigMT (SigV subSig ModuleMK)
                 submodNF = SigMTNF (SigV subSig ModuleMK)
             sig' <- extendModuleCtxNF (IdP ident) submodNF $ kont
             return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
           (SigMTNF (SigV _ ModuleMK)) ->
             typeError ("(internal error?) submodule " <> formatErr fld
                        <> " unexpectedly sampled from a module, not a model")
           (FunMTNF {}) ->
             typeError ("unexpectedly submodule " <> formatErr fld
                        <> " is being sampled from a functor")
              

naturalSignatureModuleExpr :: ModuleExpr -> TC ModuleTypeNF
naturalSignatureModuleExpr (ModuleStruct mk mdl) = do
  modSig <- naturalSignature mdl
  return (SigMTNF (SigV modSig mk))
naturalSignatureModuleExpr (ModuleSeal _ mt) = whnfModuleType mt
naturalSignatureModuleExpr (ModuleAssume mt) = whnfModuleType mt
naturalSignatureModuleExpr (ModuleId path) = lookupModuleSigPath path
naturalSignatureModuleExpr (ModuleFun bnd) =
  U.lunbind bnd $ \(tele, body) ->
  extendModuleCtxFunctorArgs tele $ \ _tele teleSig -> do
    bodySig <- naturalSignatureModuleExpr body
    return (FunMTNF $ U.bind teleSig bodySig)
naturalSignatureModuleExpr (ModuleApp pfun pargs) =
  naturalSignatureFunctorApplication pfun pargs
naturalSignatureModuleExpr (ModelLocal _ _ mt) = do
  nf <- whnfModuleType mt
  case nf of
   SigMTNF sigv -> return (SigMTNF sigv)
   FunMTNF {} -> typeError ("model is ascribed a functor type " <> formatErr mt)
naturalSignatureModuleExpr mo@(ModelObserve _m _obss) =
  typeError ("unimplemented natural signature for model observation" <> formatErr mo)

naturalSignatureFunctorApplication :: Path -> [Path] -> TC ModuleTypeNF
naturalSignatureFunctorApplication pfun pargs = do
  funNF <- lookupModuleSigPath pfun
  case funNF of
   FunMTNF bnd ->
     U.lunbind bnd $ \(tele, body) ->
     naturalSignatureTelescope tele pargs body $ \body' -> return body'
   SigMTNF {} ->
     typeError ("natural signature of " <> formatErr pfun
                <> "was not a functor, in application "
                <> formatErr (ModuleApp pfun pargs))

naturalSignatureTelescope :: U.Subst Path s
                             => Telescope (FunctorArgument ModuleTypeNF)
                             -> [Path]
                             -> s
                             -> (s -> TC r)
                             -> TC r
naturalSignatureTelescope tele_ pargs_ rest kont =
  case (tele_, pargs_) of
   (NilT, []) -> kont rest
   (ConsT (U.unrebind -> (param, tele)), parg:pargs) ->
     naturalSignatureFunctorArgument param parg (tele, rest) $ \(tele', rest') ->
     naturalSignatureTelescope tele' pargs rest' $ \rest'' ->
     kont rest''
   (_, _) -> error ("internal error: naturalSignatureTelescope with"
                    ++ " different number of parameters and argument")

naturalSignatureFunctorArgument :: U.Subst Path s
                                   => FunctorArgument ModuleTypeNF
                                   -> Path
                                   -> s
                                   -> (s -> TC r)
                                   -> TC r
naturalSignatureFunctorArgument fa parg rest kont =
  let (FunctorArgument idParam _paramTy) = fa
      rest' = U.subst idParam parg rest
  in kont rest'

