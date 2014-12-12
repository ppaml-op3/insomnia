{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Infer the natural signature of a module by typechecking its constituents.
--
module Insomnia.Typecheck.Module (inferModuleExpr, extendDCtx) where

import Prelude hiding (mapM_)

import Control.Applicative ((<$>))
import Control.Lens
import Control.Monad (unless)
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Foldable (mapM_)
import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Identifier (Path(..), Field)
import Insomnia.Types (Kind(..), TypeConstructor(..), TypePath(..),
                       Type(..), freshUVarT)
import Insomnia.Expr (Var, QVar(..), Expr(Q))
import Insomnia.ModuleType (ModuleType(..), Signature(..), TypeSigDecl(..))
import Insomnia.Module
import Insomnia.Pretty (Pretty, PrettyShort(..))

import Insomnia.Unify (Unifiable(..),
                       solveUnification,
                       UnificationResult(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkType)
import Insomnia.Typecheck.Expr (checkExpr)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn,
                                    checkTypeAlias,
                                    extendTypeDefnCtx,
                                    extendTypeAliasCtx)
import Insomnia.Typecheck.ModuleType (checkModuleType)
import Insomnia.Typecheck.Selfify (selfifyTypeDefn, selfifyModuleType)
import Insomnia.Typecheck.ClarifySignature (clarifySignature)
import Insomnia.Typecheck.ExtendModuleCtx (extendModuleCtx)
import Insomnia.Typecheck.SigOfModuleType (signatureOfModuleType)
import Insomnia.Typecheck.MayAscribe (mayAscribe)

-- | Infer the signature of the given module expression
inferModuleExpr :: Path -> ModuleExpr -> (ModuleExpr -> Signature -> ModuleKind -> TC a) -> TC a
inferModuleExpr pmod (ModuleStruct mdl modK) kont = do
  mdl' <- checkModule pmod mdl
            <??@ "while checking module " <> formatErr pmod
  msig <- naturalSignature mdl
  kont (ModuleStruct mdl' modK) msig modK
inferModuleExpr pmod (ModuleSeal mdl mtypeSealed) kont = do
  inferModuleExpr pmod mdl $ \mdl' msigInferred modK -> do
    (mtypeSealed', msigSealed, modK') <-
      checkModuleType mtypeSealed
      <??@ ("while checking sealing signature of " <> formatErr pmod)
    unless (modK == modK') $ do
      typeError (formatErr pmod <> " is sealing a "
                 <> formatErr modK <> " as a " <> formatErr modK')
    msigSealed' <- mayAscribe msigInferred msigSealed
                   <??@ ("while checking validity of signature sealing to "
                         <> formatErr pmod)
    kont (ModuleSeal mdl' mtypeSealed') msigSealed' modK'
inferModuleExpr pmod (ModuleAssume moduleType) kont = do
  (moduleType', msig, modK) <- checkModuleType moduleType
                        <??@ ("while checking postulated signature of "
                              <> formatErr pmod)
  kont (ModuleAssume moduleType') msig modK
inferModuleExpr pmod (ModuleId modPathRHS) kont = do
  (msig, modK) <- lookupModuleSigPath modPathRHS
          <??@ ("while checking the definition of " <> formatErr pmod)
  msig' <- clarifySignature modPathRHS msig
  kont (ModuleId modPathRHS) msig' modK
  -- lookup a module's signature (selfified?) and return it.

lookupModuleSigPath :: Path -> TC (Signature, ModuleKind)
lookupModuleSigPath (IdP ident) = lookupModuleSig ident
lookupModuleSigPath (ProjP pmod fieldName) = do
  (sig, _modK) <- lookupModuleSigPath pmod
  projectModuleField pmod fieldName sig

projectModuleField :: Path -> Field -> Signature -> TC (Signature, ModuleKind)
projectModuleField pmod fieldName = go
  where
    go :: Signature -> TC (Signature, ModuleKind)
    go UnitSig = typeError ("The module " <> formatErr pmod
                            <> " does not have a submodule named "
                            <> formatErr fieldName)
    go (ValueSig _ _ _ mrest) = go mrest
    go (TypeSig fld' bnd) =
      U.lunbind bnd $ \((tycon', _), mrest_) ->
      -- slightly tricky - we have to replace the tycon' in the rest
      -- of the module by the selfified name of the component so that
      -- once we finally find the signature that we need, it will
      -- refer to earlier components of its parent module by the
      -- correct name.
      let mrest = U.subst tycon' (TCGlobal $ TypePath pmod fld') mrest_
      in go mrest
    go (SubmoduleSig fld' bnd) =
      if fieldName /= fld'
      then
        U.lunbind bnd $ \((ident', _), mrest_) ->
        let mrest = U.subst ident' (ProjP pmod fld') mrest_
        in go mrest
      else
        U.lunbind bnd $ \((_, U.unembed -> modTy), _) ->
        signatureOfModuleType modTy

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
        ValueDecl fld (SigDecl stoch ty) -> do
          sig' <- kont
          return (ValueSig stoch fld ty sig')
        TypeDefn fld defn -> do
          let ident = U.s2n fld
          sig' <- kont
          let tsd = ManifestTypeSigDecl defn
          return $ TypeSig fld (U.bind (ident, U.embed tsd) sig')
        TypeAliasDefn fld alias -> do
          let ident = U.s2n fld
          sig' <- kont
          let tsd = AliasTypeSigDecl alias
          return $ TypeSig fld (U.bind (ident, U.embed tsd) sig')
        SubmoduleDefn fld moduleExpr -> do
          (subSig, modK) <- naturalSignatureModuleExpr moduleExpr
          let ident = U.s2n fld
              moduleTy = SigMT subSig modK
          sig' <- kont 
          return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
            
naturalSignatureModuleExpr :: ModuleExpr -> TC (Signature, ModuleKind)
naturalSignatureModuleExpr (ModuleStruct mdl modK) = do
  modSig <- naturalSignature mdl
  return (modSig, modK)
naturalSignatureModuleExpr (ModuleSeal _ mt) = signatureOfModuleType mt
naturalSignatureModuleExpr (ModuleAssume mt) = signatureOfModuleType mt
naturalSignatureModuleExpr (ModuleId path) = lookupModuleSigPath path

-- | Typecheck the contents of a module.
checkModule :: Path -> Module -> TC Module
checkModule pmod =
  fmap Module . go . moduleDecls
  where
    go :: [Decl] -> TC [Decl]
    go [] = return []
    go (decl:decls) = do
      decl' <- checkDecl pmod decl
      decls' <- extendDCtx pmod decl' decls go
      return (decl':decls')

checkDecl :: Path -> Decl -> TC Decl
checkDecl pmod d =
  checkDecl' pmod d
  <??@ "while checking " <> formatErr (PrettyShort d)

-- | Given the path to the module, check the declarations.
checkDecl' :: Path -> Decl -> TC Decl
checkDecl' pmod d =
  case d of
    TypeDefn fld td -> do
      let dcon = TCGlobal (TypePath pmod fld)
      guardDuplicateDConDecl dcon
      (td', _) <- checkTypeDefn (TCLocal $ U.s2n fld) td
      return $ TypeDefn fld td'
    TypeAliasDefn fld alias -> do
      let dcon = TCGlobal (TypePath pmod fld)
      guardDuplicateDConDecl dcon
      (alias', _) <- checkTypeAlias alias
      return $ TypeAliasDefn fld alias'
    ValueDecl fld vd ->
      let qfld = QVar pmod fld
      in ValueDecl fld <$> checkValueDecl fld qfld vd
    SubmoduleDefn fld moduleExpr -> do
      moduleExpr' <- inferModuleExpr (ProjP pmod fld) moduleExpr
                    (\moduleExpr' _sig _modK -> return moduleExpr')
      return $ SubmoduleDefn fld moduleExpr'

checkValueDecl :: Field -> QVar -> ValueDecl -> TC ValueDecl
checkValueDecl fld qlf vd =
  case vd of
    SigDecl stoch t -> do
      guardDuplicateValueDecl qlf
      checkSigDecl stoch t
    FunDecl e -> do
      msig <- lookupGlobal qlf
      ensureNoDefn qlf
      let v = (U.s2n fld :: Var)
          -- capture any unbound references to "fld" in the body
          -- and replace them with the fully qualified name of this
          -- function.
          body = U.subst v (Q qlf) e
      U.avoid [U.AnyName v] $ checkFunDecl fld msig body
    ValDecl e -> do
      msig <- lookupGlobal qlf
      ensureNoDefn qlf
      let v = (U.s2n fld :: Var)
      U.avoid [U.AnyName v] $ checkValDecl fld msig e
    SampleDecl e -> do
      msig <- lookupGlobal qlf
      ensureNoDefn qlf
      let v = (U.s2n fld :: Var)
      U.avoid [U.AnyName v] $ checkSampleDecl fld msig e
    ParameterDecl e -> do
      msig <- lookupGlobal qlf
      ensureNoDefn qlf
      let v = (U.s2n fld :: Var)
      U.avoid [U.AnyName v] $ checkParameterDecl fld msig e

checkSigDecl :: Stochasticity -> Type -> TC ValueDecl
checkSigDecl stoch t = do
  t' <- checkType t KType
  return $ SigDecl stoch t'

ensureParameter :: Pretty what => what -> Stochasticity -> TC ()
ensureParameter what stoch =
  case stoch of
   DeterministicParam -> return ()
   RandomVariable ->
     typeError ("Expected " <> formatErr what
                <> " to be a parameter, but it was declared as a random variable")

ensureRandomVariable :: Pretty what => what -> Stochasticity -> TC ()
ensureRandomVariable what stoch =
  case stoch of
   RandomVariable -> return ()
   DeterministicParam ->
     typeError ("Expected " <> formatErr what
                <> " to be a random variable, but it was declared as a parameter")

ensureExpStochasticity :: Pretty what => Stochasticity -> what -> Stochasticity -> TC ()
ensureExpStochasticity want =
  case want of
   RandomVariable -> ensureRandomVariable
   DeterministicParam -> ensureParameter

checkFunDecl :: Field -> Maybe (Type, Stochasticity) -> Expr -> TC ValueDecl
checkFunDecl fname msig_ e = do
  mapM_ (ensureParameter fname . snd) msig_
  res <- solveUnification $ do
    tu <- freshUVarT
    openAbstract (fmap fst msig_) $ \mty -> do
      case mty of
        Just ty -> tu =?= ty
        Nothing -> return ()
      checkExpr e tu
  case res of
    UOkay e' -> return $ FunDecl e'
    UFail err -> typeError ("when checking " <> formatErr fname
                            <> formatErr err)


-- Note that for values, unlike functions we don't generalize
checkValDecl :: Field -> Maybe (Type, Stochasticity) -> Expr -> TC ValueDecl
checkValDecl fld msig e = do
  mapM_ (ensureRandomVariable fld . snd) msig
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
      Just (ty,_) -> tu =?= ty
      Nothing -> return ()
    checkExpr e tu
  case res of
    UOkay e' -> return $ ValDecl e'
    UFail err -> typeError ("when checking "<> formatErr fld
                            <> formatErr err)

checkSampleDecl :: Field -> Maybe (Type, Stochasticity) -> Expr -> TC ValueDecl
checkSampleDecl fld msig e = do
  mapM_ (ensureRandomVariable fld . snd) msig
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
      Just (ty,_) -> tu =?= ty
      Nothing -> return ()
    checkExpr e (distT tu)
  case res of
    UOkay e' -> return $ SampleDecl e'
    UFail err -> typeError ("when checking " <> formatErr fld
                            <> formatErr err)

checkParameterDecl :: Field -> Maybe (Type, Stochasticity) -> Expr -> TC ValueDecl
checkParameterDecl fld msig e = do
  mapM_ (ensureParameter fld . snd) msig
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
     Just (ty,_) -> tu =?= ty
     Nothing -> return ()
    checkExpr e tu
  case res of
   UOkay e' -> return $ ParameterDecl e'
   UFail err -> typeError ("when checking " <> formatErr fld
                           <> formatErr err)

-- | Given a type ∀ α1∷K1 ⋯ αN∷KN . τ, freshen αᵢ and add them to the
-- local type context in the given continuation which is passed
-- τ[αfresh/α]
openAbstract :: Maybe Type -> (Maybe Type -> TC a) -> TC a
openAbstract Nothing kont = kont Nothing
openAbstract (Just ty) kont =
  case ty of
    TForall bnd -> U.lunbind bnd $ \ ((tv,k), ty') ->
      extendTyVarCtx tv k $ openAbstract (Just ty') kont
    _ -> kont (Just ty)


guardDuplicateValueDecl :: QVar -> TC ()
guardDuplicateValueDecl v = do
  msig <- view (envGlobals . at v)
  mdef <- view (envGlobalDefns . at v)
  case (msig, mdef) of
    (Nothing, Nothing) -> return ()
    (Just _, _) -> typeError (formatErr v <> " already has a type signature")
    (_, Just _) -> typeError (formatErr v <> " already has a definition")

-- | Extend the environment by incorporating the given declaration.
extendDCtx :: Path -> Decl -> [Decl] -> ([Decl] -> TC [Decl]) -> TC [Decl]
extendDCtx pmod d =
  case d of
    ValueDecl fld vd -> extendValueDeclCtx pmod fld vd
    TypeDefn fld td -> \rest kont -> do
      let p = TypePath pmod fld
          shortIdent = U.s2n fld
          substVCons = selfifyTypeDefn pmod td
          substTyCon = [(shortIdent, TCGlobal p)]
          -- replace short name occurrences by the qualified name
          td' = U.substs substTyCon $ U.substs substVCons td
          rest' = U.substs substTyCon $ U.substs substVCons rest
      extendTypeDefnCtx (TCGlobal p) td' (kont rest')
    TypeAliasDefn fld alias -> \rest kont -> do
      let p = TypePath pmod fld
          shortIdent = U.s2n fld
          substitution = [(shortIdent, TCGlobal p)]
          -- don't need to substitute into 'alias' because type
          -- aliases are not allowed to be recursive.
          rest' = U.substs substitution rest
      extendTypeAliasCtx (TCGlobal p) alias (kont rest')
    SubmoduleDefn fld moduleExpr -> \rest kont -> do
      let pSubMod = ProjP pmod fld
          shortIdent = U.s2n fld
          substitution = [(shortIdent, pSubMod)]
          rest' = U.substs substitution rest
      (subSig, modK) <- naturalSignatureModuleExpr moduleExpr
      subSelfSig <- selfifyModuleType pSubMod subSig
      extendModuleCtx subSelfSig $ kont rest'

extendValueDeclCtx :: Path -> Field -> ValueDecl -> [Decl] -> ([Decl] -> TC [Decl]) -> TC [Decl]
extendValueDeclCtx pmod fld vd =
  let qvar = QVar pmod fld
  in case vd of
    SigDecl stoch t -> extendSigDeclCtx fld stoch qvar t
    FunDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    ValDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    SampleDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    ParameterDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)

-- | @extendSigDecl fld qvar ty decls checkRest@ adds the global
-- binding of @qvar@ to type @ty@, and replaces any free appearances
-- of @fld@ by @qvar@ in @decls@ before checking them using
-- @checkRest@.
extendSigDeclCtx :: Field
                    -> Stochasticity
                    -> QVar
                    -> Type
                    -> [Decl]
                    -> ([Decl] -> TC [Decl])
                    -> TC [Decl]
extendSigDeclCtx fld stoch qvar t rest kont =
  let v = U.s2n fld :: Var
  in local (envGlobals . at qvar ?~ (t,stoch))
     . U.avoid [U.AnyName v]
     . kont
     $ U.subst v (Q qvar) rest
