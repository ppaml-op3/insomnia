{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Infer the natural signature of a model by typechecking its constituents.
--
module Insomnia.Typecheck.Model (inferModelExpr, extendDCtx) where

import Control.Applicative ((<$>))
import Control.Lens
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Path(..), Field)
import Insomnia.Types (Kind(..), Con(..), Type(..), freshUVarT)
import Insomnia.Expr (Var, QVar(..), Expr(Q))
import Insomnia.ModelType (ModelType(..), Signature(..), TypeSigDecl(..))
import Insomnia.Model
import Insomnia.Pretty (PrettyShort(..))

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
import Insomnia.Typecheck.ModelType (checkModelType)
import Insomnia.Typecheck.Selfify (selfifyTypeDefn, selfifyModelType)
import Insomnia.Typecheck.ClarifySignature (clarifySignature)
import Insomnia.Typecheck.ExtendModelCtx (extendModelCtx)
import Insomnia.Typecheck.SigOfModelType (signatureOfModelType)
import Insomnia.Typecheck.MayAscribe (mayAscribe)

-- | Infer the signature of the given model expression
inferModelExpr :: Path -> ModelExpr -> (ModelExpr -> Signature -> TC a) -> TC a
inferModelExpr pmod (ModelStruct model) kont = do
  model' <- checkModel pmod model
            <??@ "while checking model " <> formatErr pmod
  msig <- naturalSignature model
  kont (ModelStruct model') msig
inferModelExpr pmod (ModelSeal model mtypeSealed) kont = do
  inferModelExpr pmod model $ \model' msigInferred -> do
    (mtypeSealed', msigSealed) <- checkModelType mtypeSealed
                                      <??@ ("while checking sealing signature of " <> formatErr pmod)
    msigSealed' <- mayAscribe msigInferred msigSealed
                     <??@ ("while checking validity of signature sealing to "
                           <> formatErr pmod)
    kont (ModelSeal model' mtypeSealed') msigSealed'
inferModelExpr pmod (ModelAssume modelType) kont = do
  (modelType', msig) <- checkModelType modelType
                        <??@ ("while checking postulated signature of "
                              <> formatErr pmod)
  kont (ModelAssume modelType') msig
inferModelExpr pmod (ModelId modPathRHS) kont = do
  msig <- lookupModelSigPath modPathRHS
          <??@ ("while checking the definition of " <> formatErr pmod)
  msig' <- clarifySignature modPathRHS msig
  kont (ModelId modPathRHS) msig'
  -- lookup a model's signature (selfified?) and return it.

lookupModelSigPath :: Path -> TC Signature
lookupModelSigPath (IdP ident) = lookupModelSig ident
lookupModelSigPath (ProjP pmod fieldName) = do
  sig <- lookupModelSigPath pmod
  projectModelField pmod fieldName sig

projectModelField :: Path -> Field -> Signature -> TC Signature
projectModelField pmod fieldName = go
  where
    go :: Signature -> TC Signature
    go UnitSig = typeError ("The module " <> formatErr pmod
                            <> " does not have a submodule named "
                            <> formatErr fieldName)
    go (ValueSig _ _ mrest) = go mrest
    go (TypeSig fld' bnd) =
      U.lunbind bnd $ \((ident', _), mrest_) ->
      -- slightly tricky - we have to replace the ident' in the rest
      -- of the module by the selfified name of the component so that
      -- once we finally find the signature that we need, it will
      -- refer to earlier components of its parent model by the
      -- correct name.
      let mrest = U.subst ident' (ProjP pmod fld') mrest_
      in go mrest
    go (SubmodelSig fld' bnd) =
      if fieldName /= fld'
      then
        U.lunbind bnd $ \((ident', _), mrest_) ->
        let mrest = U.subst ident' (ProjP pmod fld') mrest_
        in go mrest
      else
        U.lunbind bnd $ \((_, U.unembed -> modTy), _) ->
        signatureOfModelType modTy

-- | Returns the "natural" signature of a model.
-- This is a signature in which all type equations are preserved, all
-- type definitions are manifest, and all value signatures are provided.
naturalSignature :: Model -> TC Signature
naturalSignature = go . modelDecls
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
        ValueDecl fld (SigDecl ty) -> do
          sig' <- kont
          return (ValueSig fld ty sig')
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
        SubmodelDefn fld modelExpr -> do
          subSig <- naturalSignatureModelExpr modelExpr
          let ident = U.s2n fld
              modelTy = SigMT subSig
          sig' <- kont 
          return $ SubmodelSig fld (U.bind (ident, U.embed modelTy) sig')
            
naturalSignatureModelExpr :: ModelExpr -> TC Signature
naturalSignatureModelExpr (ModelStruct model) = naturalSignature model
naturalSignatureModelExpr (ModelSeal _ mt) = signatureOfModelType mt
naturalSignatureModelExpr (ModelAssume mt) = signatureOfModelType mt
naturalSignatureModelExpr (ModelId path) = lookupModelSigPath path

-- | Typecheck the contents of a model.
checkModel :: Path -> Model -> TC Model
checkModel pmod =
  fmap Model . go . modelDecls
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
      let dcon = Con (ProjP pmod fld)
      guardDuplicateDConDecl dcon
      (td', _) <- checkTypeDefn (Con $ IdP $ U.s2n fld) td
      return $ TypeDefn fld td'
    TypeAliasDefn fld alias -> do
      let dcon = Con (ProjP pmod fld)
      guardDuplicateDConDecl dcon
      (alias', _) <- checkTypeAlias alias
      return $ TypeAliasDefn fld alias'
    ValueDecl fld vd ->
      let qfld = QVar (ProjP pmod fld)
      in ValueDecl fld <$> checkValueDecl fld qfld vd
    SubmodelDefn fld modelExpr -> do
      modelExpr' <- inferModelExpr (ProjP pmod fld) modelExpr
                    (\modelExpr' _sig -> return modelExpr')
      return $ SubmodelDefn fld modelExpr'

checkValueDecl :: Field -> QVar -> ValueDecl -> TC ValueDecl
checkValueDecl fld qlf vd =
  case vd of
    SigDecl t -> do
      guardDuplicateValueDecl qlf
      checkSigDecl t
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

checkSigDecl :: Type -> TC ValueDecl
checkSigDecl t = do
  t' <- checkType t KType
  return $ SigDecl t'

checkFunDecl :: Field -> Maybe Type -> Expr -> TC ValueDecl
checkFunDecl fname msig_ e = do
  res <- solveUnification $ do
    tu <- freshUVarT
    openAbstract msig_ $ \msig -> do
      case msig of
        Just ty -> tu =?= ty
        Nothing -> return ()
      checkExpr e tu
  case res of
    UOkay e' -> return $ FunDecl e'
    UFail err -> typeError ("when checking " <> formatErr fname
                            <> formatErr err)

-- Note that for values, unlike functions we don't generalize
checkValDecl :: Field -> Maybe Type -> Expr -> TC ValueDecl
checkValDecl fld msig e = do
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
      Just ty -> tu =?= ty
      Nothing -> return ()
    checkExpr e tu
  case res of
    UOkay e' -> return $ ValDecl e'
    UFail err -> typeError ("when checking "<> formatErr fld
                            <> formatErr err)
checkSampleDecl :: Field -> Maybe Type -> Expr -> TC ValueDecl
checkSampleDecl fld msig e = do
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
      Just ty -> tu =?= ty
      Nothing -> return ()
    checkExpr e (distT tu)
  case res of
    UOkay e' -> return $ SampleDecl e'
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
      let p = ProjP pmod fld
          shortIdent = U.s2n fld
          substitution_ = selfifyTypeDefn pmod td
          substitution = (shortIdent, p) : substitution_
          -- replace short name occurrences by the qualified name
          td' = U.substs substitution td
          rest' = U.substs substitution rest
      extendTypeDefnCtx (Con p) td' (kont rest')
    TypeAliasDefn fld alias -> \rest kont -> do
      let p = ProjP pmod fld
          shortIdent = U.s2n fld
          substitution = [(shortIdent, p)]
          -- don't need to substitute into 'alias' because type
          -- aliases are not allowed to be recursive.
          rest' = U.substs substitution rest
      extendTypeAliasCtx (Con p) alias (kont rest')
    SubmodelDefn fld modelExpr -> \rest kont -> do
      let pSubMod = ProjP pmod fld
          shortIdent = U.s2n fld
          substitution = [(shortIdent, pSubMod)]
          rest' = U.substs substitution rest
      subSig <- naturalSignatureModelExpr modelExpr
      subSelfSig <- selfifyModelType pSubMod subSig
      extendModelCtx subSelfSig $ kont rest'

extendValueDeclCtx :: Path -> Field -> ValueDecl -> [Decl] -> ([Decl] -> TC [Decl]) -> TC [Decl]
extendValueDeclCtx pmod fld vd =
  let qvar = QVar (ProjP pmod fld)
  in case vd of
    SigDecl t -> extendSigDeclCtx fld qvar t
    FunDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    ValDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    SampleDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)

-- | @extendSigDecl fld qvar ty decls checkRest@ adds the global
-- binding of @qvar@ to type @ty@, and replaces any free appearances
-- of @fld@ by @qvar@ in @decls@ before checking them using
-- @checkRest@.
extendSigDeclCtx :: Field -> QVar -> Type -> [Decl] -> ([Decl] -> TC [Decl]) -> TC [Decl]
extendSigDeclCtx fld qvar t rest kont =
  let v = U.s2n fld :: Var
  in local (envGlobals . at qvar ?~ t)
     . U.avoid [U.AnyName v]
     . kont
     $ U.subst v (Q qvar) rest
