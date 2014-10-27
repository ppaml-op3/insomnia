{-# LANGUAGE OverloadedStrings #-}
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
import Insomnia.ModelType (Signature(..), TypeSigDecl(..))
import Insomnia.Model

import Insomnia.Unify (Unifiable(..),
                       solveUnification,
                       UnificationResult(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkType)
import Insomnia.Typecheck.Expr (checkExpr)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn, extendTypeDefnCtx)
import Insomnia.Typecheck.ModelType (checkModelType)
import Insomnia.Typecheck.Selfify (selfifyTypeDefn)
import Insomnia.Typecheck.MayAscribe (mayAscribe)

-- | Infer the signature of the given model expression
inferModelExpr :: Path -> ModelExpr -> (ModelExpr -> Signature -> TC a) -> TC a
inferModelExpr pmod (ModelStruct model) kont = do
  model' <- checkModel pmod model
  msig <- naturalSignature model
  kont (ModelStruct model') msig
inferModelExpr pmod (ModelAscribe model mtypeAscribed) kont = do
  inferModelExpr pmod model $ \model' msigInferred -> do
    (mtypeAscribed', msigAscribed) <- checkModelType mtypeAscribed
    msigAscribed' <- mayAscribe msigInferred msigAscribed
    kont (ModelAscribe model' mtypeAscribed') msigAscribed'
inferModelExpr _pmod (ModelAssume modelType) kont = do
  (modelType', msig) <- checkModelType modelType
  kont (ModelAssume modelType') msig

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
              dcon = Con (IdP ident)
          sig' <- extendTypeDefnCtx dcon defn kont
          let tsd = TypeSigDecl Nothing (Just defn)
          return (TypeSig fld (U.bind (ident, U.embed tsd) sig'))

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

-- | Given the path to the module, check the declarations.
checkDecl :: Path -> Decl -> TC Decl
checkDecl pmod d =
  case d of
    TypeDefn fld td -> do
      let dcon = Con (ProjP pmod fld)
      guardDuplicateDConDecl dcon
      (td', _) <- checkTypeDefn dcon td
      return $ TypeDefn fld td'
    ValueDecl fld vd ->
      let qfld = QVar (ProjP pmod fld)
      in ValueDecl fld <$> checkValueDecl fld qfld vd

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
      let p = (ProjP pmod fld)
          shortIdent = U.s2n fld
          substitution_ = selfifyTypeDefn pmod td
          substitution = (shortIdent, p) : substitution_
          -- replace short name occurrences by the qualified name
          td' = U.substs substitution td
          rest' = U.substs substitution rest
      extendTypeDefnCtx (Con p) td' (kont rest')

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
