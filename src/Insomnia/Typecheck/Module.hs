{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Infer the natural signature of a module by typechecking its constituents.
--
module Insomnia.Typecheck.Module (inferModuleExpr, extendDCtx) where

import Prelude hiding (mapM_)

import Control.Applicative ((<$>))
import Control.Lens
import Control.Monad (unless)
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Monoid (Monoid(..), (<>), Endo(..))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier (Path(..), Field)
import Insomnia.Types (Kind(..), TypeConstructor(..), TypePath(..),
                       Type(..), freshUVarT)
import Insomnia.Expr (Var, QVar(..), Expr(Q), TabulatedFun)
import Insomnia.ModuleType (ModuleType(..), Signature(..), TypeSigDecl(..),
                            SigV(..), sigVKind, sigVSig)
import Insomnia.Module
import Insomnia.Pretty (Pretty, PrettyShort(..))

import Insomnia.Unify (Unifiable(..),
                       applyCurrentSubstitution,
                       solveUnification,
                       UnificationResult(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkType)
import Insomnia.Typecheck.Expr (checkExpr, checkTabulatedFunction)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn,
                                    checkTypeAlias,
                                    extendTypeDefnCtx,
                                    extendTypeAliasCtx)
import Insomnia.Typecheck.ModuleType (checkModuleType)
import Insomnia.Typecheck.Selfify (selfifyTypeDefn, selfifySignature)
import Insomnia.Typecheck.ClarifySignature (clarifySignatureV)
import Insomnia.Typecheck.ExtendModuleCtx (extendModuleCtxV, extendModuleCtx)
import Insomnia.Typecheck.SigOfModuleType (signatureOfModuleType)
import Insomnia.Typecheck.MayAscribe (mayAscribeV)

-- | Infer the signature of the given module expression
inferModuleExpr :: Path -> ModuleExpr -> (ModuleExpr -> SigV Signature -> TC a) -> TC a
inferModuleExpr pmod (ModuleStruct mdl) kont = do
  mdl' <- checkModule pmod DeterministicParam mdl return
            <??@ "while checking module " <> formatErr pmod
  msig <- naturalSignature mdl
  kont (ModuleStruct mdl') (SigV msig ModuleMK)
inferModuleExpr pmod (ModuleModel mdl) kont = do
  (mdl', msig) <- checkModelExpr pmod mdl
          <??@ "while checking model " <> formatErr pmod
  kont (ModuleModel mdl') (SigV msig ModelMK)
inferModuleExpr pmod (ModuleSeal mdl mtypeSealed) kont = do
  inferModuleExpr pmod mdl $ \mdl' sigvInferred -> do
    (mtypeSealed', sigvSealed) <-
      checkModuleType mtypeSealed
      <??@ ("while checking sealing signature of " <> formatErr pmod)
    unless (sigvSealed^.sigVKind == sigvInferred^.sigVKind) $ do
      typeError (formatErr pmod <> " is sealing a "
                 <> formatErr (sigvInferred^.sigVKind)
                 <> " as a " <> formatErr (sigvSealed^.sigVKind))
    sigvSealed' <- mayAscribeV sigvInferred sigvSealed
                   <??@ ("while checking validity of signature sealing to "
                         <> formatErr pmod)
    kont (ModuleSeal mdl' mtypeSealed') sigvSealed'
inferModuleExpr pmod (ModuleAssume moduleType) kont = do
  (moduleType', sigV) <- checkModuleType moduleType
                         <??@ ("while checking postulated signature of "
                               <> formatErr pmod)
  kont (ModuleAssume moduleType') sigV
inferModuleExpr pmod (ModuleId modPathRHS) kont = do
  sigV <- lookupModuleSigPath modPathRHS
          <??@ ("while checking the definition of " <> formatErr pmod)
  sigV' <- clarifySignatureV modPathRHS sigV
  kont (ModuleId modPathRHS) sigV'

checkModelExpr :: Path -> ModelExpr -> TC (ModelExpr, Signature)
checkModelExpr pmod mexpr =
  case mexpr of
   ModelId p -> do
     sigv <- lookupModuleSigPath p
     case sigv of
      (SigV msig ModuleMK) -> return (ModelId p, msig)
      (SigV _msig ModelMK) -> typeError ("model path " <> formatErr p
                                         <> " cannot be used in a model expression.")
   ModelStruct mdl -> do
     mdl' <- checkModule pmod RandomVariable mdl return
             <??@ "while checking model " <> formatErr pmod
     msig <- naturalSignature mdl
     return (ModelStruct mdl', msig)
   ModelLocal modHidden body mty -> do
     (mty', sigvAscribed) <- checkModuleType mty
     checkModule pmod RandomVariable modHidden $ \modHidden' -> do
       (body', sigInferred) <- checkModelExpr pmod body
       sigvSealed' <- mayAscribeV (SigV sigInferred ModelMK) sigvAscribed
                      <??@ ("while checking validity of signature ascription to body of local model in "
                            <> formatErr pmod)
       return (ModelLocal modHidden' body' mty', sigvSealed'^.sigVSig)



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
          subSigV <- naturalSignatureModuleExpr moduleExpr
          sig' <- kont 
          let ident = U.s2n fld
              moduleTy = SigMT subSigV
          return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
        SampleModuleDefn fld moduleExpr -> do
          subSigV <- naturalSignatureModuleExpr moduleExpr
          case subSigV of
           (SigV subSig ModelMK) -> do
             sig' <- kont
             let ident = U.s2n fld
                 moduleTy = SigMT (SigV subSig ModuleMK)
             return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
           (SigV _ ModuleMK) ->
             typeError ("(internal error?) submodule " <> formatErr fld
                        <> " unexpectedly sampled from a module, not a model")
              

naturalSignatureModuleExpr :: ModuleExpr -> TC (SigV Signature)
naturalSignatureModuleExpr (ModuleStruct mdl) = do
  modSig <- naturalSignature mdl
  return (SigV modSig ModuleMK)
naturalSignatureModuleExpr (ModuleSeal _ mt) = signatureOfModuleType mt
naturalSignatureModuleExpr (ModuleAssume mt) = signatureOfModuleType mt
naturalSignatureModuleExpr (ModuleId path) = lookupModuleSigPath path
naturalSignatureModuleExpr (ModuleModel mdl) = naturalSignatureModelExpr mdl

naturalSignatureModelExpr :: ModelExpr -> TC (SigV Signature)
naturalSignatureModelExpr (ModelId p) = do
  sigv <- lookupModuleSigPath p
  return (sigv & sigVKind .~ ModelMK)
naturalSignatureModelExpr (ModelStruct mdl) = do
  modSig <- naturalSignature mdl
  return (SigV modSig ModelMK)
naturalSignatureModelExpr (ModelLocal _ _ mt) =
  signatureOfModuleType mt

-- | After checking a declaration we get one or more declarations out
-- (for example if we inferred a signature for a value binding that did not have one).
type CheckedDecl = Endo [Decl]

singleCheckedDecl :: Decl -> CheckedDecl
singleCheckedDecl d = Endo (d :)

-- | Typecheck the contents of a module.
checkModule :: Path -> Stochasticity -> Module -> (Module -> TC r) -> TC r
checkModule pmod stoch (Module ds) kont =
  go ds $ \cd ->
  kont (Module $ checkedDeclToDecls cd)
  where
    checkedDeclToDecls :: CheckedDecl -> [Decl]
    checkedDeclToDecls = flip appEndo mempty
    go :: [Decl] -> (CheckedDecl -> TC r) -> TC r
    go [] kont = kont mempty
    go (decl:decls) kont = do
      decl' <- checkDecl pmod stoch decl
      extendDCtx pmod decl' decls $ \decls' ->
        go decls' $ \decls'' ->
        kont (decl' <> decls'')

checkDecl :: Path -> Stochasticity -> Decl -> TC CheckedDecl
checkDecl pmod stoch d =
  checkDecl' pmod stoch d
  <??@ "while checking " <> formatErr (PrettyShort d)

-- | Given the path to the module, check the declarations.
checkDecl' :: Path -> Stochasticity -> Decl -> TC CheckedDecl
checkDecl' pmod stoch d =
  case d of
    TypeDefn fld td -> do
      let dcon = TCGlobal (TypePath pmod fld)
      guardDuplicateDConDecl dcon
      (td', _) <- checkTypeDefn (TCLocal $ U.s2n fld) td
      return $ singleCheckedDecl $ TypeDefn fld td'
    TypeAliasDefn fld alias -> do
      let dcon = TCGlobal (TypePath pmod fld)
      guardDuplicateDConDecl dcon
      (alias', _) <- checkTypeAlias alias
      return $ singleCheckedDecl $ TypeAliasDefn fld alias'
    ValueDecl fld vd ->
      let qfld = QVar pmod fld
      in checkedValueDecl fld <$> checkValueDecl fld qfld vd
    SubmoduleDefn fld moduleExpr -> do
      moduleExpr' <- inferModuleExpr (ProjP pmod fld) moduleExpr
                     (\moduleExpr' _sigV -> return moduleExpr')
      return $ singleCheckedDecl $ SubmoduleDefn fld moduleExpr'
    SampleModuleDefn fld moduleExpr -> do
      let modExprPath = undefined -- XXX what goes here?
      moduleExpr' <- inferModuleExpr modExprPath moduleExpr
                     (\moduleExpr' sigV ->
                       case sigV of
                        (SigV _sig ModelMK) -> return moduleExpr'
                        (SigV _sig ModuleMK) ->
                          typeError ("submodule " <> formatErr (ProjP pmod fld)
                                     <> " is sampled from a module, not a model"))
      return $ singleCheckedDecl $ SampleModuleDefn fld moduleExpr'

type CheckedValueDecl = Endo [ValueDecl]

checkedValueDecl :: Field -> CheckedValueDecl -> CheckedDecl
checkedValueDecl fld cd =
  -- hack
  let vds = appEndo cd []
  in Endo (map (ValueDecl fld) vds ++)
  

singleCheckedValueDecl :: ValueDecl -> CheckedValueDecl
singleCheckedValueDecl vd = Endo (vd :)



checkValueDecl :: Field -> QVar -> ValueDecl -> TC CheckedValueDecl
checkValueDecl fld qlf vd =
  case vd of
    SigDecl stoch t -> do
      guardDuplicateValueDecl qlf
      singleCheckedValueDecl <$> checkSigDecl stoch t
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
    TabulatedSampleDecl tf -> do
      msig <- lookupGlobal qlf
      ensureNoDefn qlf
      let v = (U.s2n fld :: Var)
      U.avoid [U.AnyName v] $ checkTabulatedSampleDecl v msig tf

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

checkFunDecl :: Field -> Maybe Type -> Expr -> TC CheckedValueDecl
checkFunDecl fname mty_ e = do
  res <- solveUnification $ do
    tu <- freshUVarT
    e' <- openAbstract mty_ $ \mty -> do
      case mty of
        Just ty -> tu =?= ty
        Nothing -> return ()
      checkExpr e tu
    let
      funDecl = singleCheckedValueDecl $ FunDecl e'
    sigDecl <- case mty_ of
          Just _ -> return mempty
          Nothing -> do
            -- XXX TODO: generalize here.  Or else decree that
            -- polymorphic functions must have a type signature.
            tinf <- applyCurrentSubstitution tu
            return $ singleCheckedValueDecl $ SigDecl DeterministicParam tinf
    return (sigDecl <> funDecl)
  case res of
    UOkay ans -> return ans
    UFail err -> typeError ("when checking " <> formatErr fname
                            <> formatErr err)


-- Note that for values, unlike functions we don't generalize
checkValDecl :: Field -> Maybe Type -> Expr -> TC CheckedValueDecl
checkValDecl fld _mty _e = do
  typeError ("internal error - unexpected val decl "
             <> "(should've been translated away to a SampleDecl) while checking "
             <> formatErr fld)
  -- res <- solveUnification $ do
  --   tu <- freshUVarT
  --   case mty of
  --     Just ty -> tu =?= ty
  --     Nothing -> return ()
  --   e' <- checkExpr e tu
  --   let
  --     valDecl = singleCheckedValueDecl $ ValDecl e'
  --   sigDecl <- case mty_ of
  --         Just _ -> return mempty
  --         Nothing -> do
  --           tinf <- applyCurrentSubstitution tu
  --           -- by this point, if val decls are always parameters, "val x = e" inside models
  --           -- was turned into "val x ~ ireturn e" (ie a SampleDecl).
  --           return $ singleCheckedValueDecl $ SigDecl DeterministicParam tinf
  --   return (sigDecl <> valDecl)
  -- case res of
  --   UOkay ans -> return ans
  --   UFail err -> typeError ("when checking "<> formatErr fld
  --                           <> formatErr err)

checkSampleDecl :: Field -> Maybe Type -> Expr -> TC CheckedValueDecl
checkSampleDecl fld mty e = do
  res <- solveUnification $ do
    tu <- freshUVarT
    case mty of
      Just ty -> tu =?= ty
      Nothing -> return ()
    e' <- checkExpr e (distT tu)
    let
      sampleDecl = singleCheckedValueDecl $ SampleDecl e'
    sigDecl <- case mty of
          Just _ -> return mempty
          Nothing -> do
            tinf <- applyCurrentSubstitution tu
            return $ singleCheckedValueDecl $ SigDecl RandomVariable tinf
    return (sigDecl <> sampleDecl)
  case res of
    UOkay ans -> return ans
    UFail err -> typeError ("when checking " <> formatErr fld
                            <> formatErr err)

checkParameterDecl :: Field -> Maybe Type -> Expr -> TC CheckedValueDecl
checkParameterDecl fld mty e = do
  res <- solveUnification $ do
    tu <- freshUVarT
    case mty of
     Just ty -> tu =?= ty
     Nothing -> return ()
    e' <- checkExpr e tu
    let
      paramDecl = singleCheckedValueDecl $ ParameterDecl e'
    sigDecl <- case mty of
          Just _ -> return mempty
          Nothing -> do
            tinf <- applyCurrentSubstitution tu
            return $ singleCheckedValueDecl $ SigDecl DeterministicParam tinf
    return (sigDecl <> paramDecl)
  case res of
   UOkay ans -> return ans
   UFail err -> typeError ("when checking " <> formatErr fld
                           <> formatErr err)

checkTabulatedSampleDecl :: Var -> Maybe Type -> TabulatedFun -> TC CheckedValueDecl
checkTabulatedSampleDecl v mty tf = do
   checkTabulatedFunction v tf $ \tf' tyInferred -> do
     sigDecl <- case mty of
                 Just tySpec -> do
                   (tySpec =?= tyInferred)
                     <??@ ("while checking tabulated function definition " <> formatErr v)
                   return mempty
                 Nothing -> return $ singleCheckedValueDecl $ SigDecl RandomVariable tyInferred
     let
       tabFunDecl = singleCheckedValueDecl $ TabulatedSampleDecl tf'
     return (sigDecl <> tabFunDecl)

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
extendDCtx :: Path -> CheckedDecl -> [Decl] -> ([Decl] -> TC a) -> TC a
extendDCtx pmod cd = go (appEndo cd mempty)
  where
    go :: [Decl] -> [Decl] -> ([Decl] -> TC a) -> TC a
    go [] = \rest kont -> kont rest
    go (d:ds) = \rest kont -> extendDCtxSingle pmod d rest (\rest' -> go ds rest' kont)

extendDCtxSingle :: Path -> Decl -> [Decl] -> ([Decl] -> TC a) -> TC a
extendDCtxSingle pmod d =
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
      subSigV <- naturalSignatureModuleExpr moduleExpr
      case subSigV of
       (SigV subSig ModuleMK) -> do
         subSelfSig <- selfifySignature pSubMod subSig
         extendModuleCtx subSelfSig $ kont rest'
       (SigV _ ModelMK) ->
         kont rest'
    SampleModuleDefn fld moduleExpr -> \rest kont -> do
      let pSubMod = ProjP pmod fld
          shortIdent = U.s2n fld
          substitution = [(shortIdent, pSubMod)]
          rest' = U.substs substitution rest
      subSigV <- naturalSignatureModuleExpr moduleExpr
      case subSigV of
       (SigV subSig ModelMK) -> do
         subSelfSig <- selfifySignature pSubMod subSig
         -- XXX: not necessary since we did the substitution?
         extendModuleSigCtx shortIdent (SigV subSig ModuleMK)
           $ extendModuleCtx subSelfSig $ kont rest'
       (SigV _subSig ModuleMK) ->
         typeError ("expected a model on RHS of module sampling, but got a module, when defining "
                    <> formatErr pSubMod)

extendValueDeclCtx :: Path -> Field -> ValueDecl -> [Decl] -> ([Decl] -> TC a) -> TC a
extendValueDeclCtx pmod fld vd =
  let qvar = QVar pmod fld
  in case vd of
    SigDecl _stoch t -> extendSigDeclCtx fld qvar t
    FunDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    ValDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    SampleDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    ParameterDecl _e -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)
    TabulatedSampleDecl _tf -> \rest kont -> extendValueDefinitionCtx qvar (kont rest)

-- | @extendSigDecl fld qvar ty decls checkRest@ adds the global
-- binding of @qvar@ to type @ty@, and replaces any free appearances
-- of @fld@ by @qvar@ in @decls@ before checking them using
-- @checkRest@.
extendSigDeclCtx :: Field
                    -> QVar
                    -> Type
                    -> [Decl]
                    -> ([Decl] -> TC a)
                    -> TC a
extendSigDeclCtx fld qvar t rest kont =
  let v = U.s2n fld :: Var
  in local (envGlobals . at qvar ?~ t)
     . U.avoid [U.AnyName v]
     . kont
     $ U.subst v (Q qvar) rest
