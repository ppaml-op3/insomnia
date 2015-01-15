{-# LANGUAGE OverloadedStrings, ViewPatterns, FlexibleContexts #-}
-- | Infer the natural signature of a module by typechecking its constituents.
--
module Insomnia.Typecheck.Module (inferModuleExpr, extendDCtx) where

import Prelude hiding (mapM_)

import Control.Applicative ((<$>))
import Control.Lens
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Monoid (Monoid(..), (<>), Endo(..))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier (Path(..), Field)
import Insomnia.Types (Kind(..), TypeConstructor(..), TypePath(..),
                       Type(..), freshUVarT)
import Insomnia.Expr (Var, Expr, TabulatedFun)
import Insomnia.ModuleType (ModuleType(..), ModuleTypeNF(..),
                            FunctorArgument(..),
                            Signature(..), TypeSigDecl(..),
                            SigV(..), sigVKind,
                            moduleTypeNormalFormEmbed)
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
import Insomnia.Typecheck.Selfify (selfifySignature)
import Insomnia.Typecheck.ClarifySignature (clarifySignatureNF)
import Insomnia.Typecheck.ExtendModuleCtx (extendModuleCtxNF)
import Insomnia.Typecheck.SigOfModuleType (signatureOfModuleType)
import Insomnia.Typecheck.LookupModuleSigPath (lookupModuleSigPath)
import Insomnia.Typecheck.ConstructImportDefinitions (constructImportDefinitions)
import Insomnia.Typecheck.MayAscribe (mayAscribeNF)
import Insomnia.Typecheck.FunctorApplication (checkFunctorApplication)

-- | Infer the signature of the given module expression
inferModuleExpr :: Path -> ModuleExpr -> (ModuleExpr -> ModuleTypeNF -> TC a) -> TC a
inferModuleExpr pmod (ModuleStruct mdl) kont = do
  mdl' <- checkModule pmod DeterministicParam mdl return
            <??@ "while checking module " <> formatErr pmod
  msig <- naturalSignature mdl'
  kont (ModuleStruct mdl') (SigMTNF (SigV msig ModuleMK))
inferModuleExpr pmod (ModuleModel mdl) kont = do
  (mdl', msig) <- checkModelExpr pmod mdl
          <??@ "while checking model " <> formatErr pmod
  kont (ModuleModel mdl') (SigMTNF (SigV msig ModelMK))
inferModuleExpr pmod (ModuleSeal mdl mtypeSealed) kont = do
  inferModuleExpr pmod mdl $ \mdl' mtnfInferred -> do
    (mtypeSealed', mtnfSealed) <-
      checkModuleType mtypeSealed
      <??@ ("while checking sealing signature of " <> formatErr pmod)
    mtnfSealed' <- mayAscribeNF mtnfInferred mtnfSealed
                   <??@ ("while checking validity of signature sealing to "
                         <> formatErr pmod)
    kont (ModuleSeal mdl' mtypeSealed') mtnfSealed'
inferModuleExpr pmod (ModuleAssume moduleType) kont = do
  (moduleType', sigV) <- checkModuleType moduleType
                         <??@ ("while checking postulated signature of "
                               <> formatErr pmod)
  kont (ModuleAssume moduleType') sigV
inferModuleExpr pmod (ModuleId modPathRHS) kont = do
  sigV <- lookupModuleSigPath modPathRHS
          <??@ ("while checking the definition of " <> formatErr pmod)
  sigV' <- clarifySignatureNF modPathRHS sigV
  kont (ModuleId modPathRHS) sigV'
inferModuleExpr pmod (ModuleApp pfun pargs) kont = do
  sigNF <- checkFunctorApplication pfun pargs
           <??@ ("while checking functor application definiing " <> formatErr pmod)
  kont (ModuleApp pfun pargs) sigNF
inferModuleExpr pmod (ModuleFun bnd) kont =
  U.lunbind bnd $ \(teleArgs, body) ->
  checkFunctorArgs pmod teleArgs $ \teleArgs' teleArgsNF -> do
    bodyName <- U.lfresh (U.s2n "<functor body>")
    inferModuleExpr (IdP bodyName) body $ \body' bodyNF ->
      kont (ModuleFun $ U.bind teleArgs' body') (FunMTNF $ U.bind teleArgsNF bodyNF)

checkModelExpr :: Path -> ModelExpr -> TC (ModelExpr, Signature)
checkModelExpr pmod mexpr =
  case mexpr of
   ModelId p -> do
     sigv <- lookupModuleSigPath p
     case sigv of
      (SigMTNF (SigV msig ModuleMK)) -> return (ModelId p, msig)
      (SigMTNF (SigV _msig ModelMK)) -> typeError ("model path " <> formatErr p
                                         <> " cannot be used in a model expression.")
      (FunMTNF {}) -> typeError ("functor path " <> formatErr p
                                 <> " cannot be used in a model expression.")
   ModelStruct mdl -> do
     mdl' <- checkModule pmod RandomVariable mdl return
             <??@ "while checking model " <> formatErr pmod
     msig <- naturalSignature mdl'
     return (ModelStruct mdl', msig)
   ModelLocal modHidden body mty -> do
     --TODO: proper error message if this is a functor
     (mty', mtnfAscribed) <- checkModuleType mty
     checkModule pmod RandomVariable modHidden $ \modHidden' -> do
       (body', sigInferred) <- checkModelExpr pmod body
       let mtnfInferred = SigMTNF (SigV sigInferred ModelMK)
       mtnfAscribed' <- mayAscribeNF mtnfInferred mtnfAscribed
                      <??@ ("while checking validity of signature ascription to body of local model in "
                            <> formatErr pmod)
       let sigAscribed = case mtnfAscribed' of
                          SigMTNF (SigV s ModelMK) -> s
                          _ -> error ("internal error: mtnfInferred may be ascribed mtnfAscribed,"
                                      ++ " but the ascribed module type isn't a model sig.")
       return (ModelLocal modHidden' body' mty', sigAscribed)

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
          sig' <- kont
          let tsd = ManifestTypeSigDecl defn
          return $ TypeSig fld (U.bind (ident, U.embed tsd) sig')
        TypeAliasDefn fld alias -> do
          let ident = U.s2n fld
          sig' <- kont
          let tsd = AliasTypeSigDecl alias
          return $ TypeSig fld (U.bind (ident, U.embed tsd) sig')
        SubmoduleDefn fld moduleExpr -> do
          -- TODO: proper error message
          submodNF <- naturalSignatureModuleExpr moduleExpr
          sig' <- kont 
          let ident = U.s2n fld
              moduleTy = moduleTypeNormalFormEmbed submodNF
          return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
        SampleModuleDefn fld moduleExpr -> do
          subSigV <- naturalSignatureModuleExpr moduleExpr
          case subSigV of
           (SigMTNF (SigV subSig ModelMK)) -> do
             sig' <- kont
             let ident = U.s2n fld
                 moduleTy = SigMT (SigV subSig ModuleMK)
             return $ SubmoduleSig fld (U.bind (ident, U.embed moduleTy) sig')
           (SigMTNF (SigV _ ModuleMK)) ->
             typeError ("(internal error?) submodule " <> formatErr fld
                        <> " unexpectedly sampled from a module, not a model")
           (FunMTNF {}) ->
             typeError ("unexpectedly submodule " <> formatErr fld
                        <> " is being sampled from a functor")
              

naturalSignatureModuleExpr :: ModuleExpr -> TC ModuleTypeNF
naturalSignatureModuleExpr (ModuleStruct mdl) = do
  modSig <- naturalSignature mdl
  return (SigMTNF (SigV modSig ModuleMK))
naturalSignatureModuleExpr (ModuleSeal _ mt) = signatureOfModuleType mt
naturalSignatureModuleExpr (ModuleAssume mt) = signatureOfModuleType mt
naturalSignatureModuleExpr (ModuleId path) = lookupModuleSigPath path
naturalSignatureModuleExpr (ModuleModel mdl) = SigMTNF <$> naturalSignatureModelExpr mdl
naturalSignatureModuleExpr (ModuleApp pfun pargs) =
  naturalSignatureFunctorApplication pfun pargs

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
  let (FunctorArgument idParam _modK _paramTy) = fa
      rest' = U.subst idParam parg rest
  in kont rest'

naturalSignatureModelExpr :: ModelExpr -> TC (SigV Signature)
naturalSignatureModelExpr (ModelId p) = do
  -- TODO: proper error message
  nf <- lookupModuleSigPath p
  case nf of
   (SigMTNF sigv) -> return (sigv & sigVKind .~ ModelMK)
   (FunMTNF {}) -> error ("internal error: naturalSignatureModelExpr got a functor path")
naturalSignatureModelExpr (ModelStruct mdl) = do
  modSig <- naturalSignature mdl
  return (SigV modSig ModelMK)
naturalSignatureModelExpr (ModelLocal _ _ mt) = do
  nf <- signatureOfModuleType mt
  case nf of
   SigMTNF sigv -> return sigv
   FunMTNF {} -> typeError ("model is ascribed a functor type " <> formatErr mt)


checkFunctorArgs :: Path -> Telescope (FunctorArgument ModuleType)
                 -> (Telescope (FunctorArgument ModuleType)
                     -> Telescope (FunctorArgument ModuleTypeNF)
                     -> TC a)
                  -> TC a
checkFunctorArgs pmod tele kont =
  case tele of
   NilT -> kont NilT NilT
   ConsT (U.unrebind -> (arg, tele')) ->
     checkFunctorArg pmod arg $ \arg' argNF ->
     checkFunctorArgs pmod tele' $ \tele'' teleNF ->
     kont (ConsT $ U.rebind arg' tele'') (ConsT $ U.rebind argNF teleNF)

checkFunctorArg :: Path
                   -> FunctorArgument ModuleType
                   -> (FunctorArgument ModuleType
                       -> FunctorArgument ModuleTypeNF
                       -> TC a)
                   -> TC a
checkFunctorArg pmod (FunctorArgument argId modK (U.unembed -> argTy)) kont = do
  (argTy', argNF) <- checkModuleType argTy
  extendModuleCtxNF (IdP argId) argNF
    $ kont (FunctorArgument argId modK (U.embed argTy')) (FunctorArgument argId modK (U.embed argNF))

-- | After checking a declaration we get one or more declarations out
-- (for example if we inferred a signature for a value binding that did not have one).
type CheckedDecl = Endo [Decl]

singleCheckedDecl :: Decl -> CheckedDecl
singleCheckedDecl d = Endo (d :)


-- | Typecheck the contents of a module.
checkModule :: Path -> Stochasticity -> Module -> (Module -> TC r) -> TC r
checkModule pmod stoch (Module ds) =
  \kont ->
   go ds $ \cd ->
   kont (Module $ checkedDeclToDecls cd)
  where
    checkedDeclToDecls :: CheckedDecl -> [Decl]
    checkedDeclToDecls = flip appEndo mempty
    go :: [Decl] -> (CheckedDecl -> TC r) -> TC r
    go [] kont = kont mempty
    go (decl:decls) kont = do
      decl' <- checkDecl pmod stoch decl
      extendDCtx pmod decl' $
        go decls $ \decls' ->
        kont (decl' <> decls')

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
    ImportDecl impPath ->
      checkImportDecl pmod stoch impPath
    TypeAliasDefn fld alias -> do
      let dcon = TCGlobal (TypePath pmod fld)
      guardDuplicateDConDecl dcon
      (alias', _) <- checkTypeAlias alias
      return $ singleCheckedDecl $ TypeAliasDefn fld alias'
    ValueDecl fld vd ->
      let v = U.s2n fld
      in checkedValueDecl fld <$> checkValueDecl fld v vd
    SubmoduleDefn fld moduleExpr -> do
      moduleExpr' <- inferModuleExpr (ProjP pmod fld) moduleExpr
                     (\moduleExpr' _sigV -> return moduleExpr')
      return $ singleCheckedDecl $ SubmoduleDefn fld moduleExpr'
    SampleModuleDefn fld moduleExpr -> do
      modExprId <- U.lfresh (U.s2n "<sampled model>")
      let modExprPath = IdP modExprId
      moduleExpr' <- inferModuleExpr modExprPath moduleExpr
                     (\moduleExpr' sigV ->
                       case sigV of
                        (SigMTNF (SigV _sig ModelMK)) -> return moduleExpr'
                        (SigMTNF (SigV _sig ModuleMK)) ->
                          typeError ("submodule " <> formatErr (ProjP pmod fld)
                                     <> " is sampled from a module, not a model")
                        (FunMTNF {}) ->
                          typeError ("submodule " <> formatErr (ProjP pmod fld)
                                     <> " is sampled from a functor, not a model"))
      return $ singleCheckedDecl $ SampleModuleDefn fld moduleExpr'

type CheckedValueDecl = Endo [ValueDecl]

checkImportDecl :: Path -> Stochasticity -> Path -> TC CheckedDecl
checkImportDecl pmod stoch impPath = do
  impSigV <- lookupModuleSigPath impPath
  case impSigV of
   (SigMTNF (SigV msig ModuleMK)) -> do
     selfSig <- selfifySignature impPath msig
     importDefns <- constructImportDefinitions selfSig
     return importDefns
   (SigMTNF (SigV _ ModelMK)) ->
     typeError ("cannot import model " <> formatErr impPath <> " into "
                <> (case stoch of
                     RandomVariable -> " model "
                     DeterministicParam -> " module ")
                <> formatErr pmod)
   (FunMTNF {}) -> 
     typeError ("cannot import functor " <> formatErr impPath <> " into "
                <> (case stoch of
                     RandomVariable -> " model "
                     DeterministicParam -> " module ")
                <> formatErr pmod)
                

checkedValueDecl :: Field -> CheckedValueDecl -> CheckedDecl
checkedValueDecl fld cd =
  -- hack
  let vds = appEndo cd []
  in Endo (map (ValueDecl fld) vds ++)
  

singleCheckedValueDecl :: ValueDecl -> CheckedValueDecl
singleCheckedValueDecl vd = Endo (vd :)



checkValueDecl :: Field -> Var -> ValueDecl -> TC CheckedValueDecl
checkValueDecl fld v vd =
  case vd of
    SigDecl stoch t -> do
      guardDuplicateValueDecl v
      singleCheckedValueDecl <$> checkSigDecl stoch t
    FunDecl body -> do
      msig <- lookupLocal v
      ensureNoDefn v
      U.avoid [U.AnyName v] $ checkFunDecl fld msig body
    ValDecl e -> do
      msig <- lookupLocal v
      ensureNoDefn v
      U.avoid [U.AnyName v] $ checkValDecl fld msig e
    SampleDecl e -> do
      msig <- lookupLocal v
      ensureNoDefn v
      U.avoid [U.AnyName v] $ checkSampleDecl fld msig e
    ParameterDecl e -> do
      msig <- lookupLocal v
      ensureNoDefn v
      U.avoid [U.AnyName v] $ checkParameterDecl fld msig e
    TabulatedSampleDecl tf -> do
      msig <- lookupLocal v
      ensureNoDefn v
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


guardDuplicateValueDecl :: Var -> TC ()
guardDuplicateValueDecl v = do
  msig <- view (envLocals . at v)
  mdef <- view (envGlobalDefns . at v)
  case (msig, mdef) of
    (Nothing, Nothing) -> return ()
    (Just _, _) -> typeError (formatErr v <> " already has a type signature")
    (_, Just _) -> typeError (formatErr v <> " already has a definition")

-- | Extend the environment by incorporating the given declaration.
extendDCtx :: Path -> CheckedDecl -> TC a -> TC a
extendDCtx pmod cd = go (appEndo cd mempty)
  where
    go :: [Decl] -> TC a -> TC a
    go [] m = m
    go (d:ds) m = extendDCtxSingle pmod d $ go ds m

extendDCtxSingle :: Path -> Decl -> TC a -> TC a
extendDCtxSingle pmod d kont =
  case d of
    ValueDecl fld vd -> extendValueDeclCtx pmod fld vd kont
    TypeDefn fld td -> do
      let shortIdent = U.s2n fld
      extendTypeDefnCtx (TCLocal shortIdent) td kont
    TypeAliasDefn fld alias -> do
      let shortIdent = U.s2n fld
      extendTypeAliasCtx (TCLocal shortIdent) alias kont
    ImportDecl {} ->
      error ("internal error: extendDCtxSingle did not expect an ImportDecl.")
    SubmoduleDefn fld moduleExpr -> do
      let shortIdent = U.s2n fld
      subSigNF <- naturalSignatureModuleExpr moduleExpr
      extendModuleCtxNF (IdP shortIdent) subSigNF kont
    SampleModuleDefn fld moduleExpr -> do
      let shortIdent = U.s2n fld
      subSigNF <- naturalSignatureModuleExpr moduleExpr
      case subSigNF of
       (SigMTNF (SigV subSig ModelMK)) ->
         -- sample a model, get a module
         let subModSigNF = SigMTNF (SigV subSig ModuleMK)
         in extendModuleCtxNF (IdP shortIdent) subModSigNF kont
       (SigMTNF (SigV _subSig ModuleMK)) ->
         typeError ("expected a model on RHS of module sampling, but got a module, when defining "
                    <> formatErr shortIdent
                    <> " in " <> formatErr pmod)
       (FunMTNF {}) ->
         typeError ("expected a model on RHS of module sampling, but got a functor, when defining "
                    <> formatErr shortIdent
                    <> " in " <> formatErr pmod)

extendValueDeclCtx :: Path -> Field -> ValueDecl -> TC a -> TC a
extendValueDeclCtx _pmod fld vd kont =
  let v = U.s2n fld :: Var
  in case vd of
    SigDecl _stoch t -> extendSigDeclCtx v t kont
    FunDecl _e -> extendValueDefinitionCtx v kont
    ValDecl _e -> extendValueDefinitionCtx v kont
    SampleDecl _e -> extendValueDefinitionCtx v kont
    ParameterDecl _e -> extendValueDefinitionCtx v kont
    TabulatedSampleDecl _tf -> extendValueDefinitionCtx v kont

-- | @extendSigDecl fld qvar ty decls checkRest@ adds the global
-- binding of @qvar@ to type @ty@, and replaces any free appearances
-- of @fld@ by @qvar@ in @decls@ before checking them using
-- @checkRest@.
extendSigDeclCtx :: Var
                    -> Type
                    -> TC a
                    -> TC a
extendSigDeclCtx v t kont =
  local (envLocals . at v ?~ t)
  . U.avoid [U.AnyName v]
  $ kont
