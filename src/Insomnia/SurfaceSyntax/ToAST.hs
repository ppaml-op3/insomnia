{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses,
             ScopedTypeVariables, TemplateHaskell, RankNTypes
  #-}
module Insomnia.SurfaceSyntax.ToAST where

import Prelude hiding (foldr)
import Control.Applicative (Applicative (..), (<$>))
import Control.Lens hiding (cons)
import Control.Monad (forM)
import Control.Monad.Trans.Class (MonadTrans(..))

import Data.Foldable (Foldable(..))
import qualified Data.Map as M

import qualified Text.Parsec.Prim as P

import qualified Pipes

import qualified Unbound.Generics.LocallyNameless as U


import Insomnia.Common.Literal
import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Common.Stochasticity
import qualified Insomnia.Identifier  as I
import qualified Insomnia.Expr        as I
import qualified Insomnia.Types       as I
import qualified Insomnia.TypeDefn    as I
import qualified Insomnia.ModuleType  as I
import qualified Insomnia.Module      as I
import qualified Insomnia.Query       as I
import qualified Insomnia.Toplevel    as I

import Insomnia.SurfaceSyntax.Syntax
import Insomnia.SurfaceSyntax.FixityParser

import Insomnia.SurfaceSyntax.ToastMonad

-- TODO: these really ought to be imported from somewhere, not built in.
toASTbaseCtx :: Ctx
toASTbaseCtx = makeCtxSimple [
  (QId [] "->", Fixity AssocRight 5)
  ]

-- main function
toAST :: Monad m
         => Toplevel
         -> (ToastError -> m I.Toplevel)
         -> (ImportFileSpec -> m (Either ImportFileError Toplevel))
         -> Pipes.Effect m I.Toplevel
toAST tl onErr onImport =
  feedTA (toplevel tl) onErr onImport toASTbaseCtx


hasNoQualification :: QualifiedIdent -> Maybe Ident
hasNoQualification (QId [] ident) = Just ident
hasNoQualification _ = Nothing

submoduleIdentPath :: [Ident] -> I.Path
submoduleIdentPath [] = error "can't happen"
submoduleIdentPath (m:ms) = go (I.IdP $ U.s2n m) ms
  where
    go :: I.Path -> [I.Field] -> I.Path
    go p [] = p
    go p (f:fs) = go (I.ProjP p f) fs

qualifiedIdPath :: QualifiedIdent -> I.Path
qualifiedIdPath (QId pfx fld) = submoduleIdentPath (pfx ++ [fld])

qualifiedIdQVar :: QualifiedIdent -> I.QVar
qualifiedIdQVar (QId pfx fld) = I.QVar (submoduleIdentPath pfx) fld

qualifiedIdValueConstructor :: QualifiedIdent -> I.ValueConstructor
qualifiedIdValueConstructor (QId modPath fld) =
  if null modPath
  then I.VCLocal $ U.string2Name fld
  else I.VCGlobal (Left $ I.ValConPath (submoduleIdentPath modPath) fld)

contextualStochasticity :: Monad m => Maybe Stochasticity -> TA m Stochasticity
contextualStochasticity (Just stoch) = return stoch
contextualStochasticity Nothing =
  views currentModuleKind stochasticityForModule

toplevel :: Monad m => Toplevel -> TA m I.Toplevel
toplevel (Toplevel items) = do
  let comp = mapM toplevelItem items
  (its, imps) <- listenToplevels (runCTA comp)
  return $ I.Toplevel $ imps ++ concat its

nestedToplevel :: Monad m => Toplevel -> CTA m I.Toplevel
nestedToplevel (Toplevel items) = do
  I.Toplevel . concat <$> mapM toplevelItem items

singleton :: a -> [a]
singleton x = [x]

toplevelItem :: Monad m => ToplevelItem -> CTA m [I.ToplevelItem]
toplevelItem =
  toastPositionedC toplevelItem_

toplevelItem_ :: Monad m => ToplevelItem_ -> CTA m [I.ToplevelItem]
toplevelItem_ (ToplevelQuery qe) =
  singleton . I.ToplevelQuery <$> liftCTA (queryExpr qe)
toplevelItem_ (ToplevelImport filespec impspec) =
  toplevelImport filespec impspec
toplevelItem_ (ToplevelBigExpr ident be) = do
  be' <- liftCTA $ inferBigExpr be
  case be' of
    ModuleBV me -> do
      ident' <- liftCTA $ modIdentifier ident
      addModuleVarC ident ident'
      return $ singleton $ I.ToplevelModule ident' me
    SignatureBV mt -> do
      ident' <- liftCTA $ sigIdentifier ident
      addSignatureVarC ident ident'
      return $ singleton $ I.ToplevelModuleType ident' mt

data BigValue =
  ModuleBV I.ModuleExpr
  | SignatureBV I.ModuleType

inferBigExpr :: Monad m => BigExpr -> TA m BigValue
inferBigExpr = toastPositioned inferBigExpr_

inferBigExpr_ :: Monad m => BigExpr_ -> TA m BigValue
inferBigExpr_ (LiteralBE mk m) =
  ModuleBV . I.ModuleStruct mk <$> local (currentModuleKind .~ mk) (runCTA (module' m))
inferBigExpr_ (ClassifierBE mk sig) =
  SignatureBV . I.SigMT . flip I.SigV mk  <$> signature sig
inferBigExpr_ (AppBE qid qids) =
  return $ ModuleBV $ I.ModuleApp (qualifiedIdPath qid) (map qualifiedIdPath qids)
inferBigExpr_ (VarBE (QId [] ident)) = do
  mv <- lookupBigIdent ident
  case mv of
    Just (StructureBIS ident') -> return $ ModuleBV $ I.ModuleId (I.IdP ident')
    Just (SignatureBIS ident') -> return $ SignatureBV $ I.IdentMT (I.SigIdP ident')
    _ -> throwToastError $ " unknown whether a structure or signature: " ++ show ident
inferBigExpr_ (VarBE qid) =
  return $ ModuleBV $ I.ModuleId (qualifiedIdPath qid)
inferBigExpr_ (SealBE mbe sbe) =
  ModuleBV <$> (I.ModuleSeal <$> expectBigExprModule mbe <*> expectBigExprSignature sbe)
inferBigExpr_ (AbsBE args be) =
  runCTA $ do
    args' <- functorArguments args
    mv <- liftCTA $ inferBigExpr be
    case mv of
      ModuleBV me' -> return $ ModuleBV $ I.ModuleFun $ U.bind args' me'
      SignatureBV msig' -> return $ SignatureBV $ I.FunMT $ U.bind args' msig'
inferBigExpr_ (WhereTypeBE be wh) =
  SignatureBV <$> (I.WhereMT <$> expectBigExprSignature be <*> whereClause wh)
inferBigExpr_ (LocalBE m beMod beSig) = do
  mt' <- expectBigExprSignature beSig
  let comp = do
        hiddenMod' <- module' m
        bodyMdl' <- liftCTA $ expectBigExprModule beMod
        return $ ModuleBV $ I.ModelLocal hiddenMod' bodyMdl' mt'
  runCTA comp
inferBigExpr_ (ObserveBE beMdl obss) = do
  mdl <- expectBigExprModule beMdl
  obss' <- mapM observationClause obss
  return $ ModuleBV $ I.ModelObserve mdl obss'
inferBigExpr_ (UnpackBE e beModTy) = do
  e' <- expr e
  modTy <- expectBigExprSignature beModTy
  return $ ModuleBV $ I.ModuleUnpack e' modTy
inferBigExpr_ (AssumeBE be) =
  (ModuleBV . I.ModuleAssume) <$> expectBigExprSignature be

expectBigExprModule :: Monad m => BigExpr -> TA m I.ModuleExpr
expectBigExprModule be = do
  bv <- inferBigExpr be
  case bv of
    ModuleBV me -> return me
    SignatureBV sig -> toastNear be $ throwToastError $ "toasting expected a module but got a signature" ++ show sig

expectBigExprSignature :: Monad m => BigExpr -> TA m I.ModuleType
expectBigExprSignature be = do
  bv <- inferBigExpr be
  case bv of
    SignatureBV mt -> return mt
    ModuleBV me -> toastNear be $ throwToastError $ "toasting expected a module type, but got a module or model " ++ show me

-- an import
--   import "foo.ism" (module type T
--                     module M using N)
-- is translated into
--   toplevel ^foo "foo.ism"
--   module type T = ^foo:T
--   module M = ^foo:N
toplevelImport :: Monad m => ImportFileSpec -> [ImportSpecItem] -> CTA m [I.ToplevelItem]
toplevelImport filespec importSpecs = do
  let fp = importFileSpecPath filespec
  a <- withTopRefForC_ fp $ \a -> do
    tl <- liftCTA $ await filespec
    tl' <- nestedToplevel tl
    liftCTA $ tellToplevel fp a tl'
  its <- mapM (toplevelImportSpec a) importSpecs
  return its

toplevelImportSpec :: Monad m => I.TopRef -> ImportSpecItem -> CTA m I.ToplevelItem
toplevelImportSpec it (ImportModuleSpecItem modId fld) = do
  ident' <- liftCTA (modIdentifier modId)
  let p = I.ProjP (I.TopRefP it) fld
      -- import spec "module P using POther"
      -- becomes
      --   module P = module { import ^topref:POther }
      -- the reason that we do this, rather than
      --   module P = ^topref:POther
      -- is because we want to copy all the datatypes from POther into P, rather than
      -- merely alias them.
      reimportingModule =
        I.ModuleStruct ModuleMK $ I.Module [I.ImportDecl p]
  addModuleVarC modId ident'
  return $ I.ToplevelModule ident' reimportingModule
toplevelImportSpec it (ImportModuleTypeSpecItem sigId) = do
  sigId' <- liftCTA (sigIdentifier sigId)
  addSignatureVarC sigId sigId'
  return $ I.ToplevelModuleType sigId' (I.IdentMT $ I.SigTopRefP it sigId)

modIdentifier :: Monad m => Ident -> TA m I.Identifier
modIdentifier s = return $ U.s2n s

sigIdentifier :: Monad m => Ident -> TA m I.SigIdentifier
sigIdentifier s = return $ U.s2n s

valueField :: Monad m => Ident -> TA m I.Field
valueField ident = return ident

moduleField :: Monad m => Ident -> TA m (I.Field, I.Identifier)
moduleField ident = do
  ident' <- modIdentifier ident
  let f = ident
  return (f, ident')

typeField :: Monad m => Ident -> TA m (I.Field, I.TyConName)
typeField ident = return (ident, U.s2n ident)


whereClause :: Monad m => WhereClause -> TA m I.WhereClause
whereClause (WhereTypeCls con rhs) = do
  p <- whereClausePath (unCon con)
  rhs' <- type' rhs
  return $ I.WhereTypeCls p rhs'

whereClausePath :: Monad m => QualifiedIdent -> TA m (U.Bind I.Identifier I.TypePath)
whereClausePath (QId pfx fld) =
  let
    modId =  U.s2n "<mod>"
    path = I.headSkelFormToPath (Right modId, pfx)
  in return $ U.bind modId $ I.TypePath path fld

observationClause :: Monad m => ObservationClause -> TA m I.ObservationClause
observationClause (ObservationClause ident be) = do
  let f = ident
  m <- expectBigExprModule be
  return $ I.ObservationClause f m


functorArguments :: Monad m
                    => [(Ident, BigExpr)]
                    -> CTA m (Telescope (I.FunctorArgument I.ModuleType))
functorArguments [] = return NilT
functorArguments (arg:args) = do
  arg' <- functorArgument arg
  args' <- functorArguments args
  return (ConsT $ U.rebind arg' args')

functorArgument :: Monad m
                   => (Ident, BigExpr)
                   -> CTA m (I.FunctorArgument I.ModuleType)
functorArgument (ident, be) = do
  ident' <- liftCTA $ modIdentifier ident
  mt' <- liftCTA $ expectBigExprSignature be
  addModuleVarC ident ident'
  return $ I.FunctorArgument ident' (U.embed mt')
                       

signature :: Monad m => Signature -> TA m I.Signature
signature (Sig sigDecls) = foldr go (return I.UnitSig) sigDecls
  where
    go :: Monad m => SigDecl -> TA m I.Signature -> TA m I.Signature
    go dcl kont =
      case dcl of
       ValueSig _mstoch ident ty -> do
         -- stoch <- contextualStochasticity mstoch
         -- TODO: allow models to contain parameters
         -- and desugar from
         --   model { params ; vals ~ es }
         -- to
         --   module {
         --     module $Params { params } ;
         --     model $Model {
         --       vals ~ es[$Params.params/params]
         --     }
         --   }
         f <- valueField ident
         ty' <- type' ty
         rest <- kont
         return $ I.ValueSig f ty' rest
       FixitySig ident fixity ->
         updateWithFixity (QId [] ident) fixity kont
       TypeSig ident tsd -> do
         (f, tycon) <- typeField ident
         tsd' <- typeSigDecl tsd
         rest <- kont
         return $ I.TypeSig f (U.bind (tycon, U.embed tsd') rest)
       SubmoduleSig ident be -> do
         (f, ident') <- moduleField ident
         mt' <- expectBigExprSignature be
         rest <- kont
         return $ I.SubmoduleSig f (U.bind (ident', U.embed mt') rest)

module' :: Monad m => Module -> CTA m I.Module 
module' (Module decls) =
  (I.Module . concat) <$> mapM decl decls

decl :: Monad m => Decl -> CTA m [I.Decl]
decl d =
  case d of
   ValueDecl ident vd -> do
     f <- liftCTA $ valueField ident
     vd' <- liftCTA $ valueDecl vd
     return [I.ValueDecl f vd']
   ImportDecl qid -> do
     return [I.ImportDecl $  qualifiedIdPath qid]
   TypeDefn ident td -> do
     (f, _) <- liftCTA $ typeField ident
     (td', _idents) <- liftCTA $ typeDefn td
     return [I.TypeDefn f td']
   TypeAliasDefn ident alias -> do
     (f, _) <- liftCTA $ typeField ident
     alias' <- liftCTA $ typeAlias alias
     return [I.TypeAliasDefn f alias']
   FixityDecl ident fixity -> do
     updateWithFixityC (QId [] ident) fixity
     return []
   TabulatedSampleDecl tabD -> do
     let
       mkD f tf = I.ValueDecl f $ I.TabulatedSampleDecl tf
     tabulatedDecl tabD mkD
   BigSubmoduleDefn ident be -> do
     me' <- liftCTA $ expectBigExprModule be
     (f, ident') <- liftCTA $ moduleField ident
     addModuleVarC ident ident'
     return [I.SubmoduleDefn f me']
   BigSampleDefn ident be -> do
     me' <- liftCTA $ expectBigExprModule be
     (f, ident') <- liftCTA $ moduleField ident
     addModuleVarC ident ident'
     return [I.SampleModuleDefn f me']

typeSigDecl :: Monad m => TypeSigDecl -> TA m I.TypeSigDecl
typeSigDecl (AbstractTypeSigDecl k) = I.AbstractTypeSigDecl <$> kind k
typeSigDecl (ManifestTypeSigDecl td) = do
  (td', _) <- typeDefn td
  return (I.ManifestTypeSigDecl td')
typeSigDecl (AliasTypeSigDecl alias) = I.AliasTypeSigDecl <$> typeAlias alias

typeAlias :: Monad m => TypeAlias -> TA m I.TypeAlias
typeAlias (TypeAlias tvks ty) = do
  tvks' <- forM tvks $ \(tv, k) -> (,) <$> tyvar tv <*> kind k 
  ty' <- type' ty
  return $ I.ManifestTypeAlias (U.bind tvks' ty')

typeDefn :: Monad m => TypeDefn -> TA m (I.TypeDefn, [Ident])
typeDefn (DataTD dD) = do
  (dd, idents) <- dataDefn dD
  return (I.DataDefn dd, idents)
typeDefn (EnumTD n) = return (I.EnumDefn n, [])

dataDefn :: Monad m => DataDefn -> TA m (I.DataDefn, [Ident])
dataDefn (DataDefn tvks constrs) = do
  tvks' <- forM tvks $ \(tv, k) -> (,) <$> tyvar tv <*> kind k
  constrs' <- mapM constructorDef constrs
  let idents = map (\(ConstructorDef ident _) -> ident) constrs
  return (U.bind tvks' constrs', idents)

constructorDef :: Monad m => ConstructorDef -> TA m I.ConstructorDef
constructorDef (ConstructorDef ident args) = do
  let c = U.string2Name ident
  args' <- mapM type' args
  return $ I.ConstructorDef c args'

kind :: Monad m => Kind -> TA m I.Kind
kind KType = return I.KType
kind (KArr k1 k2) = I.KArr <$> kind k1 <*> kind k2

tyvar :: Monad m => TyVar -> TA m I.TyVar
tyvar (TyVar ident) = return $ U.s2n ident

type' :: Monad m => Type -> TA m I.Type
type' (TForall tv k ty) = do
  tv' <- tyvar tv
  k' <- kind k
  ty' <- type' ty
  return $ I.TForall (U.bind (tv', k') ty')
type' (TPhrase atms) = do
  ops <- getDeclaredFixity
  let presentOps =
        (M.fromList $ defaultInfix atms) `leftWithRightVals` (M.mapKeysMonotonic Con ops)
  disfix atms presentOps
  where
    defaultInfix =
      foldMap (\atm -> case atm of
                (TC (InfixN c)) -> [(c, Fixity AssocNone 5)]
                _ -> [])

typeConstructor :: Monad m => Con -> TA m I.TypeConstructor
typeConstructor (Con (QId [] f)) = return $ I.TCLocal $ U.s2n f
typeConstructor (Con (QId (h:ps) f)) = return $ I.TCGlobal (I.TypePath path f)
  where
    path = I.headSkelFormToPath (Right (U.s2n h),ps)

typeAtom :: Monad m => TypeAtom -> TA m I.Type
typeAtom (TC (PrefixN c)) = I.TC <$> typeConstructor c
typeAtom (TC (InfixN _)) = fail "ToAST.typeAtom InfixN can't happen"
typeAtom (TV tv) = I.TV <$> tyvar tv
typeAtom (TRecord rw) = I.TRecord <$> row rw
typeAtom (TEnclosed ty mk) = do
  ty' <- type' ty
  case mk of
   Nothing -> return ty'
   Just k -> do
     k' <- kind k
     return $ I.TAnn ty' k'
typeAtom (TPack be) = do
  s <- expectBigExprSignature be
  return $ I.TPack s

row :: Monad m => Row -> TA m I.Row
row (Row lts) = I.Row <$> mapM labeledType lts
  where
    labeledType (l, ty) = (,) <$> pure (label l) <*> type' ty
    label = I.Label . labelName

valueDecl :: Monad m => ValueDecl -> TA m I.ValueDecl
valueDecl (FunDecl e) = I.FunDecl <$> function e
valueDecl (ValDecl mstoch e) = do
  stoch <- contextualStochasticity mstoch
  case stoch of
   RandomVariable -> I.ValDecl <$> expr e
   DeterministicParam -> I.ParameterDecl <$> expr e
valueDecl (SampleDecl e) = I.SampleDecl <$> expr e
valueDecl (SigDecl mstoch ty) = do
  stoch <- contextualStochasticity mstoch
  I.SigDecl stoch <$> type' ty

queryExpr :: Monad m => QueryExpr -> TA m I.QueryExpr
queryExpr (GenSamplesQE qid params) =
  return $ I.GenSamplesQE (qualifiedIdPath qid) params


annot :: Monad m => Maybe Type -> TA m I.Annot
annot Nothing = return $ I.Annot Nothing
annot (Just ty) = (I.Annot . Just) <$> type' ty

function :: Monad m => Expr -> TA m I.Function
function = fmap (I.Function . Left) . expr

expr :: Monad m => Expr -> TA m I.Expr
expr (Lam ident mty e) = do
  let v = U.s2n ident
  ann <- annot mty
  e' <- expr e
  return $ I.Lam $ U.bind (v, U.Embed ann) e'
expr (Case e clauses) = do
  e' <- expr e
  clauses' <- traverse clause clauses
  return $ I.Case e' clauses' (I.Annot Nothing)
expr (Let bnds e) = 
  runCTA $ do
    bnds' <- bindings bnds
    e' <- liftCTA $ expr e
    return $ I.Let $ U.bind bnds' e'
expr (Phrase atms) = do
    ops <- getDeclaredFixity
    -- for any operators without a fixity, assume a default.
    let presentOps =
          (M.fromList $ defaultInfix atms) `leftWithRightVals` ops
    disfix atms presentOps
  where
    defaultInfix =
      foldMap (\atm -> case atm of
                (V (InfixN (Var qid))) -> [(qid, Fixity AssocNone 5)]
                (C (InfixN (Con qid))) -> [(qid, Fixity AssocNone 5)]
                _ -> [])

valueConstructor :: Monad m => Con -> TA m I.ValueConstructor
valueConstructor con = do
  let qid = unCon con
  return $ qualifiedIdValueConstructor qid
   
unqualifiedVar :: Monad m => Ident -> TA m I.Var
unqualifiedVar ident = return $ U.s2n ident

variableExpr :: Monad m => Var -> TA m I.Expr
variableExpr (Var qid) =
  case qid of
   (QId [] ident) -> I.V <$> unqualifiedVar ident
   _ -> return $ I.Q $ qualifiedIdQVar qid

exprAtom :: Monad m => ExprAtom -> TA m I.Expr
exprAtom (V (PrefixN v)) = variableExpr v
exprAtom (C (PrefixN c)) = I.C <$> valueConstructor c
exprAtom (V (InfixN _)) = fail "ToAST.exprAtom V InfixN can't happen"
exprAtom (C (InfixN _)) = fail "ToAST.exprAtom C InfixN can't happen"
exprAtom (Enclosed e mt) = do
  e' <- expr e
  mt' <- traverse type' mt
  case mt' of
   Nothing -> return e'
   Just ty' -> return (I.Ann e' ty')
exprAtom (Record les) = do
  les' <- forM les $ \(lbl, e) -> do
    let lbl' = I.Label (labelName lbl)
    e' <- expr e
    return (lbl', e')
  return (I.Record les')
exprAtom (L lit) = I.L <$> literal lit
exprAtom (Return eatm) = I.Return <$> exprAtom eatm
exprAtom (Pack mbe modTyBE) =
  I.Pack <$> expectBigExprModule mbe
  <*> expectBigExprSignature modTyBE

literal :: Monad m => Literal -> TA m Literal
literal = return

clause :: Monad m => Clause -> TA m I.Clause
clause (Clause pat e) = 
  let comp = do
        pat' <- pattern pat
        e' <- liftCTA (expr e)
        return $ I.Clause $ U.bind pat' e'
  in runCTA comp

-- | When we see an unqualified name "P" the surface syntax doesn't
-- tell us if "P" is a data type constructor or a variable.  If it's a
-- constructor, the internal syntax requires a list of patterns (that
-- is, @I.ConP :: I.Con -> [I.Pattern] -> I.Pattern@), but when we
-- just see the surface syntax name, we don't have "the rest" yet.  So
-- instead we say that the translation goes from surface syntax
-- pattern atoms to partial patterns.
data PartialPattern = CompletePP I.Pattern
                    | PartialPP ([I.Pattern] -> I.Pattern)

completePP :: PartialPattern -> I.Pattern
completePP (CompletePP pat) = pat
completePP (PartialPP patf) = patf []

patternAtom :: Monad m => PatternAtom -> CTA m PartialPattern
patternAtom (VarP ident) = (CompletePP . I.VarP) <$> liftCTA (unqualifiedVar ident)
patternAtom (ConP ncon) = do
  let con = dropNotation ncon
  vc <- liftCTA (valueConstructor con)
  return $ PartialPP $ I.ConP (U.embed vc) (U.embed Nothing)
  where
    dropNotation (InfixN x) = x
    dropNotation (PrefixN x) = x
patternAtom WildcardP = return $ CompletePP $ I.WildcardP
patternAtom (RecordP lps) = do
  lps' <- forM lps $ \(lbl, p) -> do
    let lbl' = I.Label (labelName lbl)
    p' <- pattern p
    return (U.embed lbl', p')
  return (CompletePP $ I.RecordP lps')
patternAtom (EnclosedP p) = CompletePP <$> pattern p

pattern :: Monad m => Pattern -> CTA m I.Pattern
pattern (PhraseP atms) = do
  ops <- getDeclaredFixityC
  let
    presentOps =
      (M.fromList $ defaultInfix atms) `leftWithRightVals` (M.mapKeysMonotonic Con ops)
  pp <- disfix atms presentOps
  return $ completePP pp
  where
    defaultInfix =
      foldMap (\atm -> case atm of
                (ConP (InfixN con)) -> [(con, Fixity AssocNone 5)]
                _ -> [])


bindings :: Monad m => [Binding] -> CTA m I.Bindings
bindings bnds_ = I.Bindings <$> go bnds_
  where
    go [] = return NilT
    go (bnd:bnds) = do
      bnd' <- binding bnd
      bnds' <- go bnds
      return (prependBindings bnd' bnds')
    prependBindings [] ys = ys
    prependBindings (x:xs) ys = ConsT $ U.rebind x (prependBindings xs ys)

binding :: Monad m => Binding -> CTA m [I.Binding]
binding (SigB _ident _ty) = return []
binding (ValB ident e) = do
  let v = U.s2n ident
  e' <- liftCTA $ expr e
  return [I.ValB (v, U.embed $ I.Annot Nothing) (U.embed e')]
binding (SampleB ident e) = do
  let v = U.s2n ident
  e' <- liftCTA $ expr e
  return [I.SampleB (v, U.embed $ I.Annot Nothing)
                                     (U.embed e')]
binding (TabB tabD) = 
  let mkB name tf = I.TabB (U.s2n name) (U.embed tf)
  in tabulatedDecl tabD mkB


tabulatedDecl :: Monad m => TabulatedDecl -> (Ident -> I.TabulatedFun -> b) -> CTA m [b]
tabulatedDecl (TabulatedDecl idtys tfs) mkB = do
  -- this one is a bit tricky because the surface syntax allows
  -- multiple tabulated functions to be defined within a single "for"
  -- block, but internally we separate them into individual tabulated
  -- function bindings.
  annvs <- forM idtys $ \(ident, mty) -> do
    let v = U.s2n ident
    mty' <- liftCTA $ traverse type' mty
    return (v, U.embed $ I.Annot mty')
  namedtfs' <- liftCTA $ traverse (tabulatedFun annvs) tfs
  let bnds = map (\(name, tf) -> mkB name tf) namedtfs'
  return bnds

tabulatedFun :: Monad m => [I.AnnVar] -> TabulatedFun -> TA m (Ident, I.TabulatedFun)
tabulatedFun annvs (TabulatedFun ident ts) = do
  ts' <- tabSample ts
  return (ident, I.TabulatedFun $ U.bind annvs ts')

tabSample :: Monad m => TabSample -> TA m I.TabSample
tabSample (TabSample selectors e) = do
  selectors' <- traverse tabSelector selectors
  e' <- expr e
  return $ I.TabSample selectors' e' (I.Annot Nothing)

tabSelector :: Monad m => TabSelector -> TA m I.TabSelector
tabSelector (TabIndex ident) = return (I.TabIndex $ U.s2n ident)

---------------------------------------- Infix parsing

-- | 'leftWithRightVals l r' is a mapping from each key 'k' in 'l'
-- to the value 'vl' in 'l', unless 'r' maps 'k' to 'vr' in which
-- case, the result maps 'k' to 'vr'.
leftWithRightVals :: Ord k => M.Map k a -> M.Map k a -> M.Map k a
leftWithRightVals =
  M.mergeWithKey (\_k _x y -> Just y) id (const M.empty)


instance Monad m => FixityParseable TypeAtom Con (TA m) I.Type where
  term = do
    t <- P.tokenPrim show (\pos _tok _toks -> pos) notInfix
    lift $ typeAtom t
    where
      notInfix t =
        case t of
         TC (InfixN _con) -> Nothing
         _ -> Just t 
  juxt = pure I.TApp
  infx con = do
    let match t@(TC (InfixN con2)) | con == con2 = Just t
        match _                                  = Nothing
    _ <- P.tokenPrim show (\pos _tok _toks -> pos) match
    tOp <- lift (I.TC <$> typeConstructor con)
    return $ \t1 t2 -> I.tApps tOp [t1, t2]

instance Monad m => FixityParseable ExprAtom QualifiedIdent (TA m) I.Expr where
  term = do
    ctx <- ask
    t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
    lift $ exprAtom t
    where
      notInfix _ctx e =
        case e of
         V (InfixN _) -> Nothing
         C (InfixN _) -> Nothing
         _ -> Just e
  juxt = pure I.App
  infx qid = do
    let
      match (V (InfixN qv))
        | unVar qv == qid   = Just (variableExpr qv)
      match (C (InfixN c))
        | unCon c == qid    = Just (I.C <$> valueConstructor c)
      match _               = Nothing
    m <- P.tokenPrim show (\pos _tok _toks -> pos) match
    v <- lift $ m
    return $ \e1 e2 -> I.App (I.App v e1) e2

instance Monad m => FixityParseable PatternAtom Con (CTA m) PartialPattern where
   term = do
     t <- P.tokenPrim show (\pos _tok _toks -> pos) notInfix
     lift $ patternAtom t
     where
       notInfix pa =
         case pa of
          ConP (InfixN _con) -> Nothing
          _ -> Just pa
   juxt = pure $ \pp1 pp2 ->
     case pp1 of
      CompletePP pat1 -> error ("badly formed pattern " ++ show pat1
                                ++ show (completePP pp2))
      PartialPP patf -> PartialPP $ \rest -> patf (completePP pp2 : rest)
   infx con = do
     let
       match pa@(ConP (InfixN con2)) | con == con2 = Just pa
       match _                                     = Nothing
     _ <- P.tokenPrim show (\pos _tok _toks -> pos) match
     con' <- lift $ liftCTA $ valueConstructor con
     let pat = I.ConP (U.embed con') (U.embed Nothing)
     -- we "know" pat is going to be a binary infix constructor
     -- because "infx" is only called by the fixity parser on infix
     -- names.
     return $ (\pp1 pp2 ->
                CompletePP $ pat [completePP pp1
                                 , completePP pp2
                                 ])
---------------------------------------- Utilities
  
disfix :: (FixityParseable tok op m t, Monad m, Show tok)
          => [tok]
          -> M.Map op Fixity
          -> m t
disfix atms precs = do
  errOrOk <- runFixityParser (fixityParser precs) atms "-"
  case errOrOk of
   Left err -> error ("while resolving infix operators " ++ show err)
   Right ok -> return ok

---------------------------------------- Examples/Tests

runInfixResolutionTest :: TA Identity a -> Ctx -> a
runInfixResolutionTest comp ctx =
  runIdentity $ Pipes.runEffect $ feedTA comp onErr handler ctx
  where
    onErr = fail . show
    handler _ = return $ Left $ ImportFileError "did not expect an import"

example1 :: () -> I.Type
example1 () = runInfixResolutionTest (type' y) c
  where
    a = TV (TyVar "a")
    arrow = TC (InfixN $ Con $ QId [] "->")
    times = TC (InfixN $ Con $ QId [] "*")
    -- a * a * a -> a * a
    -- parsed as ((a * a) * a) -> (a * a)
    x = TPhrase [a, times, a, times, a, arrow, a, times, a]
    y = TForall (TyVar "a") KType x
    c = makeCtxSimple
        [ (QId [] "->", Fixity AssocRight 5)
        , (QId [] "*", Fixity AssocLeft 6)
        ]
    
example1_expected :: I.Type
example1_expected =
  forall a (v a `prod` v a `prod` v a
            `funTo`
            v a `prod` v a)
  where
    a = U.s2n "a"
    v = I.TV
    prod x y = I.tApps (I.TC $ I.TCLocal $ U.s2n "*") [x, y]
    funTo x y = I.tApps (I.TC $ I.TCLocal $ U.s2n "->") [x, y]
    forall x t = I.TForall (U.bind (x, I.KType) t)
    infixr 5 `funTo`
    infixl 6 `prod`

example2 :: () -> I.Expr
example2 () = runInfixResolutionTest (expr e) ctx
  where
    c = C (InfixN $ Con $ QId [] "Cons")
    n = C (PrefixN $ Con $ QId [] "N")
    plus = V (InfixN $ Var $ QId [] "+")
    x = V (PrefixN $ Var $ QId [] "x")
    y = V (PrefixN $ Var $ QId [] "y")
    e = Phrase [x, plus, y, plus, x, c, y, plus, x, c, n]

    ctx = makeCtxSimple
          [  (QId [] "Cons", Fixity AssocRight 3)
          , (QId [] "+", Fixity AssocLeft 7)
          ]
    
example2_expected :: I.Expr
example2_expected =
  v x .+. v y .+. v x `cons` v y .+. v x `cons` n
  where
    v = I.V
    x = U.s2n "x"
    y = U.s2n "y"
    n = I.C $ I.VCLocal $ U.s2n "N"
    cons h t = I.App (I.App (I.C $ I.VCLocal $ U.s2n "Cons") h) t
    e1 .+. e2 = I.App (I.App (I.V $ U.s2n "+") e1) e2
    infixr 3 `cons`
    infixl 7 .+.

example3 :: () -> I.Clause
example3 () = runInfixResolutionTest (clause cls) ctx
  where
    (cp, c) = let q = (InfixN $ Con $ QId [] "Cons")
              in (ConP q, C q)
    (np, n) = let q = (PrefixN $ Con $ QId [] "N")
              in (ConP q, C q)
    (xp, x) = let q = "x"
              in (VarP q, V $ PrefixN $ Var $ QId [] q)
    (yp, y) = let q = "y"
              in (VarP q, V $ PrefixN $ Var $ QId [] q)
    p = PhraseP [xp, cp, yp, cp, np]
    e = Phrase [y, c, x, c, n]
    cls = Clause p e
    ctx = makeCtxSimple
          [ (QId [] "Cons", Fixity AssocRight 3)
          ]
    
example3_expected :: I.Clause
example3_expected =
  I.Clause $ U.bind p e
  where
    p = consp xp (consp yp np)
    e = cons (v y) (cons (v x) n)

    consp p1 p2 = I.ConP (U.embed consc) (U.embed Nothing) [p1, p2]
    cons e1 e2 = I.App (I.App (I.C consc) e1) e2
    consc = I.VCLocal $ U.s2n "Cons"
    np = I.ConP (U.embed nc) (U.embed Nothing) []
    n = I.C nc
    nc = I.VCLocal $ U.s2n "N"
    x = U.s2n "x"
    y = U.s2n "y"
    xp = I.VarP x
    yp = I.VarP y
    v = I.V

example4 :: () -> I.Clause
example4 () = runInfixResolutionTest (clause cls) ctx
  where
    cls = Clause p e
    p = PhraseP [xp]
    e = Phrase [x]
    
    (xp, x) = let q = "x"
              in (VarP q, V $ PrefixN $ Var $ QId [] q)
    ctx = makeCtxSimple []
    
example4_expected :: I.Clause
example4_expected =
  I.Clause $ U.bind p e
  where
    p = xp
    e = v x
    x = U.s2n "x"
    xp = I.VarP x
    v = I.V
