{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, TemplateHaskell, RankNTypes #-}
module Insomnia.SurfaceSyntax.ToAST where

import Control.Applicative (Applicative (..), (<$>))
import Control.Lens
import Control.Monad (forM)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Reader (runReader, Reader)
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.State.Class (MonadState (..))

import qualified Data.Map as M

import qualified Text.Parsec.Prim as P


import qualified Unbound.Generics.LocallyNameless as U


import Insomnia.Common.Literal
import Insomnia.Common.ModuleKind
import Insomnia.Common.Stochasticity
import qualified Insomnia.Identifier  as I
import qualified Insomnia.Expr        as I
import qualified Insomnia.Types       as I
import qualified Insomnia.TypeDefn    as I
import qualified Insomnia.ModuleType  as I
import qualified Insomnia.Module      as I
import qualified Insomnia.Toplevel    as I

import Insomnia.SurfaceSyntax.Syntax
import Insomnia.SurfaceSyntax.FixityParser

-- | Syntactic information about identifiers.
data TyIdInfo =
  TyConII (Maybe Fixity)
  deriving (Show)

data ValIdInfo =
  ValVarII (Maybe Fixity)
  | ValConII (Maybe Fixity)
  deriving (Show)

data Ctx = Ctx {_tyIdInfo :: M.Map Con TyIdInfo
                  , _valIdInfo :: M.Map QualifiedIdent ValIdInfo
                  , _currentModuleKind :: ModuleKind
                  }
            deriving (Show)

$(makeLenses ''Ctx)

-- "To AST" monad
type TA = Reader Ctx

-- the CPS version of TA
newtype CTA a = CTA { runCTA :: forall r . (a -> TA r) -> TA r }

instance Monad CTA where
  return x = CTA $ \k -> k x
  m >>= f = CTA $ \k -> runCTA m $ \x -> runCTA (f x) k

instance Applicative CTA where
  pure = return
  mf <*> mx = CTA $ \k -> runCTA mf $ \f -> runCTA mx $ \x -> k (f x)

instance Functor CTA where
  fmap f mx = CTA $ \k -> runCTA mx $ \x -> k (f x)

-- in the CPS version of TA, the Ctx is a state that persists
-- within the continuation.
instance MonadState Ctx CTA where
  state xform = CTA $ \k -> do
    ctx <- ask
    let (x, ctx') = xform ctx
    local (const ctx') $ k x

-- main function
toAST :: Toplevel -> I.Toplevel
toAST = runToAST baseCtx . toplevel
  where
    -- TODO: these really ought to be imported from somewhere, not built in.
    baseCtx = Ctx (M.fromList
                   [
                     (Con $ QId [] "->", TyConII $ Just (Fixity AssocRight 5))
                   , (Con $ QId [] "Dist", TyConII Nothing)
                   , (Con $ QId [] "Int", TyConII Nothing)
                   , (Con $ QId [] "Real", TyConII Nothing)
                   ])
                  M.empty
                  ModuleMK


runToAST :: Ctx -> TA a -> a
runToAST ctx comp = runReader comp ctx

liftCTA :: TA a -> CTA a
liftCTA comp = CTA $ \k -> comp >>= k

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
  else I.VCGlobal $ I.ValConPath (submoduleIdentPath modPath) fld

withValVar :: Ident -> TA a -> TA a
withValVar ident =
  let addVar = M.insert (QId [] ident) (ValVarII Nothing)
  in local (valIdInfo %~ addVar)

withValVars :: [Ident] -> TA a -> TA a
withValVars idents =
  let l = map (\ident -> (QId [] ident, ValVarII Nothing)) idents
      addVars = M.union (M.fromList l)
  in local (valIdInfo %~ addVars)

withValCon :: Ident -> TA a -> TA a
withValCon ident =
  let addCon = M.insert (QId [] ident) (ValConII Nothing)
  in local (valIdInfo %~ addCon)

withValCons :: [Ident] -> TA a -> TA a
withValCons idents =
  let l = map (\ident -> (QId [] ident, ValConII Nothing)) idents
      addCons = M.union (M.fromList l)
  in local (valIdInfo %~ addCons)

updateWithFixity :: Ident -> Fixity -> TA a -> TA a
updateWithFixity ident fixity =
  let setFixity (ValVarII _) = ValVarII (Just fixity)
      setFixity (ValConII _) = ValConII (Just fixity)
      qid = QId [] ident
  in local (valIdInfo . ix qid %~ setFixity)

withTyCon :: Con -> Maybe Fixity -> TA a -> TA a
withTyCon con fixity =
  let addTyCon = M.insert con (TyConII fixity)
  in local (tyIdInfo %~ addTyCon)


askTypeOperators :: TA (M.Map Con Fixity)
askTypeOperators =
  let justTypeOps (TyConII (Just fixity)) = Just fixity
      justTypeOps _                       = Nothing
  in views tyIdInfo (M.mapMaybe justTypeOps)

askValOperators :: TA (M.Map QualifiedIdent Fixity)
askValOperators =
  let justValOps (ValVarII (Just fixity)) = Just fixity
      justValOps (ValConII (Just fixity)) = Just fixity
      justValOps _                        = Nothing
  in views valIdInfo (M.mapMaybe justValOps)

askValConstructors :: TA (M.Map Con Fixity)
askValConstructors =
  let justConOps (ValConII (Just fixity)) = Just fixity
      justConOps _                        = Nothing
  in views valIdInfo (M.mapKeysMonotonic Con . M.mapMaybe justConOps)

stochasticityForModule :: ModuleKind -> Stochasticity
stochasticityForModule ModuleMK = DeterministicParam
stochasticityForModule ModelMK = RandomVariable

contextualStochasticity :: Maybe Stochasticity -> TA Stochasticity
contextualStochasticity (Just stoch) = return stoch
contextualStochasticity Nothing =
  views currentModuleKind stochasticityForModule

toplevel :: Toplevel -> TA I.Toplevel
toplevel (Toplevel items) = I.Toplevel <$> mapM toplevelItem items

toplevelItem :: ToplevelItem -> TA I.ToplevelItem
toplevelItem (ToplevelModule modK ident mmt me) = do
  ident' <- identifier ident
  me' <- local (currentModuleKind .~ modK) (moduleExpr me)
  case mmt of
   Just mt -> do
     mt' <- moduleType mt
     return $ I.ToplevelModule ident' (I.ModuleSeal me' mt')
   Nothing -> return $ I.ToplevelModule ident' me'
toplevelItem (ToplevelModuleType modK ident mt) =
  I.ToplevelModuleType
  <$> sigIdentifier ident
  <*> local (currentModuleKind .~ modK) (moduleType mt)

identifier :: Ident -> TA I.Identifier
identifier s = return $ U.s2n s

sigIdentifier :: Ident -> TA I.SigIdentifier
sigIdentifier s = return $ U.s2n s

valueField :: Ident -> TA I.Field
valueField ident = return ident

moduleField :: Ident -> TA (I.Field, I.Identifier)
moduleField ident = return (ident, U.s2n ident)

typeField :: Ident -> TA (I.Field, I.TyConName)
typeField ident = return (ident, U.s2n ident)


moduleType :: ModuleType -> TA I.ModuleType
moduleType (SigMT sig) = do
  modK <- view currentModuleKind
  let mkSig s = I.SigMT (I.SigV s modK)
  mkSig <$> (signature sig)
moduleType (IdentMT ident) = I.IdentMT <$> sigIdentifier ident

moduleExpr :: ModuleExpr -> TA I.ModuleExpr
moduleExpr (ModuleStruct mdl) = do
  modK <- view currentModuleKind
  I.ModuleStruct <$> module' mdl <*> pure modK
moduleExpr (ModuleSeal me mt) =
  I.ModuleSeal <$> moduleExpr me <*> moduleType mt
moduleExpr (ModuleAssume mt) =
  I.ModuleAssume <$> moduleType mt
moduleExpr (ModuleId qid) = return $ I.ModuleId (qualifiedIdPath qid)

signature :: Signature -> TA I.Signature
signature (Sig sigDecls) = foldr go (return I.UnitSig) sigDecls
  where
    go decl kont =
      case decl of
       ValueSig mstoch ident ty -> do
         stoch <- contextualStochasticity mstoch
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
         updateWithFixity ident fixity kont
       TypeSig ident tsd -> do
         (f, tycon) <- typeField ident
         let con = Con $ QId [] ident
         tsd' <- withTyCon con Nothing $ typeSigDecl tsd
         rest <- withTyCon con Nothing $ kont
         return $ I.TypeSig f (U.bind (tycon, U.embed tsd') rest)
       SubmoduleSig ident mt modK -> do
         (f, ident') <- moduleField ident
         mt' <- local (currentModuleKind .~ modK) (moduleType mt)
         rest <- kont
         return $ I.SubmoduleSig f (U.bind (ident', U.embed mt') rest)

module' :: Module -> TA I.Module
module' (Module decls) = I.Module <$> foldr go (return []) decls
  where
    go decl kont =
      case decl of
       ValueDecl ident vd -> do
         f <- valueField ident
         vd' <- valueDecl vd
         rest <- withValVar ident $ kont
         return (I.ValueDecl f vd' : rest)
       TypeDefn ident td -> do
         (f, _) <- typeField ident
         let con = Con $ QId [] ident
         (td', idents) <- withTyCon con Nothing $ typeDefn td
         rest <- withValCons idents $ withTyCon con Nothing $ kont
         return (I.TypeDefn f td' : rest)
       TypeAliasDefn ident alias -> do
         (f, _) <- typeField ident
         alias' <- typeAlias alias
         let con = Con $ QId [] ident
         rest <- withTyCon con Nothing $ kont
         return (I.TypeAliasDefn f alias' : rest)
       FixityDecl ident fixity ->
         updateWithFixity ident fixity $ kont
       SubmoduleDefn ident modK me -> do
         (f, _) <- moduleField ident
         me' <- local (currentModuleKind .~ modK) (moduleExpr me)
         rest <- kont
         return (I.SubmoduleDefn f me' : rest)

typeSigDecl :: TypeSigDecl -> TA I.TypeSigDecl
typeSigDecl (AbstractTypeSigDecl k) = I.AbstractTypeSigDecl <$> kind k
typeSigDecl (ManifestTypeSigDecl td) = do
  (td', _) <- typeDefn td
  return (I.ManifestTypeSigDecl td')
typeSigDecl (AliasTypeSigDecl alias) = I.AliasTypeSigDecl <$> typeAlias alias

typeAlias :: TypeAlias -> TA I.TypeAlias
typeAlias (TypeAlias tvks ty) = do
  tvks' <- forM tvks $ \(tv, k) -> (,) <$> tyvar tv <*> kind k 
  ty' <- type' ty
  return $ I.TypeAlias $ U.bind tvks' ty'

typeDefn :: TypeDefn -> TA (I.TypeDefn, [Ident])
typeDefn (DataTD dD) = do
  (dd, idents) <- dataDefn dD
  return (I.DataDefn dd, idents)
typeDefn (EnumTD n) = return (I.EnumDefn n, [])

dataDefn :: DataDefn -> TA (I.DataDefn, [Ident])
dataDefn (DataDefn tvks constrs) = do
  tvks' <- forM tvks $ \(tv, k) -> (,) <$> tyvar tv <*> kind k
  constrs' <- mapM constructorDef constrs
  let idents = map (\(ConstructorDef ident _) -> ident) constrs
  return (U.bind tvks' constrs', idents)

constructorDef :: ConstructorDef -> TA I.ConstructorDef
constructorDef (ConstructorDef ident args) = do
  let c = U.string2Name ident
  args' <- mapM type' args
  return $ I.ConstructorDef c args'

kind :: Kind -> TA I.Kind
kind KType = return I.KType
kind (KArr k1 k2) = I.KArr <$> kind k1 <*> kind k2

tyvar :: TyVar -> TA I.TyVar
tyvar (TyVar ident) = return $ U.s2n ident

type' :: Type -> TA I.Type
type' (TForall tv k ty) = do
  tv' <- tyvar tv
  k' <- kind k
  ty' <- type' ty
  return $ I.TForall (U.bind (tv', k') ty')
type' (TPhrase atms) = do
  tyOps <- askTypeOperators
  disfix atms tyOps

typeConstructor :: Con -> TA I.TypeConstructor
typeConstructor (Con (QId [] f)) = return $ I.TCLocal $ U.s2n f
typeConstructor (Con (QId (h:ps) f)) = return $ I.TCGlobal (I.TypePath path f)
  where
    path = I.headSkelFormToPath (U.s2n h,ps)

typeAtom :: TypeAtom -> TA I.Type
typeAtom (TC c) = I.TC <$> typeConstructor c
typeAtom (TV tv) = I.TV <$> tyvar tv
typeAtom (TRecord rw) = I.TRecord <$> row rw
typeAtom (TEnclosed ty mk) = do
  ty' <- type' ty
  case mk of
   Nothing -> return ty'
   Just k -> do
     k' <- kind k
     return $ I.TAnn ty' k'

row :: Row -> TA I.Row
row (Row lts) = I.Row <$> mapM labeledType lts
  where
    labeledType (l, ty) = (,) <$> pure (label l) <*> type' ty
    label = I.Label . labelName

valueDecl :: ValueDecl -> TA I.ValueDecl
valueDecl (FunDecl e) = I.FunDecl <$> expr e
valueDecl (ValDecl mstoch e) = do
  stoch <- contextualStochasticity mstoch
  case stoch of
   RandomVariable -> I.ValDecl <$> expr e
   DeterministicParam -> I.ParameterDecl <$> expr e
valueDecl (SampleDecl e) = I.SampleDecl <$> expr e
valueDecl (SigDecl mstoch ty) = do
  stoch <- contextualStochasticity mstoch
  I.SigDecl stoch <$> type' ty

annot :: Maybe Type -> TA I.Annot
annot Nothing = return $ I.Annot Nothing
annot (Just ty) = (I.Annot . Just) <$> type' ty

expr :: Expr -> TA I.Expr
expr (Lam ident mty e) = do
  let v = U.s2n ident
  ann <- annot mty
  e' <- withValVar ident $ expr e
  return $ I.Lam $ U.bind (v, U.Embed ann) e'
expr (Case e clauses) = do
  e' <- expr e
  clauses' <- traverse clause clauses
  return $ I.Case e' clauses'
expr (Let bnds e) = 
  bindings bnds $ \bnds' -> do
    e' <- expr e
    return $ I.Let $ U.bind bnds' e'
expr (Phrase atms) = do
  valOps <- askValOperators
  disfix atms valOps

valueConstructor :: Con -> TA I.ValueConstructor
valueConstructor con = do
  let qid = unCon con
  mii <- view (valIdInfo . at qid )
  case mii of
   Just (ValVarII _) -> error ("expected a value constructor, "
                               ++ " but found a variable " ++ show con)
   _ -> return $ qualifiedIdValueConstructor qid

qualifiedVar :: QVar -> TA I.QVar
qualifiedVar (QVar qid) = do
  mii <- view (valIdInfo . at qid)
  case mii of
   Just (ValConII _) ->
     error ("expected a variable, but found a value constructor " ++ show qid)
   _ -> return $ qualifiedIdQVar qid
   
unqualifiedVar :: Var -> TA I.Var
unqualifiedVar (Var ident) = do
  let q = QId [] ident
  mii <- view (valIdInfo . at q)
  case mii of
   Just (ValVarII _) -> return $ U.s2n ident
   Nothing -> return $ U.s2n ident
   Just (ValConII _) ->
     error ("expected a variable, but found a value constructor " ++ show ident)

exprNotationIdentifier :: Notation Identifier -> TA I.Expr
exprNotationIdentifier n =
  case dropNotation n of
   V v  -> I.V <$> unqualifiedVar v
   Q qv -> I.Q <$> qualifiedVar qv
   C c  -> I.C <$> valueConstructor c
  where
    dropNotation (PrefixN x) = x
    dropNotation (InfixN x) = x

exprAtom :: ExprAtom -> TA I.Expr
exprAtom (I ni) = exprNotationIdentifier ni
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

literal :: Literal -> TA Literal
literal = return

clause :: Clause -> TA I.Clause
clause (Clause pat e) = 
  runCTA (pattern pat) $ \pat' -> do
    e' <- expr e
    return $ I.Clause $ U.bind pat' e'

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

patternAtom :: PatternAtom -> CTA PartialPattern
patternAtom (VarP v) = (CompletePP . I.VarP) <$> liftCTA (unqualifiedVar v)
patternAtom (ConP ncon) = do
  let con = dropNotation ncon
      qid = unCon con
  mii <- use (valIdInfo . at qid)
  case mii of
   Just (ValConII _fix) -> (PartialPP . I.ConP . U.embed) <$> liftCTA (valueConstructor con)
   _ -> error ("in pattern expected a constructor, but got variable "
               ++ show con)
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

pattern :: Pattern -> CTA I.Pattern
pattern (PhraseP atms) = do
  valCons <- liftCTA askValConstructors
  pp <- disfix atms valCons
  return $ completePP pp


bindings :: [Binding] -> (I.Bindings -> TA a) -> TA a
bindings [] kont = kont I.NilBs
bindings (bnd:bnds) kont = 
  binding bnd $ \bnd' ->
  bindings bnds $ \bnds' ->
  kont (prependBindings bnd' bnds')
  where
    prependBindings [] ys = ys
    prependBindings (x:xs) ys = I.ConsBs $ U.rebind x (prependBindings xs ys)

binding :: Binding -> ([I.Binding] -> TA a) -> TA a
binding (SigB _ident _ty) kont = kont []
binding (ValB ident e) kont = do
  let v = U.s2n ident
  e' <- expr e
  withValVar ident $ kont [I.ValB (v, U.embed $ I.Annot Nothing) (U.embed e')]
binding (SampleB ident e) kont = do
  let v = U.s2n ident
  e' <- expr e
  withValVar ident $ kont [I.SampleB (v, U.embed $ I.Annot Nothing)
                                     (U.embed e')]
binding (TabB idtys tfs) kont = do
  -- this one is a bit tricky because the surface syntax allows
  -- multiple tabulated functions to be defined within a single "for"
  -- block, but internally we separate them into individual tabulated
  -- function bindings.
  annvs <- forM idtys $ \(ident, mty) -> do
    let v = U.s2n ident
    mty' <- traverse type' mty
    return (v, U.embed $ I.Annot mty')
  namedtfs' <- withValVars (map fst idtys) $ traverse (tabulatedFun annvs) tfs
  let (names, bnds) =
        unzip $ map (\(name, tf) -> let
                        v = U.s2n name
                        in (name,
                            I.TabB v (U.embed tf))) namedtfs'
  withValVars names $ kont bnds

tabulatedFun :: [I.AnnVar] -> TabulatedFun -> TA (Ident, I.TabulatedFun)
tabulatedFun annvs (TabulatedFun ident ts) = do
  ts' <- tabSample ts
  return (ident, I.TabulatedFun $ U.bind annvs ts')

tabSample :: TabSample -> TA I.TabSample
tabSample (TabSample selectors e) = do
  selectors' <- traverse tabSelector selectors
  e' <- expr e
  return $ I.TabSample selectors' e'

tabSelector :: TabSelector -> TA I.TabSelector
tabSelector (TabIndex ident) = return (I.TabIndex $ U.s2n ident)

---------------------------------------- Infix parsing

instance FixityParseable TypeAtom Con TA I.Type where
  term = do
    ctx <- ask
    t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
    lift $ typeAtom t
    where
      notInfix ctx t =
        case t of
         TC con -> case ctx ^. tyIdInfo . at con of
                    (Just (TyConII (Just _fixity))) -> Nothing
                    _ -> Just t
         _ -> Just t
  juxt = pure I.TApp
  infx con = do
    let match t@(TC con2) | con == con2 = Just t
        match _                         = Nothing
    _ <- P.tokenPrim show (\pos _tok _toks -> pos) match
    tOp <- lift (I.TC <$> typeConstructor con)
    return $ \t1 t2 -> I.tApps tOp [t1, t2]

instance FixityParseable ExprAtom QualifiedIdent TA I.Expr where
  term = do
    ctx <- ask
    t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
    lift $ exprAtom t
    where
      notInfix _ctx e =
        case e of
         I (InfixN _) -> Nothing
         _ -> Just e
  juxt = pure I.App
  infx qid = do
    let
      match (I (InfixN (Q qv)))
        | unQVar qv == qid          = Just (I.Q <$> qualifiedVar qv)
      match (I (InfixN (V v)))
        | (QId [] $ unVar v) == qid = Just (I.V <$> unqualifiedVar v)
      match (I (InfixN (C con)))
        | unCon con == qid          = Just (I.C <$> valueConstructor con)
      match _                                   = Nothing
    m <- P.tokenPrim show (\pos _tok _toks -> pos) match
    v <- lift $ m
    return $ \e1 e2 -> I.App (I.App v e1) e2

instance FixityParseable PatternAtom Con CTA PartialPattern where
   term = do
     ctx <- get
     t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
     lift $ patternAtom t
     where
       notInfix _ctx pa =
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
     let pat = I.ConP (U.embed con')
     -- we "know" pat is going to be a binary infix constructor
     -- because "infx" is only called by the fixity parser on infix
     -- names.
     return $ (\pp1 pp2 ->
                CompletePP $ pat [completePP pp1
                                 , completePP pp2
                                 ])
---------------------------------------- Utilities
  
disfix :: (FixityParseable tok op m t, Monad m)
          => [tok]
          -> M.Map op Fixity
          -> m t
disfix atms precs = do
  errOrOk <- runFixityParser (fixityParser precs) atms "-"
  case errOrOk of
   Left err -> error ("while resolving infix operators " ++ show err)
   Right ok -> return ok

---------------------------------------- Examples/Tests

-- TODO:

-- example1 :: () -> I.Type
-- example1 () = runReader (type' y) c
--   where
--     a = TI (QId [] "a")
--     arrow = TI (QId [] "->")
--     times = TI (QId [] "*")
--     -- a * a * a -> a * a
--     -- parsed as ((a * a) * a) -> (a * a)
--     x = TPhrase [a, times, a, times, a, arrow, a, times, a]
--     y = TForall "a" KType x
--     c = Ctx
--         (M.fromList
--          [
--            (QId [] "->", TyConII $ Just (Fixity AssocRight 5))
--          , (QId [] "*", TyConII $ Just (Fixity AssocLeft 6))
--          ]
--         )
--         M.empty

-- example2 :: () -> I.Expr
-- example2 () = runReader (expr e) ctx
--   where
--     c = I (QId [] "::")
--     n = I (QId [] "N")
--     plus = I (QId [] "+")
--     x = I (QId [] "x")
--     y = I (QId [] "y")
--     e = Phrase [x, plus, y, plus, x, c, y, plus, x, c, n]

--     ctx = Ctx
--           M.empty
--           (M.fromList
--            [
--              (QId [] "::", ValConII $ Just (Fixity AssocRight 3))
--            , (QId [] "+", ValVarII $ Just (Fixity AssocLeft 7))
--            , (QId [] "x", ValVarII Nothing)
--            , (QId [] "y", ValVarII Nothing)
--            , (QId [] "N", ValConII Nothing)
--            ]
--           )

-- example3 :: () -> I.Clause
-- example3 () = runReader (clause cls) ctx
--   where
--     c = (QId [] "::")
--     n = (QId [] "N")
--     x = (QId [] "x")
--     y = (QId [] "y")
--     p = PhraseP $ map IdP [x, c, y, c, n]
--     e = Phrase $ map I [y, c, x, c, n]
--     cls = Clause p e
--     ctx = Ctx
--           M.empty
--           (M.fromList
--            [
--              (QId [] "::", ValConII $ Just (Fixity AssocRight 3))
--            , (QId [] "N", ValConII Nothing)
--            , (QId [] "x", ValVarII Nothing) -- will be shadowed
--              -- note "y" not in scope yet.
--            ])
    
-- example4 :: () -> I.Clause
-- example4 () = runReader (clause cls) ctx
--   where
--     x = (QId [] "x")
--     p = PhraseP [IdP x]
--     e = Phrase [I x]
--     cls = Clause p e
--     ctx = Ctx
--           M.empty
--           (M.fromList
--            [
--            ])
    
