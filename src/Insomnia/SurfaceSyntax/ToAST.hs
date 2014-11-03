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


import qualified Insomnia.Identifier  as I
import qualified Insomnia.Expr        as I
import qualified Insomnia.Types       as I
import qualified Insomnia.TypeDefn    as I
import qualified Insomnia.ModelType   as I
import qualified Insomnia.Model       as I
import qualified Insomnia.Toplevel    as I

import Insomnia.SurfaceSyntax.Syntax
import Insomnia.SurfaceSyntax.FixityParser

-- | Syntactic information about identifiers.
data TyIdInfo =
  TyConII (Maybe Fixity)
  | TyVarII
  deriving (Show)

data ValIdInfo =
  ValVarII (Maybe Fixity)
  | ValConII (Maybe Fixity)
  deriving (Show)

data Ctx = Ctx {_tyIdInfo :: M.Map QualifiedIdent TyIdInfo
                  , _valIdInfo :: M.Map QualifiedIdent ValIdInfo
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
  state transform = CTA $ \k -> do
    ctx <- ask
    let (x, ctx') = transform ctx
    local (const ctx') $ k x

-- main function
toAST :: Toplevel -> I.Toplevel
toAST = runToAST baseCtx . toplevel
  where
    -- TODO: these really ought to be imported from somewhere, not built in.
    baseCtx = Ctx (M.fromList
                   [
                     (QId [] "->", TyConII $ Just (Fixity AssocRight 5))
                   , (QId [] "Dist", TyConII Nothing)
                   , (QId [] "Int", TyConII Nothing)
                   , (QId [] "Real", TyConII Nothing)
                   ])
                  M.empty


runToAST :: Ctx -> TA a -> a
runToAST ctx comp = runReader comp ctx

liftCTA :: TA a -> CTA a
liftCTA comp = CTA $ \k -> comp >>= k

hasNoQualification :: QualifiedIdent -> Maybe Ident
hasNoQualification (QId [] ident) = Just ident
hasNoQualification _ = Nothing

qualifiedIdPath :: QualifiedIdent -> I.Path
qualifiedIdPath (QId pfx fld) = go (pfx ++ [fld])
  where
    go [] = error "can't happen"
    go (x:fs) = go' (I.IdP $ U.s2n x) fs
    go' :: I.Path -> [I.Field] -> I.Path
    go' p [] = p
    go' p (f:fs) = go' (I.ProjP p f) fs

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

withTyVar :: Ident -> TA a -> TA a
withTyVar ident =
  let addTyVar = M.insert (QId [] ident) TyVarII
  in local (tyIdInfo %~ addTyVar)

withTyVars :: [Ident] -> TA a -> TA a
withTyVars idents =
  let l = map (\ident -> (QId [] ident, TyVarII)) idents
      addTyVars = M.union (M.fromList l)
  in local (tyIdInfo %~ addTyVars)

withTyCon :: Ident -> Maybe Fixity -> TA a -> TA a
withTyCon ident fixity =
  let addTyCon = M.insert (QId [] ident) (TyConII fixity)
  in local (tyIdInfo %~ addTyCon)


askTypeOperators :: TA (M.Map QualifiedIdent Fixity)
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

toplevel :: Toplevel -> TA I.Toplevel
toplevel (Toplevel items) = I.Toplevel <$> mapM toplevelItem items

toplevelItem :: ToplevelItem -> TA I.ToplevelItem
toplevelItem (ToplevelModel ident mmt me) = do
  ident' <- identifier ident
  me' <- modelExpr me
  case mmt of
   Just mt -> do
     mt' <- modelType mt
     return $ I.ToplevelModel ident' (I.ModelAscribe me' mt')
   Nothing -> return $ I.ToplevelModel ident' me'
toplevelItem (ToplevelModelType ident mt) =
  I.ToplevelModelType <$> identifier ident <*> modelType mt

identifier :: Ident -> TA I.Identifier
identifier s = return $ U.s2n s

field :: Ident -> TA (I.Field, I.Identifier)
field ident = return (ident, U.s2n ident)

modelType :: ModelType -> TA I.ModelType
modelType (SigMT sig) = I.SigMT <$> signature sig
modelType (IdentMT ident) = I.IdentMT <$> identifier ident

modelExpr :: ModelExpr -> TA I.ModelExpr
modelExpr (ModelStruct mdl) = I.ModelStruct <$> model mdl
modelExpr (ModelAscribe me mt) =
  I.ModelAscribe <$> modelExpr me <*> modelType mt
modelExpr (ModelAssume mt) =
  I.ModelAssume <$> modelType mt
modelExpr (ModelId qid) = return $ I.ModelId (qualifiedIdPath qid)

signature :: Signature -> TA I.Signature
signature (Sig sigDecls) = foldr go (return I.UnitSig) sigDecls
  where
    go decl kont =
      case decl of
       ValueSig ident ty -> do
         (f, _) <- field ident
         ty' <- type' ty
         rest <- kont
         return $ I.ValueSig f ty' rest
       FixitySig ident fixity ->
         updateWithFixity ident fixity kont
       TypeSig ident tsd -> do
         (f, ident') <- field ident
         tsd' <- withTyCon ident Nothing $ typeSigDecl tsd
         rest <- withTyCon ident Nothing $ kont
         return $ I.TypeSig f (U.bind (ident', U.embed tsd') rest)
       SubmodelSig ident mt -> do
         (f, ident') <- field ident
         mt' <- modelType mt
         rest <- kont
         return $ I.SubmodelSig f (U.bind (ident', U.embed mt') rest)

model :: Model -> TA I.Model
model (Model decls) = I.Model <$> foldr go (return []) decls
  where
    go decl kont =
      case decl of
       ValueDecl ident vd -> do
         (f, _) <- field ident
         vd' <- valueDecl vd
         rest <- withValVar ident $ kont
         return (I.ValueDecl f vd' : rest)
       TypeDefn ident td -> do
         (f, _) <- field ident
         (td', idents) <- withTyCon ident Nothing $ typeDefn td
         rest <- withValCons idents $ withTyCon ident Nothing $ kont
         return (I.TypeDefn f td' : rest)
       TypeAliasDefn ident alias -> do
         (f, _) <- field ident
         alias' <- typeAlias alias
         rest <- withTyCon ident Nothing $ kont
         return (I.TypeAliasDefn f alias' : rest)
       FixityDecl ident fixity ->
         updateWithFixity ident fixity $ kont
       SubmodelDefn ident me -> do
         (f, _) <- field ident
         me' <- modelExpr me
         rest <- kont
         return (I.SubmodelDefn f me' : rest)

typeSigDecl :: TypeSigDecl -> TA I.TypeSigDecl
typeSigDecl (AbstractTypeSigDecl k) = I.AbstractTypeSigDecl <$> kind k
typeSigDecl (ManifestTypeSigDecl td) = do
  (td', _) <- typeDefn td
  return (I.ManifestTypeSigDecl td')
typeSigDecl (AliasTypeSigDecl alias) = I.AliasTypeSigDecl <$> typeAlias alias

typeAlias :: TypeAlias -> TA I.TypeAlias
typeAlias (TypeAlias tvks ty) = do
  tvks' <- forM tvks $ \(tv, k) -> (,) <$> tyvar (QId [] tv) <*> kind k 
  ty' <- withTyVars (map fst tvks) $ type' ty
  return $ I.TypeAlias $ U.bind tvks' ty'

typeDefn :: TypeDefn -> TA (I.TypeDefn, [Ident])
typeDefn (DataTD dD) = do
  (dd, idents) <- dataDefn dD
  return (I.DataDefn dd, idents)
typeDefn (EnumTD n) = return (I.EnumDefn n, [])

dataDefn :: DataDefn -> TA (I.DataDefn, [Ident])
dataDefn (DataDefn tvks constrs) = do
  tvks' <- forM tvks $ \(tv, k) -> (,) <$> tyvar (QId [] tv) <*> kind k
  constrs' <- withTyVars (map fst tvks) $ mapM constructorDef constrs
  let idents = map (\(ConstructorDef ident _) -> ident) constrs
  return (U.bind tvks' constrs', idents)

constructorDef :: ConstructorDef -> TA I.ConstructorDef
constructorDef (ConstructorDef ident args) = do
  let c = I.Con $ qualifiedIdPath (QId [] ident)
  args' <- mapM type' args
  return $ I.ConstructorDef c args'

kind :: Kind -> TA I.Kind
kind KType = return I.KType
kind (KArr k1 k2) = I.KArr <$> kind k1 <*> kind k2

tyvar :: QualifiedIdent -> TA I.TyVar
tyvar (QId [] nm) = return $ U.s2n nm
tyvar _ = error "unexpected qualified type variable"

qualifiedTyCon :: QualifiedIdent -> TA I.Type
qualifiedTyCon q = do
  mt <- view (tyIdInfo . at q)
  case mt of
   Just (TyConII _) -> return $ I.TC $ I.Con $ qualifiedIdPath q
   Just TyVarII -> I.TV <$> tyvar q
   _ -> error ("unbound name " ++ show q ++ " where a type was expected")

type' :: Type -> TA I.Type
type' (TForall ident k ty) = do
  tv' <- tyvar (QId [] ident)
  k' <- kind k
  ty' <- withTyVar ident $ type' ty
  return $ I.TForall (U.bind (tv', k') ty')
type' (TPhrase atms) = do
  tyOps <- askTypeOperators
  disfix atms tyOps

typeAtom :: TypeAtom -> TA I.Type
typeAtom (TI q) = qualifiedTyCon q
typeAtom (TEnclosed ty mk) = do
  ty' <- type' ty
  case mk of
   Nothing -> return ty'
   Just k -> do
     k' <- kind k
     return $ I.TAnn ty' k'

valueDecl :: ValueDecl -> TA I.ValueDecl
valueDecl (FunDecl e) = I.FunDecl <$> expr e
valueDecl (ValDecl e) = I.ValDecl <$> expr e
valueDecl (SampleDecl e) = I.SampleDecl <$> expr e
valueDecl (SigDecl ty) = I.SigDecl <$> type' ty

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

qualifiedVal :: QualifiedIdent -> TA I.Expr
qualifiedVal q = do
  mii <- view (valIdInfo . at q)
  case mii of
   Just (ValVarII _) -> (case hasNoQualification q of
                          Just ident -> return $ I.V $ U.s2n ident
                          Nothing-> return $ I.Q $ I.QVar $ qualifiedIdPath q)
   Just (ValConII _) -> return $ I.C $ I.Con $ qualifiedIdPath q
   Nothing -> error ("unknown identifier " ++ show q)
                         

exprAtom :: ExprAtom -> TA I.Expr
exprAtom (I q) = qualifiedVal q
exprAtom (Enclosed e mt) = do
  e' <- expr e
  mt' <- traverse type' mt
  case mt' of
   Nothing -> return e'
   Just ty' -> return (I.Ann e' ty')
exprAtom (L lit) = I.L <$> literal lit

literal :: Literal -> TA I.Literal
literal (IntL i) = return (I.IntL i)
literal (RealL r) = return (I.RealL r)

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

qualifiedPat :: QualifiedIdent -> CTA PartialPattern
qualifiedPat qid = do
  mii <- use (valIdInfo . at qid)
  case mii of
   Nothing -> unqual qid
   Just (ValVarII _) -> unqual qid -- shadow existing variable
   Just (ValConII mfixity) ->
     -- literal data type constructor
     return $ PartialPP $ I.ConP $ I.Con $ qualifiedIdPath qid
  where
    unqual q =
      case hasNoQualification q of
       Just ident -> do
         -- add variable to context, note that it's not infix.
         (valIdInfo . at q) .= Just (ValVarII Nothing)
         return $ CompletePP $ I.VarP (U.s2n ident)
       Nothing -> error $ "qualified variable in pattern " ++ show q

patternAtom :: PatternAtom -> CTA PartialPattern
patternAtom WildcardP = return $ CompletePP $ I.WildcardP
patternAtom (EnclosedP p) = CompletePP <$> pattern p
patternAtom (IdP qid) = qualifiedPat qid

pattern :: Pattern -> CTA I.Pattern
pattern (PhraseP atms) = do
  valOps <- liftCTA askValOperators
  pp <- disfix atms valOps
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
binding (SigB ident ty) kont = kont []
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
  let (names, bindings) =
        unzip $ map (\(name, tf) -> let
                        v = U.s2n name
                        in (name,
                            I.TabB v (U.embed tf))) namedtfs'
  withValVars names $ kont bindings

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

instance FixityParseable TypeAtom QualifiedIdent TA I.Type where
  term = do
    ctx <- ask
    t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
    lift $ typeAtom t
    where
      notInfix ctx t =
        case t of
         TI qid -> case ctx ^. tyIdInfo . at qid of
                    (Just (TyConII (Just _fixity))) -> Nothing
                    _ -> Just t
         _ -> Just t
  juxt = pure I.TApp
  infx qid = do
    tOp <- lift $ qualifiedTyCon qid
    let match t@(TI qid2) | qid == qid2 = Just t
        match _                         = Nothing
    _ <- P.tokenPrim show (\pos _tok _toks -> pos) match
    return $ \t1 t2 -> I.tApps tOp [t1, t2]

instance FixityParseable ExprAtom QualifiedIdent TA I.Expr where
  term = do
    ctx <- ask
    t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
    lift $ exprAtom t
    where
      notInfix ctx e =
        case e of
         I qid -> case ctx ^. valIdInfo . at qid of
                   (Just (ValVarII (Just _fixity))) -> Nothing
                   (Just (ValConII (Just _fixity))) -> Nothing
                   _ -> Just e
         _ -> Just e
  juxt = pure I.App
  infx qid = do
    v <- lift $ qualifiedVal qid
    let
      match e@(I qid2) | qid == qid2 = Just e
      match _                        = Nothing
    _ <- P.tokenPrim show (\pos _tok _toks -> pos) match
    return $ \e1 e2 -> I.App (I.App v e1) e2

instance FixityParseable PatternAtom QualifiedIdent CTA PartialPattern where
   term = do
     ctx <- get
     t <- P.tokenPrim show (\pos _tok _toks -> pos) (notInfix ctx)
     lift $ patternAtom t
     where
       notInfix ctx pa =
         case pa of
          WildcardP -> Just pa
          EnclosedP _ -> Just pa
          IdP qid -> case ctx ^. valIdInfo . at qid of
                      (Just (ValVarII (Just _fixity))) -> Nothing
                      (Just (ValConII (Just _fixity))) -> Nothing
                      _ -> Just pa
   juxt = pure $ \pp1 pp2 ->
     case pp1 of
      CompletePP pat1 -> error ("badly formed pattern " ++ show pat1
                                ++ show (completePP pp2))
      PartialPP patf -> PartialPP $ \rest -> patf (completePP pp2 : rest)
   infx qid = do
     let
       match pa@(IdP qid2) | qid == qid2 = Just pa
       match _                           = Nothing
     _ <- P.tokenPrim show (\pos _tok _toks -> pos) match
     pp <- lift $ qualifiedPat qid
     -- we "know" pp is going to be a PartialPP infix because "infx"
     -- is only called by the fixity parser on infix names.
     return $ (\pp1 pp2 ->
                case pp of
                 CompletePP pat -> error ("unexpected pattern "
                                          ++ show pat
                                          ++ " in infix position")
                 PartialPP pat -> CompletePP $ pat [completePP pp1
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

example1 :: () -> I.Type
example1 () = runReader (type' y) c
  where
    a = TI (QId [] "a")
    arrow = TI (QId [] "->")
    times = TI (QId [] "*")
    -- a * a * a -> a * a
    -- parsed as ((a * a) * a) -> (a * a)
    x = TPhrase [a, times, a, times, a, arrow, a, times, a]
    y = TForall "a" KType x
    c = Ctx
        (M.fromList
         [
           (QId [] "->", TyConII $ Just (Fixity AssocRight 5))
         , (QId [] "*", TyConII $ Just (Fixity AssocLeft 6))
         ]
        )
        M.empty

example2 :: () -> I.Expr
example2 () = runReader (expr e) ctx
  where
    c = I (QId [] "::")
    n = I (QId [] "N")
    plus = I (QId [] "+")
    x = I (QId [] "x")
    y = I (QId [] "y")
    e = Phrase [x, plus, y, plus, x, c, y, plus, x, c, n]

    ctx = Ctx
          M.empty
          (M.fromList
           [
             (QId [] "::", ValConII $ Just (Fixity AssocRight 3))
           , (QId [] "+", ValVarII $ Just (Fixity AssocLeft 7))
           , (QId [] "x", ValVarII Nothing)
           , (QId [] "y", ValVarII Nothing)
           , (QId [] "N", ValConII Nothing)
           ]
          )

example3 :: () -> I.Clause
example3 () = runReader (clause cls) ctx
  where
    c = (QId [] "::")
    n = (QId [] "N")
    x = (QId [] "x")
    y = (QId [] "y")
    p = PhraseP $ map IdP [x, c, y, c, n]
    e = Phrase $ map I [y, c, x, c, n]
    cls = Clause p e
    ctx = Ctx
          M.empty
          (M.fromList
           [
             (QId [] "::", ValConII $ Just (Fixity AssocRight 3))
           , (QId [] "N", ValConII Nothing)
           , (QId [] "x", ValVarII Nothing) -- will be shadowed
             -- note "y" not in scope yet.
           ])
    
example4 :: () -> I.Clause
example4 () = runReader (clause cls) ctx
  where
    x = (QId [] "x")
    p = PhraseP [IdP x]
    e = Phrase [I x]
    cls = Clause p e
    ctx = Ctx
          M.empty
          (M.fromList
           [
           ])
    
