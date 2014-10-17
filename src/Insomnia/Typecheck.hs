{-# LANGUAGE OverloadedStrings,
             FlexibleInstances, MultiParamTypeClasses,
             ViewPatterns,
             TemplateHaskell
  #-}
module Insomnia.Typecheck where

import Control.Lens
import Control.Applicative ((<$>))
import Control.Monad (forM, unless, void, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Error.Class (MonadError(..))
import Data.List (foldl')
import Data.Format (Format(..))
import qualified Data.Format as F
import qualified Data.Map as M
import Data.Monoid (Monoid(..), (<>), First(..))

import qualified Unbound.Generics.LocallyNameless as U

import Unbound.Generics.LocallyNameless.LFresh (LFreshMT, runLFreshMT)

import Insomnia.Types
import Insomnia.Expr
import Insomnia.Model
import Insomnia.Unify
import Insomnia.Pretty
import Insomnia.Except (Except, runExcept)

newtype TCError = TCError { getTCError :: F.Doc }

instance Format TCError where
  format = format . getTCError

type ConstructorArgs = (U.Bind [KindedTVar] [Type])

-- each constructor C of algebraic datatype D has the form:
--  ∀ (α₁ ∷ K₁, … αᵢ ∷ Kᵢ) . T₁ → T₂ → ⋯ → D α₁ ⋯ αᵢ
-- (if we add GADTs, there will also be existential β vars and
-- equality constraints.  In any case, D will always be applied to exactly
-- the αs and we don't bother storing the whole application.  Just the head
-- data constructor D.)
data AlgConstructor =
  AlgConstructor {
    _algConstructorArgs :: ConstructorArgs
    , _algConstructorDCon :: Con
    }

data AlgType =
  AlgType {
    _algTypeParams :: [Kind] -- ^ the ADT is parametric, having kind κ1→⋯→κN→⋆
    , _algTypeCons :: [Con] -- ^ the names of the constructors in this kind.
    }

-- | Types that arise as a result of checking a declaration.  Each
-- declaration gives rise to a new type that is distinct even from
-- other declarations that appear structurally equivalent.  (Formally
-- these may be modeled by singleton kinds or by definitions in a
-- typing context.)
data GenerativeType =
  AlgebraicType !AlgType -- ^ an (AlgebraicType κs) declares a type of kind κ1 → ⋯ → κN → ⋆
  | EnumerationType !Nat -- ^ a finite enumeration type of N elements
--   | RecordType Rows -- ^ a record type with the given rows


$(makeLenses ''AlgConstructor)
$(makeLenses ''AlgType)
  
-- | Typechecking environment
data Env = Env { _envDCons :: M.Map Con GenerativeType -- ^ data types
               , _envCCons :: M.Map Con AlgConstructor -- ^ value constructors
               , _envGlobals :: M.Map Var Type      -- ^ declared global vars
               , _envGlobalDefns :: M.Map Var ()    -- ^ defined global vars
               , _envTys :: M.Map TyVar Kind        -- ^ local type variables
               , _envLocals :: M.Map Var Type       -- ^ local value variables
               , _envVisibleSelector :: M.Map Var () -- ^ local vars that may be used as indices of tabulated functions.  (Come into scope in "forall" expressions)
               }

$(makeLenses ''Env)

-- | The empty typechecking environment
emptyEnv :: Env
emptyEnv = Env mempty mempty mempty mempty mempty mempty mempty

-- | Base environment with builtin types.
baseEnv :: Env
baseEnv = emptyEnv
          & (envDCons . at conArrow) .~ Just (AlgebraicType algArrow)
          & (envDCons . at conDist) .~ Just (AlgebraicType algDist)
          & (envDCons . at conInt) .~ Just (AlgebraicType algInt)
          & (envDCons . at conReal) .~ Just (AlgebraicType algReal)

-- | Base data constructors
conArrow :: Con
conArrow = Con "->"

conDist :: Con
conDist = Con "Dist"

conInt :: Con
conInt = Con "Int"

conReal :: Con
conReal = Con "Real"

algArrow :: AlgType
algArrow = AlgType [KType, KType] []

algDist :: AlgType
algDist = AlgType [KType] []

algInt :: AlgType
algInt = AlgType [] []

algReal :: AlgType
algReal = AlgType [] []

functionT :: Type -> Type -> Type
functionT t1 t2 = TC conArrow `TApp` t1 `TApp` t2

functionT' :: [Type] -> Type -> Type
functionT' [] _tcod = error "expected at least one domain type"
functionT' [tdom] tcod = functionT tdom tcod
functionT' (tdom:tdoms) tcod = functionT tdom (functionT' tdoms tcod)

distT :: Type -> Type
distT tsample = TC conDist `TApp` tsample

intT :: Type
intT = TC conInt

realT :: Type
realT = TC conReal


-- | The typechecking monad sand unification
type TCSimple = ReaderT Env (LFreshMT (Except TCError))

-- | The typechecking monad
type TC = UnificationT Type TCSimple

-- instance MonadUnificationExcept Type TCSimple
instance MonadUnificationExcept TypeUnificationError Type (ReaderT Env (LFreshMT (Except TCError))) where
  throwUnificationFailure = throwError . TCError . formatErr

-- | Run a typechecking computation
runTC :: TC a -> Either TCError (a, M.Map (UVar Type) Type)
runTC comp =
  runExcept $ runLFreshMT $ runReaderT (runUnificationT comp) baseEnv

-- | Check that a kind is well-formed.  Note that for now, all kinds
-- are well-formed.
checkKind :: Kind -> TC ()
checkKind _k = return ()

-- | The subkinding relation. For our simple kinds it is reflexive.
isSubkind :: Kind -> Kind -> Bool
isSubkind = U.aeq

-- | Look up info about a datatype
lookupDCon :: Con -> TC GenerativeType
lookupDCon d = do
  m <- view (envDCons . at d)
  case m of
    Just k -> return k
    Nothing -> typeError $ "no data type " <> formatErr d

lookupCCon :: Con -> TC AlgConstructor
lookupCCon c = do
  m <- view (envCCons . at c)
  case m of
    Just constr -> return constr
    Nothing -> typeError $ "no datatype defines a constructor " <> formatErr c

-- | Lookup the kind of a type variable
lookupTyVar :: TyVar -> TC Kind
lookupTyVar tv = do
  m <- view (envTys . at tv)
  case m of
    Just k -> return k
    Nothing -> typeError $ "no type variable " <> formatErr tv

lookupGlobal :: Var -> TC (Maybe Type)
lookupGlobal v = view (envGlobals . at v)

lookupLocal :: Var -> TC (Maybe Type)
lookupLocal v = view (envLocals . at v)

lookupVar :: Var -> TC (Maybe Type)
lookupVar v = do
  tl <- First <$> lookupLocal v
  tg <- First <$> lookupGlobal v
  return $ getFirst (tl <> tg)

-- | ensure that the first kind is a subtype of the second.
ensureSubkind :: (Type, Kind) -> Kind -> TC ()
ensureSubkind (tblame, ksub) ksup =
  if (isSubkind ksub ksup)
  then return ()
  else typeError (formatErr tblame
                  <> " has kind "
                  <> formatErr ksub
                  <> " which is not a subkind of "
                  <> formatErr ksup)

-- | Ensure that the given kind is of the form (k1 → k2).
ensureKArr :: Kind -> Type -> TC (Kind, Kind)
ensureKArr k t =
  case k of
    KType -> typeError ("expected an arrow kind, got ⋆ when checking"
                        <> formatErr t)
    KArr k1 k2 -> return (k1, k2)

ensureNoDefn :: Var -> TC ()
ensureNoDefn v = do
  m <- view (envGlobalDefns . at v)
  case m of
    Just () -> typeError ("duplicate defintion of " <> formatErr v)
    Nothing -> return ()

ensureVisibleSelector :: Var -> TC ()
ensureVisibleSelector v = do
  m <- view (envVisibleSelector . at v)
  case m of
    Just () -> return ()
    Nothing -> typeError (formatErr v
                          <> " is not a selector from "
                          <> "the immediately enclosing 'forall'")

inferGenerativeType :: GenerativeType -> TC Kind
inferGenerativeType (AlgebraicType algTy) =
  let k = foldr KArr KType (algTy^.algTypeParams)
  in return k
inferGenerativeType (EnumerationType {}) = return KType
  

-- | Check that a type has the given kind
checkType :: Type -> Kind -> TC Type
checkType t k = do
  tk@(t', _) <- inferType t
  ensureSubkind tk k
  return t'

-- | Given a type, infer its kind.
inferType :: Type  -> TC (Type, Kind)
inferType t =
  case t of
    TC dcon -> do
      gt <- lookupDCon dcon
      k' <- inferGenerativeType gt
      return (t,k')
    TUVar u -> typeError ("unexpected unification variable "
                          <> formatErr u)
    TV v -> do
      k' <- lookupTyVar v
      return (t, k')
    TAnn t1 k1 -> do
      checkKind k1
      t1' <- checkType t1 k1
      return (TAnn t1' k1, k1)
    TApp t1 t2 -> do
      (t1', k1) <- inferType t1
      (k1dom, k1cod) <- ensureKArr k1 t
      t2' <- checkType t2 k1dom
      return (TApp t1' t2', k1cod)
    TForall bnd -> do
      U.lunbind bnd $ \((v, kdom), tcod) -> do
        checkKind kdom
        tcod' <- extendTyVarCtx v kdom $ checkType tcod KType
        return (TForall (U.bind (v, kdom) tcod'), KType)        

checkDecl :: Decl -> TC Decl
checkDecl d =
  case d of
    TypeDecl td -> TypeDecl <$> checkTypeDecl td
    ValueDecl vd -> ValueDecl <$> checkValueDecl vd

checkTypeDecl :: TypeDecl -> TC TypeDecl
checkTypeDecl td =
  case td of
    DataDecl dcon constrs -> checkDataDecl dcon constrs
    EnumDecl dcon n -> checkEnumDecl dcon n


checkValueDecl :: ValueDecl -> TC ValueDecl
checkValueDecl vd =
  case vd of
    SigDecl v t -> checkSigDecl v t
    FunDecl v e -> checkFunDecl v e
    ValDecl v e -> checkValDecl v e
    SampleDecl v e -> checkSampleDecl v e

guardDuplicateValueDecl :: Var -> TC ()
guardDuplicateValueDecl v = do
  msig <- view (envGlobals . at v)
  mdef <- view (envGlobalDefns . at v)
  case (msig, mdef) of
    (Nothing, Nothing) -> return ()
    (Just _, _) -> typeError (formatErr v <> " already has a type signature")
    (_, Just _) -> typeError (formatErr v <> " already has a definition")

guardDuplicateDConDecl :: Con -> TC ()
guardDuplicateDConDecl dcon = do
  mdata <- view (envDCons . at dcon)
  case mdata of
    Nothing -> return ()
    Just _ -> typeError ("data type "
                         <> formatErr dcon
                         <> " is already defined")

guardDuplicateCConDecl :: Con -> TC ()
guardDuplicateCConDecl ccon = do
  mcon <- view (envCCons . at ccon)
  case mcon of
    Nothing -> return ()
    Just _ -> typeError ("value constructor "
                         <> formatErr ccon
                         <> " is already defined")

checkSigDecl :: Var -> Type -> TC ValueDecl
checkSigDecl v t = do
  guardDuplicateValueDecl v
  t' <- checkType t KType
  return $ SigDecl v t'

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

-- | Given a type ∀ α1∷K1 ⋯ αN∷KN . τ, pick fresh unification vars u1,…,uN
-- and pass τ[u/α] to the given continuation.
instantiate :: Type -> (Type -> TC a) -> TC a
instantiate ty kont =
  case ty of
    TForall bnd -> U.lunbind bnd $ \ ((tv, _), ty') -> do
      tu <- TUVar<$> unconstrained
      instantiate (U.subst tv tu ty') kont
    _ -> kont ty

-- | Given α1∷ ⋯ αN.KN . 〈τ1, …, τM〉, pick fresh unification vars u1,…,uN
-- and pass 〈u1,…,uN〉 and 〈τ1[u/α], …, τM[u/α]〉 to the continuation
instantiateConstructorArgs :: ConstructorArgs -> ([Type] -> [Type] -> TC a) -> TC a
instantiateConstructorArgs bnd kont =
  U.lunbind bnd $ \ (tvks, targs) -> do
    tus <- mapM (\_-> freshUVarT) tvks
    -- the substitution taking each variable to a fresh unification var
    let
      s = zip (map fst tvks) tus
      targs' = U.substs s targs
    kont tus targs'

-- | Given a value constructor c, return its type as a polymorphic function
--   (that is, ∀ αs . T1(αs) → ⋯ → TN(αs) → D αs)
mkConstructorType :: AlgConstructor -> TC Type
mkConstructorType constr = 
  -- XX could do unsafeBunbind here for working under the binder.
  U.lunbind (constr^.algConstructorArgs) $ \ (tvks, targs) -> do
  let tvs = map (TV . fst) tvks
      d = constr^.algConstructorDCon
      -- data type applied to the type variables - D α1 ⋯ αK
      dt = foldl' TApp (TC d) tvs
      -- arg1 → (arg2 → ⋯ (argN → D αs))
      ty = foldr functionT dt targs
  -- ∀ αs . …
  return $ go ty tvks
  where
    go t [] = t
    go t (tvk:tvks) = go (TForall (U.bind tvk t)) tvks

checkFunDecl :: Var -> Expr -> TC ValueDecl
checkFunDecl v e = do
  msig_ <- lookupGlobal v
  ensureNoDefn v
  res <- solveUnification $ do
    tu <- freshUVarT
    openAbstract msig_ $ \msig -> do
      case msig of
        Just ty -> tu =?= ty
        Nothing -> return ()
      U.avoid [U.AnyName v] $ checkExpr e tu
  case res of
    UOkay e' -> return $ FunDecl v e'
    UFail err -> typeError ("when checking " <> formatErr v
                            <> formatErr err)

-- Note that for values, unlike functions we don't generalize
checkValDecl :: Var -> Expr -> TC ValueDecl
checkValDecl v e = do
  msig <- lookupGlobal v
  ensureNoDefn v
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
      Just ty -> tu =?= ty
      Nothing -> return ()
    U.avoid [U.AnyName v] $ checkExpr e tu
  case res of
    UOkay e' -> return $ ValDecl v e'
    UFail err -> typeError ("when checking "<> formatErr v
                            <> formatErr err)

checkSampleDecl :: Var -> Expr -> TC ValueDecl
checkSampleDecl v e = do
  msig <- lookupGlobal v
  ensureNoDefn v
  res <- solveUnification $ do
    tu <- freshUVarT
    case msig of
      Just ty -> tu =?= ty
      Nothing -> return ()
    U.avoid [U.AnyName v] $ checkExpr e (distT tu)
  case res of
    UOkay e' -> return $ SampleDecl v e'
    UFail err -> typeError ("when checking " <> formatErr v
                            <> formatErr err)

checkDataDecl :: Con -> DataDecl -> TC TypeDecl
checkDataDecl dcon bnd = do
  guardDuplicateDConDecl dcon
  U.lunbind bnd $ \ (vks, constrs) -> do
    -- k1 -> k2 -> ... -> *
    let kparams = map snd vks
        cs = map (\(ConstructorDef c _) -> c) constrs
        algty = AlgType kparams cs
    mapM_ checkKind kparams
    constrs' <- extendDConCtx dcon (AlgebraicType algty)
                $ extendTyVarsCtx vks $ forM constrs checkConstructor
    return $ DataDecl dcon $ U.bind vks constrs'

checkEnumDecl :: Con -> Nat -> TC TypeDecl
checkEnumDecl dcon n = do
  guardDuplicateDConDecl dcon
  unless (n > 0) $ do
    typeError ("when checking declaration of enumeration type "
               <> formatErr dcon
               <> " the number of elements "
               <> formatErr n <> "was negative")
  return $ EnumDecl dcon n

checkConstructor :: ConstructorDef -> TC ConstructorDef
checkConstructor (ConstructorDef ccon args) = do
  guardDuplicateCConDecl ccon
  args' <- forM args $ \arg -> checkType arg KType
  return (ConstructorDef ccon args')

unifyAnn :: Type -> Annot -> TC ()
unifyAnn t1 (Annot (Just t2)) = do
  t2' <- checkType t2 KType
  t1 =?= t2'
unifyAnn _ _ = return ()

unifyFunctionT :: Type -> TC (Type, Type)
unifyFunctionT t = do
  tdom <- freshUVarT
  tcod <- freshUVarT
  t =?= functionT tdom tcod
  return (tdom, tcod)

unifyDistT :: Type -> TC Type
unifyDistT t = do
  tsample <- freshUVarT
  t =?= distT tsample
  return tsample

checkLiteral :: Literal -> Type -> TC ()
checkLiteral (IntL {}) t = t =?= intT
checkLiteral (RealL {}) t = t =?= realT

checkExpr :: Expr -> Type -> TC Expr
checkExpr e_ t_ = case e_ of
  Lam bnd ->
    U.lunbind bnd $ \ ((v, U.unembed -> ann), e) -> do
      (tdom, tcod) <- unifyFunctionT t_
      unifyAnn tdom ann
      e' <- extendLocalCtx v tdom $ checkExpr e tcod
      tannot <- applyCurrentSubstitution tdom
      return $ Lam (U.bind (v, U.embed $ Annot $ Just tannot) e')
  L l -> do
    checkLiteral l t_
    return (L l)
  V v -> do
    mt <- lookupVar v
    case mt of
      Nothing -> typeError ("unbound variable " <> formatErr v)
      Just tv -> instantiate tv $ \t' -> do
        t_ =?= t'
        return $ V v
  C c -> do
    constr <- lookupCCon c
    ty <- mkConstructorType constr
    instantiate ty $ \ty' -> do
      ty' =?= t_
      return $ C c
  App e1_ e2_ -> do
    (t1, e1') <- inferExpr e1_
    (tdom, tcod) <- unifyFunctionT t1
    e2' <- checkExpr e2_ tdom
    tcod =?= t_
    return $ App e1' e2'
  Let bnd ->
    U.lunbind bnd $ \(binds, body) ->
    checkBindings binds $ \ binds' -> do
      body' <- checkExpr body t_
      return $ Let $ U.bind binds' body'
  Case scrut clauses -> do
    (tscrut, scrut') <- inferExpr scrut
    clauses' <- forM clauses (checkClause tscrut t_)
    return $ Case scrut' clauses'
  Ann e1_ t1_ -> do
    t1 <- checkType t1_ KType
    e1 <- checkExpr e1_ t1
    t1 =?= t_
    return (Ann e1 t1)

-- | check that the give clause scrutenized the given type and returns
-- a result of the expected result type.
checkClause :: Type -> Type -> Clause -> TC Clause
checkClause tscrut texp (Clause bnd) =
  U.lunbind bnd $ \ (pat, expr) -> do
    (pat', match) <- checkPattern tscrut pat
    expr' <- extendMatchCtx match $ checkExpr expr texp
    return $ Clause $ U.bind pat' expr'

type PatternMatch = [(Var, Type)]

checkPattern :: Type -> Pattern -> TC (Pattern, PatternMatch)
checkPattern tscrut p =
  case p of
    WildcardP -> return (p, [])
    VarP v -> return (p, [(v, tscrut)])
    ConP c ps -> do
      alg <- lookupCCon c
      instantiateConstructorArgs (alg^.algConstructorArgs) $ \ tparams targs -> do
        unless (length ps == length targs) $
          typeError ("constructor " <> formatErr c
                     <> " should take " <> formatErr (length targs)
                     <> " arguments, but pattern matches "
                     <> formatErr (length ps)
                     <> " arguments")
        let d = alg^.algConstructorDCon
            -- data type of the constructor applied to the
            -- fresh unification vars
            dty = foldl' TApp (TC d) tparams
        tscrut =?= dty
        (ps', ms) <- unzip <$> zipWithM checkPattern targs ps
        return (ConP c ps', mconcat ms)

extendMatchCtx :: PatternMatch -> TC a -> TC a
extendMatchCtx ms = local (envLocals %~ M.union (M.fromList ms))

-- | check a sequence of bindings and pass them to the given continuation
-- in an environment suitably extended by the new bindings.
checkBindings :: Bindings -> (Bindings -> TC a) -> TC a
checkBindings NilBs kont = kont NilBs
checkBindings (ConsBs (U.unrebind -> (bind, binds))) kont =
  checkBinding bind $ \bind' ->
  checkBindings binds $ \ binds' ->
  kont (ConsBs (U.rebind bind' binds'))

checkBinding :: Binding -> (Binding -> TC a) -> TC a
checkBinding (ValB (v, U.unembed -> ann) (U.unembed -> e)) kont =
  case ann of
    Annot Nothing -> do
      (t, e') <- inferExpr e
      -- XXX : TODO generalize uvars, or else freeze 'em if we're going to
      -- behave like recent versions of GHC
      extendLocalCtx v t $ do
        tannot <- applyCurrentSubstitution t
        kont $ ValB (v, U.embed $ Annot $ Just tannot) (U.embed e')
    Annot (Just t) -> do
      void $ checkType t KType
      e' <- checkExpr e t
      extendLocalCtx v t $ do
        tannot <- applyCurrentSubstitution t
        kont $ ValB (v, U.embed $ Annot $ Just tannot) (U.embed e')
checkBinding (SampleB (v, U.unembed -> ann) (U.unembed -> e)) kont =
  case ann of
    Annot Nothing -> do
      (tdist, e') <- inferExpr e
      tsample <- unifyDistT tdist
      extendLocalCtx v tsample $ do
        tannot <- applyCurrentSubstitution tsample
        kont $ SampleB (v, U.embed $ Annot $ Just tannot) (U.embed e')
    Annot (Just tsample) -> do
      void $ checkType tsample KType
      e' <- checkExpr e (distT tsample)
      extendLocalCtx v tsample $ do
        tannot <- applyCurrentSubstitution tsample
        kont $ SampleB (v, U.embed $ Annot $ Just tannot) (U.embed e')
checkBinding (TabB y (U.unembed -> tf)) kont =
  checkTabulatedFunction y tf kont

checkTabulatedFunction :: Var -> TabulatedFun -> (Binding -> TC a) -> TC a
checkTabulatedFunction y (TabulatedFun bnd) kont =
  U.lunbind bnd $ \(avs, TabSample sels e) -> do
    -- map each var to a uvar unified with the var's typing annotation
    vts <- forM avs $ \(v, U.unembed -> a) -> do
      tu <- freshUVarT
      unifyAnn tu a
      return (v, tu)
    (sels', selTys, e', tdist) <-
      extendLocalsCtx vts $ settingVisibleSelectors (map fst vts) $ do
        (sels', selTys) <- unzip <$> mapM inferTabSelector sels
        (tdist, e') <- inferExpr e
        return (sels', selTys, e', tdist)
    tsample <- unifyDistT tdist
    let tfun = functionT' selTys tsample
    extendLocalCtx y tfun
      $ kont $ TabB y (U.embed $ TabulatedFun $ U.bind avs $ TabSample sels' e')

inferTabSelector :: TabSelector -> TC (TabSelector, Type)
inferTabSelector (TabIndex v) = do
  ensureVisibleSelector v
  mty <- lookupLocal v
  ty <- case mty of
    Nothing -> typeError ("selector " <> formatErr v <> " is not in scope??")
    Just ty -> return ty
  return (TabIndex v, ty)

inferExpr :: Expr -> TC (Type, Expr)
inferExpr e_ = case e_ of
  V v -> do
    mt <- lookupVar v
    case mt of
      Nothing -> typeError ("unbound variable " <> formatErr v)
      Just tv -> instantiate tv $ \t' -> 
        return (t', V v)
  App e1_ e2_ -> do
    (t1, e1') <- inferExpr e1_
    (tdom, tcod) <- unifyFunctionT t1
    e2' <- checkExpr e2_ tdom
    return (tcod, App e1' e2')
  C c -> do
    constr <- lookupCCon c
    ty <- mkConstructorType constr
    return (ty, C c)
  Ann e1_ t_ -> do
    t <- checkType t_ KType
    e1' <- checkExpr e1_ t
    tannot <- applyCurrentSubstitution t
    return (t, Ann e1' tannot)
  Case {} -> typeError ("cannot infer the type of a case expression "
                        <> formatErr e_
                        <> " try adding a type annotation"
                        <> " or a function signature declaration")
  Lam bnd ->
    U.lunbind bnd $ \((v, U.unembed -> ann), e1_) -> do
      tdom <- freshUVarT
      tcod <- freshUVarT
      unifyAnn tdom ann
      e1 <- extendLocalCtx v tdom $ checkExpr e1_ tcod
      tanndom <- applyCurrentSubstitution tdom
      tanncod <- applyCurrentSubstitution tcod
      let
        e = Lam $ U.bind (v, U.embed $ Annot $ Just tanndom) (Ann e1 tanncod)
        t = functionT tdom tcod
      return (t, e)
  _ -> typeError ("cannot infer type of " <> formatErr e_
                  <> " try adding a type annotation")

-- | Extend the environment by incorporating the given declaration.
extendDCtx :: Decl -> TC a -> TC a
extendDCtx d =
  case d of
    ValueDecl vd -> extendValueDeclCtx vd
    TypeDecl td -> extendTypeDeclCtx td

extendValueDeclCtx :: ValueDecl -> TC a -> TC a
extendValueDeclCtx vd =
  case vd of
    SigDecl v t -> extendSigDeclCtx v t
    FunDecl v _e -> extendValueDefinitionCtx v
    ValDecl v _e -> extendValueDefinitionCtx v
    SampleDecl v _e -> extendValueDefinitionCtx v

extendTypeDeclCtx :: TypeDecl -> TC a -> TC a
extendTypeDeclCtx td =
  case td of
    DataDecl dcon constrs -> extendDataDeclCtx dcon constrs
    EnumDecl dcon n -> extendEnumDeclCtx dcon n

-- | Extend the typing context by adding the given type and value constructors
extendDataDeclCtx :: Con -> DataDecl -> TC a -> TC a
extendDataDeclCtx dcon bnd comp = do
  U.lunbind bnd $ \ (vks, constrs) -> do
    let kparams = map snd vks
        cs = map (\(ConstructorDef c _) -> c) constrs
        algty = AlgType kparams cs
    extendDConCtx dcon (AlgebraicType algty) $ do
      let constructors = map (mkConstructor dcon vks) constrs
      extendConstructorsCtx constructors comp

-- | Extend the typing context by adding the given enumeration type
extendEnumDeclCtx :: Con -> Nat -> TC a -> TC a
extendEnumDeclCtx dcon n =
  extendDConCtx dcon (EnumerationType n)

-- | @mkConstructor d vks (ConstructorDef c params)@ returns @(c,
-- ccon)@ where @ccon@ is a 'Constructor' for the type @d@ with the
-- given type and value parameters.
mkConstructor :: Con -> [(TyVar, Kind)] -> ConstructorDef -> (Con, AlgConstructor)
mkConstructor dcon vks (ConstructorDef ccon args) =
  (ccon, AlgConstructor (U.bind vks args) dcon)

extendSigDeclCtx :: Var -> Type -> TC a -> TC a
extendSigDeclCtx v t =
  local (envGlobals . at v ?~ t) . U.avoid [U.AnyName v]

extendValueDefinitionCtx :: Var -> TC a -> TC a
extendValueDefinitionCtx v =
  local (envGlobalDefns %~ M.insert v ())

-- | @extendTyVarCtx a k comp@ Extend the type environment of @comp@
-- with @a@ having the kind @k@.
extendTyVarCtx :: TyVar -> Kind -> TC a -> TC a
extendTyVarCtx a k =
  -- no need for U.avoid since we used U.lunbind when we brough the
  -- variable into scope.
  local (envTys . at a ?~ k)

-- | Extend the type environment with all the given type variables
-- with the given kinds.  Assumes the variables are distinct.
-- Does not add to the avoid set because we must have already called U.lunbind.
extendTyVarsCtx :: [(TyVar, Kind)] -> TC a -> TC a
extendTyVarsCtx vks = local (envTys %~ M.union (M.fromList vks))

-- | Extend the data type environment by adding the declaration
-- of the given data type with the given kind
extendDConCtx :: Con -> GenerativeType -> TC a -> TC a
extendDConCtx dcon k = local (envDCons . at dcon ?~ k)

-- | Extend the local variables environment by adding the given
-- variable (assumed to be free and fresh) with the given type (which may be
-- a UVar)
extendLocalCtx :: Var -> Type -> TC a -> TC a
extendLocalCtx v t = local (envLocals . at v ?~ t)

extendLocalsCtx :: [(Var, Type)] -> TC a -> TC a
extendLocalsCtx vts = local (envLocals %~ M.union (M.fromList vts))

-- | Make the given vars be the only legal selectors when runnning
-- the given computation
settingVisibleSelectors :: [Var] -> TC a -> TC a
settingVisibleSelectors vs =
  local (envVisibleSelector .~ vsMap)
  where
    vsMap = M.fromList (map (\k -> (k, ())) vs)

extendConstructorsCtx :: [(Con, AlgConstructor)] -> TC a -> TC a
extendConstructorsCtx cconstrs =
  local (envCCons %~ M.union (M.fromList cconstrs))

-- | Typecheck the contents of a model.
checkModel :: Model -> TC Model
checkModel =
  fmap Model . foldr tcE (return []) . modelDecls
  where
    tcE :: Decl -> TC [Decl] -> TC [Decl]
    d `tcE` checkRest = do
      d' <- checkDecl d
      ms' <- extendDCtx d' $ checkRest
      return (d' : ms')
  
throwTCError :: TCError -> TC a
throwTCError = lift . lift . throwError

typeError :: F.Doc -> TC a
typeError msg =
  throwTCError . TCError $ "type error: " <> msg

unimplemented :: F.Doc -> TC a
unimplemented msg =
  throwTCError . TCError $ "typecheck unimplemented: " <> msg

formatErr :: (Pretty a) => a -> F.Doc
formatErr = format . ppDefault

