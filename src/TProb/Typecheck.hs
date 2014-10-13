{-# LANGUAGE OverloadedStrings,
             FlexibleInstances, MultiParamTypeClasses,
             ViewPatterns,
             TemplateHaskell
  #-}
module TProb.Typecheck where

import Control.Lens
import Control.Applicative ((<$>))
import Control.Monad (forM, void)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Trans.Except (Except, runExcept)
import Data.List (foldl')
import Data.Format (Format(..))
import qualified Data.Map as M
import Data.Monoid (Monoid(..), (<>), First(..))
import Data.Text (Text)
import qualified Data.Text as T

import qualified Unbound.Generics.LocallyNameless as U

import Unbound.Generics.LocallyNameless.LFresh (LFreshMT, runLFreshMT)

import TProb.Types
import TProb.AST
import TProb.Unify

newtype TCError = TCError { getTCError :: Text }

instance Format TCError where
  format = format . getTCError

-- each constructor C of type D has the form:
--  ∀ (α₁ ∷ K₁, … αᵢ ∷ Kᵢ) . T₁ → T₂ → ⋯ → D α₁ ⋯ αᵢ
-- (if we add GADTs, there will also be existential β vars and
-- equality constraints.  In any case, D will always be applied to exactly
-- the αs and we don't bother storing the whole application.  Just the head
-- data constructor D.)
data Constructor =
  Constructor {
    _constructorArgs :: (U.Bind [KindedTVar] [Type])
    , _constructorDCon :: Con
    }

$(makeLenses ''Constructor)
  
-- | Typechecking environment
data Env = Env { _envDCons :: M.Map Con Kind        -- ^ data types
               , _envCCons :: M.Map Con Constructor -- ^ value constructors
               , _envGlobals :: M.Map Var Type      -- ^ declared global vars
               , _envGlobalDefns :: M.Map Var ()    -- ^ defined global vars
               , _envTys :: M.Map TyVar Kind        -- ^ local type variables
               , _envLocals :: M.Map Var Type       -- ^ local value variables
               }

$(makeLenses ''Env)

-- | The empty typechecking environment
emptyEnv :: Env
emptyEnv = Env mempty mempty mempty mempty mempty mempty

-- | Base environment with builtin types.
baseEnv :: Env
baseEnv = emptyEnv
          & (envDCons . at conArrow) .~ Just (KType `KArr` KType `KArr` KType)
          & (envDCons . at conDist) .~ Just (KType `KArr` KType)
          & (envDCons . at conInt) .~ Just KType
          & (envDCons . at conReal) .~ Just KType

-- | Base data constructors
conArrow :: Con
conArrow = Con "->"

conDist :: Con
conDist = Con "Dist"

conInt :: Con
conInt = Con "Int"

conReal :: Con
conReal = Con "Real"

functionT :: Type -> Type -> Type
functionT t1 t2 = TC conArrow `TApp` t1 `TApp` t2

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
instance MonadUnificationExcept Type (ReaderT Env (LFreshMT (Except TCError))) where
  throwUnificationFailure uf = throwError (TCError $ T.pack $ show uf)

-- | Run a typechecking computation
runTC :: TC a -> Either TCError a
runTC comp =
  runExcept $ runLFreshMT $ runReaderT (evalUnificationT comp) baseEnv

-- | Check that a kind is well-formed.  Note that for now, all kinds
-- are well-formed.
checkKind :: Kind -> TC ()
checkKind _k = return ()

-- | The subkinding relation. For our simple kinds it is reflexive.
isSubkind :: Kind -> Kind -> Bool
isSubkind = U.aeq

-- | Look up the kind of a datatype
lookupDCon :: Con -> TC Kind 
lookupDCon d = do
  m <- view (envDCons . at d)
  case m of
    Just k -> return k
    Nothing -> typeError $ "no data type " <> formatErr d

lookupCCon :: Con -> TC Constructor
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
ensureKArr :: Kind -> TC (Kind, Kind)
ensureKArr k =
  case k of
    KType -> typeError "expected an arrow kind, got ⋆"
    KArr k1 k2 -> return (k1, k2)

ensureNoDefn :: Var -> TC ()
ensureNoDefn v = do
  m <- view (envGlobalDefns . at v)
  case m of
    Just () -> typeError ("duplicate defintion of " <> formatErr v)
    Nothing -> return ()

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
      k' <- lookupDCon dcon
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
      (k1dom, k1cod) <- ensureKArr k1
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
    SigDecl v t -> checkSigDecl v t
    FunDecl v e -> checkFunDecl v e
    DataDecl dcon constrs -> checkDataDecl dcon constrs

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

checkSigDecl :: Var -> Type -> TC Decl
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
    TForall bnd -> U.lunbind bnd $ \ ((tv, k), ty') -> do
      tu <- freshUnificationVar k
      instantiate (U.subst tv tu ty') kont
    _ -> kont ty

-- | Given a value constructor c, return its type as a polymorphic function
--   (that is, ∀ αs . T1(αs) → ⋯ → TN(αs) → D αs)
mkConstructorType :: Constructor -> TC Type
mkConstructorType constr = 
  -- XX could do unsafeBunbind here for working under the binder.
  U.lunbind (constr^.constructorArgs) $ \ (tvks, targs) -> do
  let tvs = map (TV . fst) tvks
      d = constr^.constructorDCon
      -- data type applied to the type variables - D α1 ⋯ αK
      dt = foldl' TApp (TC d) tvs
      -- arg1 → (arg2 → ⋯ (argN → D αs))
      ty = foldr functionT dt targs
  -- ∀ αs . …
  return $ go ty tvks
  where
    go t [] = t
    go t (tvk:tvks) = go (TForall (U.bind tvk t)) tvks

checkFunDecl :: Var -> Expr -> TC Decl
checkFunDecl v e = do
  msig_ <- lookupGlobal v
  ensureNoDefn v
  res <- solveUnification $ do
    tu <- freshUnificationVar KType
    openAbstract msig_ $ \msig -> do
      case msig of
        Just ty -> tu =?= ty
        Nothing -> return ()
      U.avoid [U.AnyName v] $ checkExpr e tu
  case res of
    UOkay e' -> return $ FunDecl v e'
    UFail err -> typeError ("when checking " <> formatErr v
                            <> formatErr err)

checkDataDecl :: Con -> DataDecl -> TC Decl
checkDataDecl dcon bnd = do
  guardDuplicateDConDecl dcon
  U.lunbind bnd $ \ (vks, constrs) -> do
    -- k1 -> k2 -> ... -> *
    let kcon = foldr KArr KType (map snd vks)
    checkKind kcon
    constrs' <- extendDConCtx dcon kcon $ extendTyVarsCtx vks $ forM constrs checkConstructor
    return $ DataDecl dcon $ U.bind vks constrs'

checkConstructor :: ConstructorDef -> TC ConstructorDef
checkConstructor (ConstructorDef ccon args) = do
  guardDuplicateCConDecl ccon
  args' <- forM args $ \arg -> checkType arg KType
  return (ConstructorDef ccon args')

unifyAnn :: Type -> Annot -> TC ()
unifyAnn t1 (Annot (Just t2)) = t1 =?= t2
unifyAnn _ _ = return ()

unifyFunctionT :: Type -> TC (Type, Type)
unifyFunctionT t = do
  tdom <- freshUnificationVar KType
  tcod <- freshUnificationVar KType
  t =?= functionT tdom tcod
  return (tdom, tcod)

unifyDistT :: Type -> TC Type
unifyDistT t = do
  tsample <- freshUnificationVar KType
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
      return $ Lam (U.bind (v, U.embed $ Annot $ Just tdom) e')
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
  _ -> unimplemented ("checkExpr for " <> formatErr e_)

-- | check a sequence of bindings and pass them to the given continuation
-- in an environment suitably extended by the new bindings.
checkBindings :: Bindings -> (Bindings -> TC a) -> TC a
checkBindings NilBs kont = kont NilBs
checkBindings (ConsBs (U.unrebind -> (bind, binds))) kont =
  checkBinding bind $ \bind' ->
  checkBindings binds $ \ binds' ->
  kont (ConsBs (U.rebind bind' binds'))

checkBinding :: Binding -> (Binding -> TC a) -> TC a
checkBinding (LetB (v, U.unembed -> ann) (U.unembed -> e)) kont =
  case ann of
    Annot Nothing -> do
      (t, e') <- inferExpr e
      -- XXX : TODO generalize uvars, or else freeze 'em if we're going to
      -- behave like recent versions of GHC
      extendLocalCtx v t $ do
        kont $ LetB (v, U.embed $ Annot $ Just t) (U.embed e')
    Annot (Just t) -> do
      void $ checkType t KType
      e' <- checkExpr e t
      extendLocalCtx v t $ do
        kont $ LetB (v, U.embed $ Annot $ Just t) (U.embed e')
checkBinding (SampleB (v, U.unembed -> ann) (U.unembed -> e)) kont =
  case ann of
    Annot Nothing -> do
      (tdist, e') <- inferExpr e
      tsample <- unifyDistT tdist
      extendLocalCtx v tsample $ do
        kont $ LetB (v, U.embed $ Annot $ Just tsample) (U.embed e')
    Annot (Just tsample) -> do
      void $ checkType tsample KType
      e' <- checkExpr e (distT tsample)
      extendLocalCtx v tsample $ do
        kont $ LetB (v, U.embed $ Annot $ Just tsample) (U.embed e')

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
    return (t, Ann e1' t)
  _ -> typeError ("cannot infer type of " <> formatErr e_
                  <> " try adding a type annotation")

-- | Extend the environment by incorporating the given declaration.
extendDCtx :: Decl -> TC a -> TC a
extendDCtx d =
  case d of
    SigDecl v t -> extendSigDeclCtx v t
    FunDecl v _e -> extendFunDeclCtx v
    DataDecl dcon constrs -> extendDataDeclCtx dcon constrs

-- | Extend the typing context by addind the given type and value constructors
extendDataDeclCtx :: Con -> DataDecl -> TC a -> TC a
extendDataDeclCtx dcon bnd comp = do
  U.lunbind bnd $ \ (vks, constrs) -> do
    let kcon = foldr KArr KType (map snd vks)
    extendDConCtx dcon kcon $ do
      let constructors = map (mkConstructor dcon vks) constrs
      extendConstructorsCtx constructors comp

-- | @mkConstructor d vks (ConstructorDef c params)@ returns @(c,
-- ccon)@ where @ccon@ is a 'Constructor' for the type @d@ with the
-- given type and value parameters.
mkConstructor :: Con -> [(TyVar, Kind)] -> ConstructorDef -> (Con, Constructor)
mkConstructor dcon vks (ConstructorDef ccon args) =
  (ccon, Constructor (U.bind vks args) dcon)

extendSigDeclCtx :: Var -> Type -> TC a -> TC a
extendSigDeclCtx v t =
  local (envGlobals . at v ?~ t) . U.avoid [U.AnyName v]

extendFunDeclCtx :: Var -> TC a -> TC a
extendFunDeclCtx v =
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
extendDConCtx :: Con -> Kind -> TC a -> TC a
extendDConCtx dcon k = local (envDCons . at dcon ?~ k)

-- | Extend the local variables environment by adding the given
-- variable (assumed to be free and fresh) with the given type (which may be
-- a UVar)
extendLocalCtx :: Var -> Type -> TC a -> TC a
extendLocalCtx v t = local (envLocals . at v ?~ t)

extendConstructorsCtx :: [(Con, Constructor)] -> TC a -> TC a
extendConstructorsCtx cconstrs =
  local (envCCons %~ M.union (M.fromList cconstrs))

-- | Typecheck an entire module.
checkModule :: Module -> TC Module
checkModule =
  fmap Module . foldr tcE (return []) . moduleDecls
  where
    tcE :: Decl -> TC [Decl] -> TC [Decl]
    d `tcE` checkRest = do
      d' <- checkDecl d
      ms' <- extendDCtx d' $ checkRest
      return (d' : ms')
  
throwTCError :: TCError -> TC a
throwTCError = lift . lift . throwError

typeError :: Text -> TC a
typeError msg =
  throwTCError . TCError $ "type error: " <> msg

unimplemented :: Text -> TC a
unimplemented msg =
  throwTCError . TCError $ "typecheck unimplemented: " <> msg

formatErr :: (Show a) => a -> Text
formatErr = T.pack . show

