{-# LANGUAGE ViewPatterns, FlexibleContexts,
     FlexibleInstances,
     TypeSynonymInstances
  #-}
module FOmega.Check where

import Control.Monad.Reader hiding (forM)
import Data.Monoid
import qualified Data.Set as S
import Control.Monad.Except hiding (forM)

import Data.Traversable (forM)

import qualified Unbound.Generics.LocallyNameless as U
import Unbound.Generics.LocallyNameless.LFresh (LFresh, LFreshMT, runLFreshMT)

import Insomnia.Common.Literal
import FOmega.Syntax


data Ctx = Ctx { ctxBinds :: [CBind] }

data CBind =
  CVal !Var !Type 
  | CType !TyVar !Kind

newtype Expected a = Expected { unExpected :: a }
                     deriving (Show)

newtype Got a = Got { unGot :: a }
              deriving (Show)

data OmegaErr =
  TypeAppArgKindMismatch !Type !(Expected Kind) !Type !(Got Kind)
  | TypeAppNotArr !Type !(Got Kind)
  | FixptTypeBodyKindMismatch !(Expected Kind) !(Got Kind)
  | ExpectedKType !Type !(Got Kind)
  | UnboundTypeVariable !TyVar
  | UnboundVariable !Var
  | ApplicationNotAFun !Term !(Got Type)
  | PolyAppArgKindMismatch !Term !(Expected Kind) !Type !(Got Kind)
  | PolyAppNotAFun !Term !(Got Type)
  | UnexpectedType !(Expected Type) !(Got Type)
  | ExistentialKindMismatch !(Expected Kind) !(Got Type) !(Got Kind)
  | UnpackBodyMentionsVar !Type !TyVar !(Got Type)
  | UnpackNotExist !(Got Type)
  | ProjectFromNonRecord !(Got Type) !(Expected Field)
  | FieldNotFound !(Expected Field) !(Got [Field])
  | MalformedStylizedRecord !(Got [Field])
  | MalformedSumType !(Got [Field])
  | SampleBodyNotDist !(Got Type)
  | SampleFromNonDist !(Got Type)
  | AppendErr !OmegaErr !OmegaErr
  | ExpectedSumType !(Got Type)
  | EmptyCaseConstruct --  case m of {}
  | SumTypeHasNoField !(Expected Type) !(Got Field)
  | ExpectedValueInLetRec !Var
  | MemoizeNonFunction !(Got Type)
  | MemoResultNotDist !(Got Type)
  | ExpectedFixType !(Got Type)
  | NoErr
  deriving (Show)

instance Monoid OmegaErr where
  mempty = NoErr
  mappend NoErr m = m
  mappend m NoErr = m
  mappend (AppendErr m1 m2) m3 = mappend m1 (mappend m2 m3)
  mappend m1 m2 = AppendErr m1 m2

type TC m = ReaderT Ctx (ExceptT OmegaErr (LFreshMT m))

class (LFresh m, MonadReader Ctx m, MonadError OmegaErr m, MonadPlus m) => MonadTC m
instance Monad m => MonadTC (TC m)

runTC :: TC m a -> m (Either OmegaErr a)
runTC c = runLFreshMT $ runExceptT (runReaderT c initialCtx)
  where
    initialCtx = Ctx
      [ CType (U.s2n "Int") KType
      , CType (U.s2n "Real") KType
      , CVal (U.s2n "__BOOT.intAdd") intAddTy
      , CVal (U.s2n "__BOOT.ifIntLt") ifIntLtTy
      , CVal (U.s2n "__BOOT.Distribution.choose") distChooseTy
      ]

intAddTy :: Type
intAddTy = [intT, intT] `tArrs` intT

ifIntLtTy :: Type
ifIntLtTy =
  let va = U.s2n "a"
      a = TV va
      kontT = unitT `TArr` a
  in TForall $ U.bind (va, U.embed KType) $ [intT, intT, kontT, kontT] `tArrs` kontT

distChooseTy :: Type
distChooseTy =
  let va = U.s2n "a"
      a = TV va
      da = TDist a
  in TForall $ U.bind (va, U.embed KType) $ [realT, da, da] `tArrs` da
          
inferK :: MonadTC m => Type -> m Kind
inferK t_ =
  case t_ of
   TV v -> lookupTyVar v
   TLam bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
       kbody <- extendEnv (CType v k) $ inferK tbody
       return $ KArr k kbody
   TApp tfn targ -> do
     kfn <- inferK tfn
     karg <- inferK targ
     case kfn of
      KArr karg' kres | karg == karg' -> return kres
                      | otherwise -> throwError (TypeAppArgKindMismatch tfn (Expected karg') targ (Got karg))
      KType -> throwError (TypeAppNotArr tfn (Got KType))
   TFix bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
       kbody <- extendEnv (CType v k) $ inferK tbody
       when (kbody /= k) $
         throwError (FixptTypeBodyKindMismatch (Expected k) (Got kbody))
       return k
   TForall bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
       kbody <- extendEnv (CType v k) $ inferK tbody
       expectKType tbody kbody
       return KType
   TExist ep -> do
     checkExistPack ep
     return KType
   TArr t1 t2 -> do
     k1 <- inferK t1
     expectKType t1 k1
     k2 <- inferK t2
     expectKType t2 k2
     return KType
   TRecord fts -> do
     forM_ fts $ \(_f, t) -> do
       k <- inferK t
       expectKType t k
     ensureDistinctFields $ map fst fts
     wellFormedStylizedRecord fts
     return KType
   TSum fts -> do
     forM_ fts $ \(_f, t) -> do
       k <- inferK t
       expectKType t k
     ensureDistinctFields $ map fst fts
     wellFormedSumType fts
     return KType
   TDist t -> do
     k <- inferK t
     expectKType t k
     return KType

checkExistPack :: MonadTC m => ExistPack -> m ()
checkExistPack bnd =
  U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
    kbody <- extendEnv (CType v k) $ inferK tbody
    expectKType tbody kbody

inferLit :: MonadTC m => Literal -> m Type
inferLit (IntL {}) = return intT
inferLit (RealL {}) = return realT

inferTy :: MonadTC m => Term -> m Type
inferTy m_ =
  case m_ of
   V v -> lookupVar v
   L l -> inferLit l
   Lam bnd ->
     U.lunbind bnd $ \((v, U.unembed -> t), body) -> do
       k <- inferK t
       expectKType t k
       -- TODO: normalize t here?
       t' <- extendEnv (CVal v t) $ inferTy body
       return $ TArr t t'
   App f m -> do
     tfn <- inferTy f
     targ <- inferTy m
     tfnN <- whnfTy tfn KType
     case tfnN of
      TArr targ' tres -> do
        _argNorm <- tyEquiv (Expected targ') (Got targ) KType
        return tres
      tother -> throwError $ ApplicationNotAFun f (Got tother)
   PLam bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), m) -> do
       tbody <- extendEnv (CType v k) $ inferTy m
       return $ TForall $ U.bind (v, U.embed k) tbody
   PApp m a -> do
     tfn <- inferTy m
     karg <- inferK a
     tfnN <- whnfTy tfn KType
     case tfnN of
      TForall bnd ->
        U.lunbind bnd $ \((tv, U.unembed -> karg'), tres) -> do
          unless (karg == karg') $
            throwError $ PolyAppArgKindMismatch m (Expected karg') a (Got karg)
          return $ U.subst tv a tres
      tother -> throwError $ PolyAppNotAFun m (Got tother)
   Pack a m ep -> do
     k <- inferK a
     t <- inferTy m
     checkExistPack ep
     t' <- instExistPack a k ep
     _bodyNorm <- tyEquiv (Expected t) (Got t') KType
     return $ TExist ep
   Unpack bnd ->
     checkUnpack inferTy bnd 
   Record fms -> do
     fts <- forM fms $ \(f, m) -> do
       t <- inferTy m
       return (f, t)
     ensureDistinctFields $ map fst fms
     wellFormedStylizedRecord fts
     return $ TRecord fts
   Proj m f -> do
     t <- inferTy m
     tN  <- whnfTy t KType
     case tN of
      TRecord fts ->
        lookupField fts f
      _ -> throwError $ ProjectFromNonRecord (Got t) (Expected f)
   Let bnd ->
     U.lunbind bnd $ \((x, U.unembed -> m1), m2) -> do
       t <- inferTy m1
       extendEnv (CVal x t) $ inferTy m2
   LetRec bnd ->
     U.lunbind bnd $ \(U.unrec -> constituents, body) -> do
       checkRecursiveConstituents constituents $ inferTy body
   Return m -> do
     t <- inferTy m
     return $ TDist t
   LetSample bnd ->
     U.lunbind bnd $ \((x, U.unembed -> m1), m2) -> do
       t <- inferTy m1
       tN <- whnfTy t KType
       case tN of
        TDist t' -> do
          t'' <- extendEnv (CVal x t') $ inferTy m2
          tN'' <- whnfTy t'' KType
          case tN'' of
           TDist {} -> return tN''
           _ -> throwError $ SampleBodyNotDist (Got t'')
        _ -> throwError $ SampleFromNonDist (Got t)
   Assume t -> do
     k <- inferK t
     expectKType t k
     return t
   Case m clauses optDefault -> do
     tsum <- inferTy m
     tsumN <- whnfTy tsum KType
     alts <- case tsumN of
      TSum alts -> return alts
      _ -> throwError $ ExpectedSumType (Got tsum)
     ts <- forM clauses (checkClause alts)
     optT <- forM optDefault inferTy
     let touts = ts ++ (maybe [] (\t -> [t]) optT)
     case touts of
      [] -> throwError $ EmptyCaseConstruct
      (tcand:tcands) -> do
        mapM_ (\t -> tyEquiv (Expected tcand) (Got t) KType) tcands
        return tcand
   Inj f m t -> do
     k <- inferK t
     expectKType t k
     tN <- whnfTy t KType
     alts <- case tN of
       TSum alts -> return alts
       _ -> throwError $ ExpectedSumType (Got tN)
     tin <- inferTy m
     checkInj alts f tin
     return tN
   Roll t m pk -> do
     checkRollUnroll True t m pk
   Unroll t m pk -> do
     checkRollUnroll False t m pk
   Abort t -> do
     k <- inferK t
     expectKType t k
     return t
   Memo m -> do
     t <- inferTy m
     tN <- whnfTy t KType
     case tN of
      TArr tDom tCod -> do
        tCodN <- whnfTy tCod KType
        case tCodN of
         TDist tans -> do
           return $ TDist (tDom `TArr` tans)
         _ -> throwError $ MemoResultNotDist (Got tCod)
      _ -> throwError $ MemoizeNonFunction (Got t)

inferCmdTy :: MonadTC m => Command -> m Type
inferCmdTy c_ =
  case c_ of
   LetC bnd ->
     U.lunbind bnd $ \((x, U.unembed -> m), c) -> do
       t <- inferTy m
       extendEnv (CVal x t) $ inferCmdTy c
   UnpackC bnd ->
     checkUnpack inferCmdTy bnd
   BindC bnd ->
     U.lunbind bnd $ \((x, U.unembed -> c1), c2) -> do
       t' <- inferCmdTy c1
       extendEnv (CVal x t') $ inferCmdTy c2
   ReturnC m -> 
     inferTy m
   EffectC pc m -> inferPrimitiveCommandTy pc m


inferPrimitiveCommandTy :: MonadTC m
                           => PrimitiveCommand
                           -> Term
                           -> m Type
inferPrimitiveCommandTy pc m =
  case pc of
   SamplePC _params -> do
     t <- inferTy m
     tN <- whnfTy t KType
     case tN of
      TDist t' -> return $ listT `TApp` t'
      _ -> throwError $ SampleFromNonDist (Got t)
   PrintPC -> do
     _t <- inferTy m
     return $ unitT
   
instExistPack :: MonadTC m => Type -> Kind -> ExistPack -> m Type
instExistPack t k bnd =
  U.lunbind bnd $ \((v, U.unembed -> k'), tbody) -> do
    unless (k == k') $
      throwError $ ExistentialKindMismatch (Expected k') (Got t) (Got k)
    return $ U.subst v t tbody

checkUnpack :: (MonadTC m, U.Alpha a)
               => (a -> m Type)
               -> (U.Bind (TyVar, Var, U.Embed Term) a)
               -> m Type
checkUnpack inferBody bnd =
  U.lunbind bnd $ \((tv, xv, U.unembed -> m), body) -> do
    t <- inferTy m
    tN <- whnfTy t KType
    case tN of
     TExist ep ->
       U.lunbind ep $ \((tv', U.unembed -> k), tx_) -> do
         let tx = U.subst tv' (TV tv) tx_
         tbody <- extendEnv (CType tv k) $ extendEnv (CVal xv tx) $ inferBody body
         (inferK tbody >>= expectKType tbody)
           `mplus` (throwError $ UnpackBodyMentionsVar tbody tv (Got tN))
         return tbody
     _ -> throwError $ UnpackNotExist (Got tN)


checkRollUnroll :: MonadTC m
                   => Bool -- True = rolling, False = unrolling
                   -> Type -- μα:κ.β
                   -> Term -- m
                   -> (U.Bind TyVar Type) -- δ.Ctx
                   -> m Type -- Ctx[?/δ] where ? is either the rolled or the unrolled type of m
checkRollUnroll isRoll t m pk = do
  k <- inferK t
  tN <- whnfTy t k
  -- tun = β [μα:κ.β / α]
  tun <- case tN of
    TFix bnd ->
      U.lunbind bnd $ \((tv, _), tbody) ->
      return (U.subst tv tN tbody)
    _ -> throwError $ ExpectedFixType (Got tN)
  -- trolled = ctx [μα:κ.β/δ]
  -- tunrolled = ctx [β[μα:κ.β/β]/δ]
  (trolled, tunrolled) <- U.lunbind pk $ \(tv, tctx) ->
    extendEnv (CType tv k) $ do
      kctx <- inferK tctx
      expectKType tctx kctx
      let trolled = U.subst tv tN tctx
          tunrolled = U.subst tv tun tctx
      return (trolled, tunrolled)
  do
    infTy <- inferTy m
    _ <- tyEquiv (Expected (if isRoll then tunrolled else trolled)) (Got infTy) KType
    return ()
  return (if isRoll then trolled else tunrolled)


-- | checks that the pattern of the given clause matches one of fields
-- in the list, and returns the type of the body of the clause.
checkClause :: MonadTC m => [(Field, Type)] -> Clause -> m Type
checkClause fts (Clause f bnd) =
  U.lunbind bnd $ \ (v, body) -> do
    t <- case lookup f fts of
          Just ty -> return ty
          Nothing -> throwError $ SumTypeHasNoField (Expected $ TSum fts) (Got f)
    extendEnv (CVal v t) $ inferTy body

-- | checks that the given field is in the given list of alternatives,
-- and if so, checks that its type is equivalent to the type in the
-- list.
checkInj :: MonadTC m => [(Field, Type)] -> Field -> Type -> m ()
checkInj alts f t = do
  case lookup f alts of
   Nothing -> throwError $ SumTypeHasNoField (Expected $ TSum alts) (Got f)
   Just t' -> do
     _ <- tyEquiv (Expected t) (Got t') KType
     return ()

-- | Check the bindings comprising a LetRec term, then call the given
-- continuation in the environment extended with their bindings.
checkRecursiveConstituents :: MonadTC m
                              => [(Var, U.Embed Type, U.Embed Term)]
                              -> m ans
                              -> m ans
checkRecursiveConstituents constituents kont = do
  -- First pass - check that all the types are well-formed
  newBinds <- forM constituents $ \(v, U.unembed -> ty, _) -> do
    k <- inferK ty
    expectKType ty k
    return $ CVal v ty
  extendEnvs newBinds $ do
    -- Second pass - in the environment extended with new bindings,
    -- check that each body is a value and has the putative type.
    forM_ constituents $ \(v, U.unembed -> ascribedTy, U.unembed -> m) -> do
      valueRestriction v m
      infTy <- inferTy m
      tyEquiv (Expected ascribedTy) (Got infTy) KType
    -- Then (still in the extended env), call the continuation.
    kont

-- | Check (conservatively) that the given term is manifestly a value.
-- The following things are values:
--   Polymorphic lambda, ordinary lambdas, literals, records of values.
valueRestriction :: MonadTC m => Var -> Term -> m ()
valueRestriction theName m_ =
  unless (isValue m_)
  $ throwError (ExpectedValueInLetRec theName)
  where
    isValue :: Term -> Bool
    isValue (L {}) = True
    isValue (PLam {}) = True
    isValue (Lam {}) = True
    isValue (Record fms) = all (\(_f, m) -> isValue m) fms
    isValue (Memo m) = isValue m || isVar m
    isValue _ = False

    isVar (V {}) = True
    isVar _ = False

------------------------------------------------------------
-- * Type normalization and equivalence

whnfTy :: MonadTC m => Type -> Kind -> m Type
whnfTy t k_ =
  case t of
   TApp t1 t2 -> do
     k2 <- inferK t2
     t1N <- whnfTy t1 (k2 `KArr` k_)
     case t1N of
      TLam bnd ->
        U.lunbind bnd $ \((v, _), tbody) ->
        whnfTy (U.subst v t2 tbody) k_
      _ -> return $ TApp t1N t2
   TLam bnd ->
     U.lunbind bnd $ \(vk@(v, _), tbody) ->
     case k_ of
      (KArr k1 k2) -> do
        tbodyN <- extendEnv (CType v k1) $ whnfTy tbody k2
        return $ TLam $ U.bind vk tbodyN
      KType -> fail $ "whnfTy lambda of base kind impossible for well-kinded types, but saw " ++ show t
   _ -> return t

tyEquiv :: MonadTC m => Expected Type -> Got Type -> Kind -> m Type
tyEquiv e@(Expected t1) g@(Got t2) k =
  tyEquiv' t1 t2 k `mplus` throwError (UnexpectedType e g)

tyEquiv' :: MonadTC m => Type -> Type -> Kind -> m Type
tyEquiv' t1_ t2_ k = do
  t1N_ <- whnfTy t1_ k
  t2N_ <- whnfTy t2_ k
  case (t1N_, t2N_, k) of
   (TV {}, TV {}, _) -> do
     (tA, _k) <- tyAtEquiv t1N_ t2N_
     return tA
   (TFix bnd1, TFix bnd2, _) ->
     U.lunbind2 bnd1 bnd2 $ \m ->
     case m of
      Just (p@(v, U.unembed -> k1), t1, (_, U.unembed -> k2), t2) -> do
        guard (k1 == k2)
        tN <- extendEnv (CType v k1) $ tyEquiv' t1 t2 k1
        return $ TFix $ U.bind p tN
      Nothing -> mzero
   (TApp {}, TApp {}, _) -> do
     (tA, _k) <- tyAtEquiv t1N_ t2N_
     return tA
   (TArr s1 t1, TArr s2 t2, KType) -> do
     sN <- tyEquiv' s1 s2 KType
     tN <- tyEquiv' t1 t2 KType
     return $ TArr sN tN
   (TForall bnd1, TForall bnd2, KType) -> do
     U.lunbind2 bnd1 bnd2 $ \m ->
       case m of
        Just (p@(v, U.unembed -> k1), t1, (_, U.unembed -> k2), t2) -> do
          guard (k1 == k2)
          tN <- extendEnv (CType v k1) $ tyEquiv' t1 t2 KType
          return $ TForall $ U.bind p tN
        Nothing -> mzero
   (TExist bnd1, TExist bnd2, KType) -> do
     U.lunbind2 bnd1 bnd2 $ \m ->
       case m of
        Just (p@(v, U.unembed -> k1), t1, (_, U.unembed -> k2), t2) -> do
          guard (k1 == k2)
          tN <- extendEnv (CType v k1) $ tyEquiv' t1 t2 KType
          return $ TExist $ U.bind p tN
        Nothing -> mzero
   (TRecord fts, TRecord gts, KType) -> do
     let allFieldNames = S.toList $ mconcat $ map (S.fromList . map fst) [fts, gts]
     ftsN <- forM allFieldNames $ \f -> do
       t1 <- lookupField fts f
       t2 <- lookupField gts f
       tN <- tyEquiv' t1 t2 KType
       return (f, tN)
     return $ TRecord ftsN
   (TSum fts, TSum gts, KType) -> do
     let allFieldNames = S.toList $ mconcat $ map (S.fromList . map fst) [fts, gts]
     ftsN <- forM allFieldNames $ \f -> do
       t1 <- lookupField fts f
       t2 <- lookupField gts f
       tN <- tyEquiv' t1 t2 KType
       return (f, tN)
     return $ TSum ftsN
   (TDist t1, TDist t2, KType) -> do
     tN <- tyEquiv' t1 t2 KType
     return $ TDist tN
   (_, _, KArr k1 k2) -> do
     v <- U.lfresh (U.s2n "a")
     let
       tv = TV v
       t1 = TApp t1_ tv
       t2 = TApp t2_ tv
     t1N <- extendEnv (CType v k1) $ tyEquiv' t1 t2 k2
     return $ TLam $ U.bind (v, U.embed k1) t1N
   (_, _, KType) -> mzero -- not equivalent
     
-- | Compare types in atomic form for equivalence.  An atomic type has
-- a variable at the head of a sequence of application.
tyAtEquiv :: MonadTC m => Type -> Type -> m (Type, Kind)
tyAtEquiv t1_ t2_ =
  case (t1_, t2_) of
   (TV v1, TV v2) ->
     if v1 == v2
     then do
       k <- lookupTyVar v1
       return (t1_, k)
     else mzero
   (TFix bnd1, TFix bnd2) ->
     U.lunbind2 bnd1 bnd2 $ \m ->
     case m of
      Just (p@(v, U.unembed -> k1), t1, (_, U.unembed -> k2), t2) -> do
        guard (k1 == k2)
        tN <- extendEnv (CType v k1) $ tyEquiv' t1 t2 k1
        return (TFix $ U.bind p tN, k1)
      Nothing -> mzero
   (TApp t1A s1, TApp t2A s2) -> do
     (tA, kt) <- tyAtEquiv t1A t2A
     case kt of
      KType -> mzero
      KArr ks k -> do
        sN <- tyEquiv' s1 s2 ks
        return (TApp tA sN, k)
   (_, _) -> mzero
     
------------------------------------------------------------
-- * Utilities

ensureDistinctFields :: MonadTC m => [Field] -> m ()
ensureDistinctFields _ = return () -- TODO: actually ensure

-- | Records that contain builtin-fields have a certain expected form:
-- 1. If a FVal, FType or FSig field is present, it is the only field.
-- 2. Both FDataIn and FDataOut fields are present.
-- 3. All the fields are FCon  (this happens in an FDataIn)
-- 4. Otherwise all fields must be FUser
wellFormedStylizedRecord :: MonadTC m => [(Field, a)] -> m ()
wellFormedStylizedRecord [(FVal, _)] = return ()
wellFormedStylizedRecord [(FType, _)] = return ()
wellFormedStylizedRecord [(FSig, _)] = return ()
wellFormedStylizedRecord fs = do
  let userRecord = all isUser fs
      isDatatype = case fs of
                    [(FDataIn, _), (FDataOut, _)] -> True
                    [(FDataOut, _), (FDataIn, _)] -> True
                    _ -> False
      isConProduct = all isCon fs
      isTuple = all isTupleIdx fs
  unless (userRecord || isDatatype || isConProduct || isTuple) $
    throwError $ MalformedStylizedRecord (Got $ map fst fs)
  where
    isUser (FUser {}, _) = True
    isUser _ = False
    isCon  (FCon {}, _) = True
    isCon _ = False
    isTupleIdx (FTuple {}, _) = True
    isTupleIdx _ = False

wellFormedSumType :: MonadTC m => [(Field, a)] -> m ()
wellFormedSumType fs = do
  let allUser = all isUser fs
      isConSum = all isCon fs
  unless (allUser || isConSum) $
    throwError $ MalformedSumType (Got $ map fst fs)
  where
    isUser (FUser {}, _) = True
    isUser _ = False
    isCon (FCon {}, _) = True
    isCon _ = False

lookupField :: MonadTC m => [(Field, a)] -> Field -> m a
lookupField fs_ f = go fs_
  where
    go [] = throwError $ FieldNotFound (Expected f) (Got $ map fst fs_)
    go ((f',x):fs) | f == f' = return x
                   | otherwise = go fs

extendEnv :: MonadTC m => CBind -> m a -> m a
extendEnv b = local (Ctx . (b:) . ctxBinds)

extendEnvs :: MonadTC m => [CBind] -> m a -> m a
extendEnvs [] = id
extendEnvs (b:bs) = extendEnv b . extendEnvs bs

expectKType :: MonadTC m => Type -> Kind -> m ()
expectKType t k =
  case k of
   KType -> return ()
   KArr {} -> throwError $ ExpectedKType t (Got k)

lookupTyVar :: MonadTC m => TyVar -> m Kind
lookupTyVar v = do
  m <- asks (findTyVar v)
  case m of
   Nothing -> throwError $ UnboundTypeVariable v
   Just k -> return k

lookupVar :: MonadTC m => Var -> m Type
lookupVar v = do
  m <- asks (findVar v)
  case m of
   Nothing -> throwError $ UnboundVariable v
   Just t -> return t

findTyVar :: TyVar -> Ctx -> Maybe Kind
findTyVar v = go . ctxBinds
  where
    go [] = Nothing
    go (b:c) =
      case b of
      CType v' k | v == v' -> Just k
      _ -> go c

findVar :: Var -> Ctx -> Maybe Type
findVar v = go . ctxBinds
  where
    go [] = Nothing
    go (b:c) =
      case b of
       CVal v' t | v == v' -> Just t
       _ -> go c

