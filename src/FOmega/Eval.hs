{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}
module FOmega.Eval where

import Control.Applicative (Applicative(..))
import Control.Lens
import Control.Monad (forM, replicateM, unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.Except (MonadError(..), ExceptT(..), runExceptT)
import Control.Monad.State (MonadState(..), StateT(..), mapStateT, evalStateT)
import Control.Monad.Trans (MonadTrans(..))
import qualified Data.Map as M
import qualified System.Random as RNG

import qualified Data.Format as F

import Insomnia.Common.Literal
import Insomnia.Common.SampleParameters
import Insomnia.Interp.PMonad as PMonad
import Insomnia.Pretty (ppDefault)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import FOmega.Syntax
import FOmega.Value
import qualified FOmega.Primitives as Primitives

class (U.Fresh m) => MonadEval m where
  localEnv :: (Env -> Env) -> m a -> m a
  askEnv :: m Env
  asksEnv :: (Env -> a) -> m a
  unimplemented :: String -> m a
  evaluationError :: String -> m a
  lookupPrimitive :: PrimitiveClosureHead -> m (PrimitiveClosureSpine -> m Value)

type EvalTransformerStack m = ReaderT Env (ReaderT (PrimImplEnv m)
                                           (U.FreshMT (ExceptT String m)))
newtype EvalT m a = EvalT { unEvalT :: (EvalTransformerStack m) a }
                    deriving (Functor, Applicative, Monad, MonadIO)

newtype PrimImplEnv m =
  PrimImplEnv { primImplEnvMap :: M.Map PrimitiveClosureHead (PrimitiveClosureSpine -> EvalT m Value) }


instance Monad m => U.Fresh (EvalT m) where
  fresh = EvalT . U.fresh

instance Monad m => MonadEval (EvalT m) where
  localEnv f = EvalT . local f . unEvalT
  askEnv = EvalT ask
  asksEnv f = EvalT (asks f)
  unimplemented what = EvalT (throwError $ "unimplemented in FOmega.Eval " ++ what)
  evaluationError what = EvalT (throwError $ "unexpected runtime error - FOmega.Eval " ++ what)
  lookupPrimitive = lookupPrimitiveEvalT

lookupPrimitiveEvalT :: Monad m
                        => PrimitiveClosureHead
                        -> EvalT m (PrimitiveClosureSpine -> EvalT m Value)
lookupPrimitiveEvalT h = EvalT $ do
  mfn <- lift (asks (M.lookup h . primImplEnvMap))
  case mfn of
   Just fn -> return fn
   Nothing -> unEvalT $ evaluationError $ "unknown primitive " ++ show h

runEvalCommand :: (MonadIO m) => Command -> m (Either String Value)
runEvalCommand cmd = runEvalCommand' cmd (addPrimitiveVars emptyEnv) (PrimImplEnv primitiveEvalMap)

runEvalCommand' :: (MonadIO m) => Command -> Env -> PrimImplEnv m -> m (Either String Value)
runEvalCommand' cmd env primImpl =
  runExceptT
  $ U.runFreshMT (runReaderT
                  (runReaderT (unEvalT (evalCommand cmd)) env)
                  primImpl)

addPrimitiveVars :: Env -> Env 
addPrimitiveVars env =
  M.foldWithKey extendEnv env Primitives.primitives
  
primitiveEvalMap :: MonadEval m => M.Map PrimitiveClosureHead (PrimitiveClosureSpine -> m Value)
primitiveEvalMap =
  M.fromList [ primitive "__BOOT.intAdd"  intAddImpl
             , primitive "__BOOT.ifIntLt" ifIntLtImpl
             , primitive "__BOOT.Distribution.choose" distChooseImpl
             , primitive "__BOOT.Distribution.uniform" distUniformImpl
             ]
  where
    primitive h c = (h, c)

-- intAdd :: Int -> Int -> Int
intAddImpl :: MonadEval m => PrimitiveClosureSpine -> m Value
intAddImpl (NilPCS
            `AppPCS` (LitV (IntL n1))
            `AppPCS` (LitV (IntL n2))) =
  return $ LitV $ IntL $! n1 + n2
intAddImpl _ = evaluationError "__BOOT.intAdd incorrect arguments"

-- ifIntLt :: forall a . Int -> Int -> ({} -> a) -> ({} -> a) -> ({} -> a)
ifIntLtImpl :: MonadEval m => PrimitiveClosureSpine -> m Value
ifIntLtImpl (NilPCS
             `AppPCS` (LitV (IntL n1))
             `AppPCS` (LitV (IntL n2))
             `AppPCS` k1 `AppPCS` k2) =
  return $ if n1 < n2 then k1 else k2
ifIntLtImpl _ = evaluationError "__BOOT.ifIntLt incorrect arguments"
  
-- distChooseImpl :: forall a . Real -> Dist a -> Dist a -> Dist a
distChooseImpl :: MonadEval m => PrimitiveClosureSpine -> m Value
distChooseImpl (NilPCS
                `AppPCS` (LitV (RealL r))
                `AppPCS` (DistV dc1)
                `AppPCS` (DistV dc2)) = do
  unless (0.0 <= r && r <= 1.0) $
    evaluationError "__BOOT.Distribution.choose: real parameter should be in the range [0.0 .. 1.0]"
  return $ DistV $ DistClosure emptyEnv $ PrimitiveTh $ ChoosePD r dc1 dc2
distChooseImpl _ = evaluationError "__BOOT.Distribution.choose incorrect arguments"

-- distUniformImpl :: Real -> Real -> Dist Real
distUniformImpl :: MonadEval m => PrimitiveClosureSpine -> m Value
distUniformImpl (NilPCS
                 `AppPCS` (LitV (RealL lo))
                 `AppPCS` (LitV (RealL hi))) = do
  unless (lo <= hi) $
    evaluationError "__BOOT.Distribution.uniform: lo not less then or equal to hi"
  return $ DistV $ DistClosure emptyEnv $ PrimitiveTh $ UniformPD lo hi
distUniformImpl _ = evaluationError "__BOOT.Distribution.uniform incorrect arguments"

extendEnv :: Var -> Value -> Env -> Env
extendEnv x v e =
  Env $ \x' -> if x == x' then v else envLookup e x'

eval :: MonadEval m => Term -> m Value
eval m_ =
  case m_ of
   V x -> asksEnv (flip envLookup x)
   L l -> return $ LitV l
   Lam bnd -> asksEnv (mkClosureLam bnd)
   PLam bnd -> asksEnv (mkPClosure bnd)
   PApp m t -> do
     v1 <- eval m
     applyPClosureV v1 t
   App m1 m2 -> do
     v1 <- eval m1
     v2 <- eval m2
     applyClosureV v1 v2
   Let bnd -> do
     ((x, U.unembed -> m1), m2) <- U.unbind bnd
     v1 <- eval m1
     localEnv (extendEnv x v1) $ eval m2
   Record fms -> do
     fvs <- forM fms $ \(f, m) -> do
       v <- eval m
       return (f, v)
     return $ RecordV fvs
   Proj m f -> do
     v <- eval m
     case v of
      RecordV fvs -> selectField fvs f
      _ -> evaluationError "projection from something other than a record"
   Inj f m _ -> do
     v <- eval m
     return $ InjV f v
   Case m clauses fallthrough -> do
     v <- eval m
     case v of
      InjV f v' -> do
        s <- selectClause clauses fallthrough f
        case s of
         Left defM -> eval defM
         Right bnd -> do
           (x, m') <- U.unbind bnd
           localEnv (extendEnv x v') (eval m')
      _ -> evaluationError "case on non-injection value"
   Return m -> asksEnv (mkDistClosureRet m)
   LetSample bnd -> asksEnv (mkDistClosureSeq bnd)
   LetRec bnd -> do
     (U.unrec -> recBinds, body) <- U.unbind bnd
     env <- mkRecursiveEnv recBinds
     localEnv (const env) $ eval body
   Memo memfn -> asksEnv (mkDistClosureMemo memfn)
   Pack t m _ -> do
     v <- eval m
     return $ PackV t v
   Unpack bnd -> do
     ((a, x, U.unembed -> m1), body) <- U.unbind bnd
     v1 <- eval m1
     case v1 of
      PackV t v -> localEnv (extendEnv x v) $ eval (U.subst a t body)
      _ -> evaluationError "unpack of non-packed value"
   Roll _t m _ctx -> do
     v <- eval m
     return $ RollV v
   Unroll _t m _ctx -> do
     v <- eval m
     case v of
      RollV v' -> return v'
      _ -> evaluationError "unroll of non-rolled value"
   Assume _ -> evaluationError "evaluation of an Assume directive"
   Abort _ -> evaluationError "evaluation Aborted"

applyClosureV :: MonadEval m
                 => Value
                 -> Value
                 -> m Value
applyClosureV v1 v2 =
  case v1 of
   ClosureV e clz ->
     localEnv (const e) $ applyClosure clz v2
   _ -> evaluationError "application of something other than a closure"

applyClosure :: MonadEval m
                => Closure
                -> Value
                -> m Value
applyClosure (PlainLambdaClz bnd) v2 = do
  (x, m) <- U.unbind bnd
  localEnv (extendEnv x v2) $ eval m
applyClosure (PrimitiveClz p) v2 = applyPrimitiveVal p v2

applyPClosureV :: MonadEval m
                 => Value
                 -> Type
                 -> m Value
applyPClosureV v1 t = do
  case v1 of
   PClosureV env clz ->
     localEnv (const env) $ applyPolyClosure clz t
   _ -> evaluationError "polymorphic application of something other than a polymorphic closure"

applyPolyClosure :: MonadEval m
                    => PolyClosure
                    -> Type
                    -> m Value
applyPolyClosure (PlainPolyClz bnd) t = do
  (a, body) <- U.unbind bnd
  eval (U.subst a t body)
applyPolyClosure (PrimitivePolyClz prim) _t = do
  return $ if prim^.polyPrimSatArity > 1
           then PClosureV emptyEnv $ PrimitivePolyClz (prim & polyPrimSatArity -~ 1)
           else ClosureV emptyEnv $ PrimitiveClz $ prim^.polyPrimClz

applyPrimitive :: MonadEval m
                  => PrimitiveClosure
                  -> (PrimitiveClosureSpine -> PrimitiveClosureSpine)
                  -> m Value
applyPrimitive prim growSpine =
  if prim^.primClzSatArity > 1
  then return
       $ ClosureV emptyEnv
       $ PrimitiveClz (prim
                       & primClzSatArity -~ 1
                       & primClzSpine %~ growSpine)
  else evaluatePrimitive (prim^.primClzHead) (growSpine (prim^.primClzSpine))

applyPrimitiveVal :: MonadEval m => PrimitiveClosure -> Value -> m Value
applyPrimitiveVal prim v = applyPrimitive prim (flip AppPCS v)

evaluatePrimitive :: MonadEval m
                     => PrimitiveClosureHead
                     -> PrimitiveClosureSpine
                     -> m Value
evaluatePrimitive h sp = do
  fn <- lookupPrimitive h
  fn sp

mkClosureLam :: U.Bind (Var, U.Embed Type) Term -> Env -> Value
mkClosureLam bnd env = 
  let ((v, _t), m) = UU.unsafeUnbind bnd
  in ClosureV env $ PlainLambdaClz $ U.bind v m
  
mkPClosure :: U.Bind (TyVar, U.Embed Kind) Term -> Env -> Value
mkPClosure bnd env = 
  let ((a, _k), m) = UU.unsafeUnbind bnd
  in PClosureV env $ PlainPolyClz $ U.bind a m

mkDistClosureRet :: Term -> Env -> Value
mkDistClosureRet m = mkDistClosure (ReturnTh m)

mkDistClosureSeq :: (U.Bind (Var, U.Embed Term) Term) -> Env -> Value
mkDistClosureSeq bnd = mkDistClosure (LetSampleTh bnd)

mkDistClosureMemo :: Term -> Env -> Value
mkDistClosureMemo m = mkDistClosure (MemoTh m)

mkDistClosure :: DistThunk -> Env -> Value
mkDistClosure cmp env = DistV $ DistClosure env cmp

selectField :: MonadEval m => [(Field, Value)] -> Field -> m Value
selectField fvs_ f = (go fvs_)
  where
    go [] = evaluationError "selected a field that isn't present in the record"
    go ((f',v):fvs) | f == f' = return v
                    | otherwise = go fvs
  

selectClause :: MonadEval m
                => [Clause]
                -> Maybe Term
                -> Field
             -> m (Either Term (U.Bind Var Term))
selectClause clauses_ defaultClause f =
  go clauses_
  where
    go [] =
      case defaultClause of
       Just m -> return (Left m)
       Nothing -> evaluationError "no match case clause found and no default available"
    go (Clause f' bnd : clauses) | f == f' = return (Right bnd)
                                 | otherwise = go clauses

mkRecursiveEnv :: MonadEval m => [(Var, a, U.Embed Term)] -> m Env
mkRecursiveEnv recBinds = do
  env0 <- askEnv
  let
    -- N.B. knot tying
    binds = map (evalRecursiveBinding env) recBinds
    env = extendsEnv binds env0
  return env

evalRecursiveBinding :: Env -> (Var, a, U.Embed Term) -> (Var, Value)
evalRecursiveBinding env (x, _, U.unembed -> m_) =
  (x, evalRecRHS env m_)

-- | By construction the RHS's of bindings in a letrec are syntactically evidently values
-- (in fact, a subset of the possible values) so we can "evaluate" them without invoking the
-- real evaluation.
evalRecRHS :: Env -> Term -> Value
evalRecRHS env m_ =
  case m_ of
   Lam bnd -> mkClosureLam bnd env
   PLam bnd -> mkPClosure bnd env
   L lit -> LitV lit
   Record fms ->
     RecordV $ map (\(f, m) -> (f, evalRecRHS env m)) fms
   Memo m -> mkDistClosureMemo m env
   _ -> error "internal error: FOmega.Eval.evalRecursiveBinding saw something that disagrees with FOmega.Check.valueRestriction"
       

extendsEnv :: [(Var, Value)] -> Env -> Env
extendsEnv [] = id
extendsEnv ((x,v):xvs) = extendEnv x v . extendsEnv xvs

evalCommand :: (MonadEval m, MonadIO m) => Command -> m Value
evalCommand c_ =
  case c_ of
   LetC bnd -> do
     ((x, U.unembed -> m), c) <- U.unbind bnd
     v <- eval m
     localEnv (extendEnv x v) (evalCommand c)
   ReturnC m -> eval m
   EffectC pc m -> do
     v <- eval m
     evalPrimitiveCommand pc v
   BindC bnd -> do
     ((x, U.unembed -> c1), c2) <- U.unbind bnd
     v1 <- evalCommand c1
     localEnv (extendEnv x v1) (evalCommand c2)
   UnpackC bnd -> do
     ((a, x, U.unembed -> m), c) <- U.unbind bnd
     v <- eval m
     case v of
      PackV t v' ->
        localEnv (extendEnv x v') (evalCommand (U.subst a t c))
      _ -> evaluationError "evalCommand tried to unpack something other than a pack"

evalPrimitiveCommand :: (MonadEval m, MonadIO m)
                        => PrimitiveCommand
                        -> Value
                        -> m Value
evalPrimitiveCommand pc arg =
  case pc of
   SamplePC params -> do
     evalSampleDistribution params arg
   PrintPC -> do
     liftIO $ F.putStrLnDoc (F.format $ ppDefault arg)
     return $ embedUnitV

evalSampleDistribution :: (MonadEval m, MonadIO m)
                          => SampleParameters
                          -> Value
                          -> m Value
evalSampleDistribution params v_ = do
  let
    comp = replicateM (params^.numSamplesParameter) (forceValue v_)
  vs <- runSampleTIO comp
  embedToList vs

embedToList :: MonadEval m => [Value] -> m Value
embedToList vs_ = do
  n <- eval nilListVal
  c <- eval consListVal
  let
    make vs =
      case vs of
      [] -> applyPClosureV n unitT
      (v:vs') -> do
        vs'' <- make vs'
        let w = tupleV [v, vs'']
        c' <- applyPClosureV c unitT
        applyClosureV c' w
  make vs_
  
embedUnitV :: Value
embedUnitV = RecordV []

-- Assuming the term evaluates to a DistV, force the underlying thunk
-- and return its value.
forceEval :: (MonadEval m, PMonad.ContinuousProbabilityMonad m)
             => Term
             -> m Value
forceEval m = do
  v <- eval m
  forceValue v

-- Assuming the value is a DistV, force the underlying thunk and
-- return its value.
forceValue :: (MonadEval m, PMonad.ContinuousProbabilityMonad m)
              => Value
              -> m Value
forceValue v_ =
  case v_ of
   DistV clos -> do
     forceDistClosure clos
   _ -> evaluationError "forcing a value that is not a distribution thunk"
  
newtype SampleT g m a = SampleT {unSampleT :: StateT g m a }
                      deriving (Functor, Applicative, Monad, U.Fresh)

runSampleTIO :: MonadIO m => SampleT RNG.StdGen m a -> m a
runSampleTIO comp = do
  g <- liftIO $ RNG.newStdGen
  evalStateT (unSampleT comp) g

instance (RNG.RandomGen g, Monad m) => PMonad.ProbabilityMonad (SampleT g m) where
  choose r m1 m2 = SampleT $ do
    x <- state $ RNG.randomR (0.0, 1.0)
    unSampleT $ if x < r then m1 else m2

instance (MonadEval m) => MonadEval (SampleT g m) where
  localEnv f = SampleT . mapStateT (localEnv f) . unSampleT
  askEnv = SampleT $ lift $ askEnv
  asksEnv = SampleT . lift . asksEnv
  unimplemented = SampleT . lift . unimplemented
  evaluationError = SampleT . lift . evaluationError
  lookupPrimitive p = SampleT $ do
    f <- lift $ lookupPrimitive p
    return $ \x -> SampleT $ lift (f x)
    
instance (RNG.RandomGen g, Monad m) => PMonad.ContinuousProbabilityMonad (SampleT g m) where
  u = SampleT $ state $ RNG.randomR (0.0, 1.0)


forceDistClosure :: (MonadEval m, PMonad.ContinuousProbabilityMonad m)
                    => DistClosure
                    -> m Value
forceDistClosure clos =
  localEnv (const $ clos^.distClosureEnv)
  $ forceDistThunk $ clos^.distClosureThunk

-- Force the given thunk and return its value
forceDistThunk :: (MonadEval m, PMonad.ContinuousProbabilityMonad m)
             => DistThunk
             -> m Value
forceDistThunk th_ = do
  case th_ of
   ReturnTh m -> eval m
   LetSampleTh bnd -> do
     ((x, U.unembed -> m1), m2) <- U.unbind bnd
     v1 <- forceEval m1
     localEnv (extendEnv x v1) $ forceEval m2
   MemoTh {} -> unimplemented "force memo thunk"
   PrimitiveTh pd -> forcePrimitiveDistribution pd


forcePrimitiveDistribution :: (MonadEval m, PMonad.ContinuousProbabilityMonad m)
                              => PrimitiveDistribution
                              -> m Value
forcePrimitiveDistribution pd =
  case pd of
   ChoosePD r m1 m2 -> do
     PMonad.choose r (forceDistClosure m1) (forceDistClosure m2)
   UniformPD lo hi -> do
     r <- PMonad.u
     return $ LitV $ RealL $ r * lo + (1 - r) * hi
     
