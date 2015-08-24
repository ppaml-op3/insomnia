{-# LANGUAGE ViewPatterns, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module FOmega.Eval where

import Control.Applicative (Applicative(..))
import Control.Lens
import Control.Monad (forM, replicateM, unless, zipWithM_)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.Except (MonadError(..), ExceptT(..), runExceptT)
import Control.Monad.State (MonadState(..), StateT(..), mapStateT, evalStateT)
import Control.Monad.Trans (MonadTrans(..))
import qualified Control.Monad.Trans.State as St
import Data.Function (on)
import qualified Data.Map as M
import qualified System.Random as RNG

import qualified Data.Format as F

import Insomnia.Common.Literal
import Insomnia.Common.SampleParameters
import Insomnia.Interp.PMonad as PMonad
import Insomnia.Pretty (ppDefault)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import FOmega.Syntax hiding (selectField)
import qualified FOmega.Syntax as Stx
import FOmega.Value
import qualified FOmega.Primitives as Primitives

type PrimitiveImpl m = PrimitiveClosureSpine -> m Value

class (U.Fresh m) => MonadEval m where
  localEnv :: (Env -> Env) -> m a -> m a
  askEnv :: m Env
  asksEnv :: (Env -> a) -> m a
  unimplemented :: String -> m a
  evaluationError :: String -> m a
  observationFailure :: m a
  catchObservationFailure :: m a -> m a -> m a
  lookupPrimitive :: PrimitiveClosureHead -> m (PrimitiveImpl m)

type EvalTransformerStack m = ReaderT Env (ReaderT (PrimImplEnv m)
                                           (U.FreshMT (ExceptT EvaluationError m)))
newtype EvalT m a = EvalT { unEvalT :: (EvalTransformerStack m) a }
                    deriving (Functor, Applicative, Monad, MonadIO)

data EvaluationError =
  EvaluationRuntimeError !String
  | EvaluationObservationFailure
  deriving (Show)

newtype PrimImplEnv m =
  PrimImplEnv { primImplEnvMap :: M.Map PrimitiveClosureHead (PrimitiveImpl (EvalT m)) }


instance Monad m => U.Fresh (EvalT m) where
  fresh = EvalT . U.fresh

handleObservationFailure :: MonadError EvaluationError m => m a -> EvaluationError -> m a
handleObservationFailure h e =
  case e of
  EvaluationRuntimeError msg -> throwError $ EvaluationRuntimeError msg
  EvaluationObservationFailure -> h
  

instance Monad m => MonadEval (EvalT m) where
  localEnv f = EvalT . local f . unEvalT
  askEnv = EvalT ask
  asksEnv f = EvalT (asks f)
  unimplemented what = EvalT (throwError $ EvaluationRuntimeError $ "unimplemented in FOmega.Eval " ++ what)
  evaluationError what = EvalT (throwError $ EvaluationRuntimeError $ "unexpected runtime error - FOmega.Eval " ++ what)
  observationFailure = EvalT (throwError EvaluationObservationFailure)
  catchObservationFailure comp handler =
      EvalT (unEvalT comp `catchError` handleObservationFailure (unEvalT handler))
  lookupPrimitive = lookupPrimitiveEvalT

lookupPrimitiveEvalT :: Monad m
                        => PrimitiveClosureHead
                        -> EvalT m (PrimitiveImpl (EvalT m))
lookupPrimitiveEvalT h = EvalT $ do
  mfn <- lift (asks (M.lookup h . primImplEnvMap))
  case mfn of
   Just fn -> return fn
   Nothing -> unEvalT $ evaluationError $ "unknown primitive " ++ show h

runEvalCommand :: (MonadIO m) => Command -> m (Either EvaluationError Value)
runEvalCommand cmd = runEvalCommand' cmd (addPrimitiveVars emptyEnv) (PrimImplEnv primitiveEvalMap)

runEvalCommand' :: (MonadIO m) => Command -> Env -> PrimImplEnv m -> m (Either EvaluationError Value)
runEvalCommand' cmd env primImpl =
  runExceptT
  $ U.runFreshMT (runReaderT
                  (runReaderT (unEvalT (evalCommand cmd)) env)
                  primImpl)

addPrimitiveVars :: Env -> Env 
addPrimitiveVars env =
  M.foldWithKey extendEnv env Primitives.primitives
  
primitiveEvalMap :: MonadEval m => M.Map PrimitiveClosureHead (PrimitiveImpl m)
primitiveEvalMap =
  M.fromList [ primitive "__BOOT.intAdd"  intAddImpl
             , primitive "__BOOT.ifIntLt" ifIntLtImpl
             , primitive "__BOOT.realAdd"  realAddImpl
             , primitive "__BOOT.realMul"  realMulImpl
             , primitive "__BOOT.ifRealLt" ifRealLtImpl
             , primitive "__BOOT.Distribution.choose" distChooseImpl
             , primitive "__BOOT.Distribution.uniform" distUniformImpl
             , primitive "__BOOT.Distribution.normal" distNormalImpl
             , primitive "__BOOT.posterior" posteriorImpl
             ]
  where
    primitive h c = (h, c)

-- intAdd :: Int -> Int -> Int
intAddImpl :: MonadEval m => PrimitiveImpl m
intAddImpl (NilPCS
            `AppPCS` (LitV (IntL n1))
            `AppPCS` (LitV (IntL n2))) =
  return $ LitV $ IntL $! n1 + n2
intAddImpl _ = evaluationError "__BOOT.intAdd incorrect arguments"

-- realAdd :: Real -> Real -> Real
realAddImpl :: MonadEval m => PrimitiveImpl m
realAddImpl (NilPCS
             `AppPCS` (LitV (RealL r1))
             `AppPCS` (LitV (RealL r2))) =
  return $ LitV $ RealL $! r1 + r2
realAddImpl _ = evaluationError "__BOOT.realAdd incorrect arguments"

-- realMul :: Real -> Real -> Real
realMulImpl :: MonadEval m => PrimitiveImpl m
realMulImpl (NilPCS
             `AppPCS` (LitV (RealL r1))
             `AppPCS` (LitV (RealL r2))) =
  return $ LitV $ RealL $! r1 * r2
realMulImpl _ = evaluationError "__BOOT.realMul incorrect arguments"

-- ifIntLt :: forall a . Int -> Int -> ({} -> a) -> ({} -> a) -> ({} -> a)
ifIntLtImpl :: MonadEval m => PrimitiveImpl m
ifIntLtImpl (NilPCS
             `AppPCS` (LitV (IntL n1))
             `AppPCS` (LitV (IntL n2))
             `AppPCS` k1 `AppPCS` k2) =
  return $ if n1 < n2 then k1 else k2
ifIntLtImpl _ = evaluationError "__BOOT.ifIntLt incorrect arguments"
  
-- ifRealLt :: forall a . Real -> Real -> ({} -> a) -> ({} -> a) -> ({} -> a)
ifRealLtImpl :: MonadEval m => PrimitiveImpl m
ifRealLtImpl (NilPCS
              `AppPCS` (LitV (RealL n1))
              `AppPCS` (LitV (RealL n2))
              `AppPCS` k1 `AppPCS` k2) =
  return $ if n1 < n2 then k1 else k2
ifRealLtImpl _ = evaluationError "__BOOT.ifRealLt incorrect arguments"

-- distChooseImpl :: forall a . Real -> Dist a -> Dist a -> Dist a
distChooseImpl :: MonadEval m => PrimitiveImpl m
distChooseImpl (NilPCS
                `AppPCS` (LitV (RealL r))
                `AppPCS` (DistV dc1)
                `AppPCS` (DistV dc2)) = do
  unless (0.0 <= r && r <= 1.0) $
    evaluationError "__BOOT.Distribution.choose: real parameter should be in the range [0.0 .. 1.0]"
  return $ DistV $ DistClosure emptyEnv $ PrimitiveTh $ ChoosePD r dc1 dc2
distChooseImpl _ = evaluationError "__BOOT.Distribution.choose incorrect arguments"

-- distUniformImpl :: Real -> Real -> Dist Real
distUniformImpl :: MonadEval m => PrimitiveImpl m
distUniformImpl (NilPCS
                 `AppPCS` (LitV (RealL lo))
                 `AppPCS` (LitV (RealL hi))) = do
  unless (lo <= hi) $
    evaluationError "__BOOT.Distribution.uniform: lo not less then or equal to hi"
  return $ DistV $ DistClosure emptyEnv $ PrimitiveTh $ UniformPD lo hi
distUniformImpl _ = evaluationError "__BOOT.Distribution.uniform incorrect arguments"

-- distNormalImpl :: Real -> Real -> Dist Real
distNormalImpl :: MonadEval m => PrimitiveImpl m
distNormalImpl (NilPCS
                 `AppPCS` (LitV (RealL mu))
                 `AppPCS` (LitV (RealL sigma2))) = do
  unless (sigma2 >= 0) $
    evaluationError "__BOOT.Distribution.normal: σ² is negative"
  return $ DistV $ DistClosure emptyEnv $ PrimitiveTh $ NormalPD mu sigma2
distNormalImpl _ = evaluationError "__BOOT.Distribution.uniform incorrect arguments"

-- posteriorImpl :: forall st obs . (st -> Dist obs) -> obs -> Dist st -> Dist st
posteriorImpl :: MonadEval m => PrimitiveImpl m
posteriorImpl (NilPCS
               `AppPCS` kernel
               `AppPCS` obs
               `AppPCS` prior) = do
  kernelClz <- case kernel of
    ClosureV clz -> return clz
    _ -> evaluationError "__BOOT.posterior first arg not a function"
  priorClz <- case prior of
    DistV clz -> return clz
    _ -> evaluationError "__BOOT.posterior third arg not a distribution"
  return $ DistV $ DistClosure emptyEnv $ PrimitiveTh
    $ PosteriorPD kernelClz obs priorClz
posteriorImpl _ = evaluationError "__BOOT.posterior incorrect arguments"

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
   Case m clauses defaultClause -> do
     v <- eval m
     case v of
      InjV f v' -> do
        s <- selectClause clauses defaultClause f
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

applyClosureV :: MonadEval m
                 => Value
                 -> Value
                 -> m Value
applyClosureV v1 v2 =
  case v1 of
   ClosureV clz ->
     applyLambdaClosure clz v2
   _ -> evaluationError "application of something other than a closure"

applyLambdaClosure :: MonadEval m
                      => LambdaClosure
                      -> Value
                      -> m Value
applyLambdaClosure clz v2 =
  localEnv (const $ clz^.lambdaClosureEnv) $ applyClosure (clz^.lambdaClosureClz) v2

applyClosure :: MonadEval m
                => Closure
                -> Value
                -> m Value
applyClosure (PlainLambdaClz bnd) v2 = do
  (x, m) <- U.unbind bnd
  localEnv (extendEnv x v2) $ eval m
applyClosure (PrimitiveClz p) v2 =
  applyPrimitiveVal p v2

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
           else ClosureV $ LambdaClosure emptyEnv $ PrimitiveClz $ prim^.polyPrimClz

applyPrimitive :: MonadEval m
                  => PrimitiveClosure
                  -> (PrimitiveClosureSpine -> PrimitiveClosureSpine)
                  -> m Value
applyPrimitive prim growSpine =
  if prim^.primClzSatArity > 1
  then return
       $ ClosureV
       $ LambdaClosure emptyEnv
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
  in ClosureV $ LambdaClosure env $ PlainLambdaClz $ U.bind v m
  
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

selectField :: MonadEval m => [(Field, a)] -> Field -> m a
selectField fvs f = case Stx.selectField fvs f of
  Nothing -> evaluationError "selected a field that isn't present in the record"
  Just a -> return a
  

selectClause :: MonadEval m
                => [Clause]
                -> DefaultClause
                -> Field
             -> m (Either Term (U.Bind Var Term))
selectClause clauses_ defaultClause f =
  go clauses_
  where
    go [] =
      case defaultClause of
       (DefaultClause (Right m)) -> return (Left m)
       (DefaultClause (Left _matchFailure)) ->
         evaluationError "no match case clause found and no default available"
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
    numWanted = params^.numSamplesParameter
    comp = replicateM numWanted $ restartOnObsFailure $ forceValue v_
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

restartOnObsFailure :: (RNG.RandomGen g, MonadEval m) => SampleT g m a -> SampleT g m a
restartOnObsFailure comp = go
  where
    go = comp `catchObservationFailure` go
      
      

runSampleTIO :: MonadIO m => SampleT RNG.StdGen m a -> m a
runSampleTIO comp = do
  g <- liftIO $ RNG.newStdGen
  evalStateT (unSampleT comp) g

instance (RNG.RandomGen g, Monad m) => PMonad.ProbabilityMonad (SampleT g m) where
  choose r m1 m2 = SampleT $ do
    x <- state $ RNG.randomR (0.0, 1.0)
    unSampleT $ if x < r then m1 else m2

instance (RNG.RandomGen g, MonadEval m) => MonadEval (SampleT g m) where
  localEnv f = SampleT . mapStateT (localEnv f) . unSampleT
  askEnv = SampleT $ lift $ askEnv
  asksEnv = SampleT . lift . asksEnv
  unimplemented = SampleT . lift . unimplemented
  evaluationError = SampleT . lift . evaluationError
  observationFailure = SampleT $ lift observationFailure
  catchObservationFailure comp handler =
    SampleT $ StateT $ \g -> 
      let (g1, g2) = RNG.split g
      in runStateT (unSampleT comp) g1
         `catchObservationFailure`
         runStateT (unSampleT handler) g2
      
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
   NormalPD mu sigma2 -> do
     r <- PMonad.gauss
     let r' = mu + r * sigma2
     return $ LitV $ RealL r'
   PosteriorPD kernelClz obsExp priorClz -> do
     v <- forceDistClosure priorClz
     distActual <- applyLambdaClosure kernelClz v
     obsActual <- forceValue distActual
     guardObservation obsExp obsActual
     return v

guardObservation :: (MonadEval m)
                    => Value
                    -> Value
                    -> m ()
guardObservation obsExp obsActual = do
  case (obsExp, obsActual) of
    (LitV lit1, LitV lit2) | lit1 == lit2 -> return ()
                           | otherwise -> observationFailure
    (RecordV fs1, RecordV fs2) | ((==) `on` (map fst)) fs1 fs2 ->
                                   zipWithM_ guardObservation (map snd fs1) (map snd fs2)
                               | otherwise -> unimplemented "guardObservation: record observations of unequal fields"
    (InjV f1 v1, InjV f2 v2) | f1 == f2 -> guardObservation v1 v2
                             | otherwise -> observationFailure
    (RollV v1, RollV v2) -> guardObservation v1 v2
    _ ->
      -- XXX TODO: handle more valid observation cases here.
      {- Unsafe.unsafePerformIO $ do
        print "expecting: "
        print obsExp
        print "got"
        print obsActual
        return $ -} observationFailure
