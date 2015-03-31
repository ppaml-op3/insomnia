{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}
module FOmega.Eval where

import Control.Applicative (Applicative(..))
import Control.Lens
import Control.Monad (forM, replicateM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.Except (MonadError(..), ExceptT(..), runExceptT)

import qualified Data.Format as F

import Insomnia.Common.SampleParameters
import Insomnia.Pretty (ppDefault)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import FOmega.Syntax
import FOmega.Value

class (U.Fresh m) => MonadEval m where
  localEnv :: (Env -> Env) -> m a -> m a
  askEnv :: m Env
  asksEnv :: (Env -> a) -> m a
  unimplemented :: String -> m a
  evaluationError :: String -> m a

newtype EvalT m a = EvalT { unEvalT :: ReaderT Env (U.FreshMT (ExceptT String m)) a }
                    deriving (Functor, Applicative, Monad, MonadIO)

instance Monad m => U.Fresh (EvalT m) where
  fresh = EvalT . U.fresh

instance Monad m => MonadEval (EvalT m) where
  localEnv f = EvalT . local f . unEvalT
  askEnv = EvalT ask
  asksEnv f = EvalT (asks f)
  unimplemented what = EvalT (throwError $ "unimplemented in FOmega.Eval " ++ what)
  evaluationError what = EvalT (throwError $ "unexpected runtime error - FOmega.Eval " ++ what)

runEvalCommand :: (MonadIO m) => Command -> m (Either String Value)
runEvalCommand cmd = runExceptT (U.runFreshMT (runReaderT (unEvalT (evalCommand cmd)) baseEnv))
  where baseEnv = Env (const (error "unbound variable in FOmega.Eval baseEnv"))

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
     applyPClosure v1 t
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
applyClosure (PrimitiveClz str) v2 = unimplemented "apply primitive closure"

applyPClosure :: MonadEval m
                 => Value
                 -> Type
                 -> m Value
applyPClosure v1 t = do
  case v1 of
   PClosureV e bnd -> do
     (a, body) <- U.unbind bnd
     localEnv (const e) $ eval (U.subst a t body)
   _ -> evaluationError "polymorphic application of something other than a polymorphic closure"


mkClosureLam :: U.Bind (Var, U.Embed Type) Term -> Env -> Value
mkClosureLam bnd env = 
  let ((v, _t), m) = UU.unsafeUnbind bnd
  in ClosureV env $ PlainLambdaClz $ U.bind v m
  
mkPClosure :: U.Bind (TyVar, U.Embed Kind) Term -> Env -> Value
mkPClosure bnd env = 
  let ((a, _k), m) = UU.unsafeUnbind bnd
  in PClosureV env $ U.bind a m

mkDistClosureRet :: Term -> Env -> Value
mkDistClosureRet m = mkDistClosure (ReturnTh m)

mkDistClosureSeq :: (U.Bind (Var, U.Embed Term) Term) -> Env -> Value
mkDistClosureSeq bnd = mkDistClosure (LetSampleTh bnd)

mkDistClosureMemo :: Term -> Env -> Value
mkDistClosureMemo m = mkDistClosure (MemoTh m)

mkDistClosure :: DistThunk -> Env -> Value
mkDistClosure cmp env = DistV env cmp

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
   SamplePC params -> evalSampleDistribution params arg
   PrintPC -> do
     liftIO $ F.putStrLnDoc (F.format $ ppDefault arg)
     return $ embedUnitV

evalSampleDistribution :: (MonadEval m, MonadIO m)
                          => SampleParameters
                          -> Value
                          -> m Value
evalSampleDistribution params v_ = do
  vs <- replicateM (params^.numSamplesParameter) (forceValue v_)
  embedToList vs

embedToList :: MonadEval m => [Value] -> m Value
embedToList vs_ = do
  n <- eval nilListVal
  c <- eval consListVal
  let
    make vs =
      case vs of
      [] -> applyPClosure n unitT
      (v:vs') -> do
        vs'' <- make vs'
        let w = tupleV [v, vs'']
        c' <- applyPClosure c unitT
        applyClosureV c' w
  make vs_
  
embedUnitV :: Value
embedUnitV = RecordV []

-- Assuming the term evaluates to a DistV, force the underlying thunk
-- and return its value.
forceEval :: (MonadEval m)
             => Term
             -> m Value
forceEval m = do
  v <- eval m
  forceValue v

-- Assuming the value is a DistV, force the underlying thunk and
-- return its value.
forceValue :: (MonadEval m)
              => Value
              -> m Value
forceValue v_ =
  case v_ of
   DistV env th -> do
     localEnv (const env) (forceDistThunk th)
   _ -> evaluationError "forcing a value that is not a distribution thunk"
  

-- Force the given thunk and return its value
forceDistThunk :: (MonadEval m)
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
   PrimitiveTh _ -> unimplemented "force primitive thunk"
     
