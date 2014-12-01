{-# LANGUAGE FlexibleInstances #-}
module Insomnia.Interp.Eval where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error.Class
import Insomnia.Except

import qualified Data.Map as M

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Literal
import Insomnia.Interp.Lam

newtype RuntimeError = RuntimeError { runtimeErrorMsg :: String }
                     deriving (Show)

class (Applicative m, Monad m, U.Fresh m) => MonadEval m where
  rho :: m Env
  lookupEnv :: Var -> m (Maybe Value)
  lookupEnv v = fmap (fmap U.unembed . M.lookup v . envMapping) rho
  localEnv :: (Env -> Env) -> m a -> m a
  runtimeError :: RuntimeError -> m a
    
type E = U.FreshMT (ReaderT Env (Except RuntimeError))
  
instance MonadEval (U.FreshMT (ReaderT Env (Except RuntimeError))) where
  rho = ask
  runtimeError = throwError
  localEnv = local

evalProgram :: MonadEval m => Program -> m Value
evalProgram p =
  case p of
   EvalP e -> eval e
   DefineP bnd -> do
     (defn, rest) <- U.unbind bnd
     evalDefinition defn (evalProgram rest)

evalDefinition :: MonadEval m => Definition -> m a -> m a
evalDefinition d kont =
  case d of
   VarDefn x e_ -> do
     let e = U.unembed e_
     v <- eval e
     localEnv (extendEnv x v) kont
   FunDefn f e_ -> do
     let e = U.unembed e_
     case e of
      LamE bnd -> do
        (x, body) <- U.unbind bnd
        env_ <- rho
        let -- rec
          env = extendEnv f v env_
          v = CloV (U.bind (env, x) body)
        localEnv (extendEnv f v) kont

eval :: MonadEval m => Expr -> m Value
eval e =
  case e of
   VarE x -> do
     m <- lookupEnv x
     case m of
      Just ans -> return ans
      Nothing -> runtimeError $ RuntimeError $ "unbound variable " ++ show x
   ValE ans -> return ans
   LamE bnd -> do
     (x, e') <- U.unbind bnd
     env <- rho
     return $ CloV (U.bind (env, x) e')
   AppE e1 e2 -> do
     vclo <- eval e1
     ((env, x), e') <- case vclo of
       CloV bnd -> U.unbind bnd
       _ -> runtimeError $ RuntimeError $ "expected closure, got " ++ show vclo
     varg <- eval e2
     localEnv (const $ extendEnv env (x, varg)) $ eval e'
   _ -> runtimeError $ RuntimeError "eval unimplemented"

runE :: Env -> E a -> Either RuntimeError a
runE env comp = runExcept $ runReaderT (U.runFreshMT comp) env

runEval :: Env -> Expr -> Either RuntimeError Value
runEval env = runE env . eval 
     
emptyEnv :: Env
emptyEnv = Env M.empty

extendEnv :: Env -> (Var, Value) -> Env
extendEnv env (x, v) = Env $ M.insert x (U.embed v) (envMapping env)

examples :: [Either RuntimeError Value]
examples =
  [
    runEval emptyEnv (AppE (AppE (LamE $ U.bind (U.s2n "x") $ LamE $ U.bind (U.s2n "y") $ VarE $ U.s2n "y")
                            (ValE $ LitV $ IntL 1))
                      (ValE $ LitV $ RealL 2))
  , runEval emptyEnv (AppE (AppE (LamE $ U.bind (U.s2n "x") $ LamE $ U.bind (U.s2n "y") $ VarE $ U.s2n "x")
                            (ValE $ LitV $ IntL 1))
                      (ValE $ LitV $ RealL 2))
  , runEval emptyEnv (AppE (AppE (LamE $ U.bind (U.s2n "x") $ VarE $ U.s2n "x")
                            (ValE $ LitV $ IntL 1))
                      (ValE $ LitV $ RealL 2))
  ]
