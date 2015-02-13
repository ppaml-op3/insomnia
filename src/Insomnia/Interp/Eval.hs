{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Insomnia.Interp.Eval where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error.Class
import qualified Control.Monad.State.Lazy as LazyST
import Control.Monad.Except

import qualified Data.Map as M
import Data.Monoid (Endo(..))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Literal
import Insomnia.Common.Telescope
import Insomnia.Interp.Lam

import qualified Insomnia.Interp.PMonad as PM

data RuntimeError =
  UnboundVariableRE !Var
  | AppliedUnexpectedRE !Value
  | ExpectedRealRE !Value
  | NoCaseMatchedRE !Value
  | ConstructorArityMismatchRE !ConId ![Value] ![Pattern]
  | FunDefnNotLamRE !Expr
  | InternalErrorRE !String

instance Show RuntimeError where
  show (UnboundVariableRE v) = "Unbound variable: " ++ show v
  show (AppliedUnexpectedRE value) = "In application position, expected closure, got: " ++ show value
  show (ExpectedRealRE value) = "Expected a real value, got: " ++ show value
  show (InternalErrorRE msg) = "Internal error in evaluator, " ++ msg
  show (NoCaseMatchedRE value) = "Case expression had no clauses that matched " ++ show value
  show (ConstructorArityMismatchRE conId vals pats) =
    "Constructor " ++ show conId ++ " applied to "
    ++ show (length vals) ++ " values, but pattern " ++ show pats
    ++ " only matches " ++ show (length pats) ++ " arguments"
  show (FunDefnNotLamRE e) =
    "In function definition, expected a lambda expression, but got " ++ show e

class (Applicative m, Monad m, U.Fresh m, PM.ProbabilityMonad m) => MonadEval m where
  rho :: m Env
  lookupEnv :: Var -> m (Maybe Value)
  lookupEnv v = fmap (fmap U.unembed . M.lookup v . envMapping) rho
  localEnv :: (Env -> Env) -> m a -> m a
  runtimeError :: RuntimeError -> m a
    
type E = U.FreshMT (ReaderT Env (ExceptT RuntimeError PM.Sample))
  
instance PM.ProbabilityMonad m => PM.ProbabilityMonad (LazyST.StateT s m) where
  choose p c1 c2 = do
    s <- LazyST.get
    (x, s') <- lift $ PM.choose p (LazyST.runStateT c1 s) (LazyST.runStateT c2 s)
    LazyST.put s'
    return x

instance PM.ProbabilityMonad m => PM.ProbabilityMonad (U.FreshMT m) where
  choose p c1 c2 = U.FreshMT $ PM.choose p (U.unFreshMT c1) (U.unFreshMT c2)

instance PM.ProbabilityMonad m => PM.ProbabilityMonad (ReaderT r m) where
  choose p c1 c2 = ask >>= \r -> lift $ PM.choose p (runReaderT c1 r) (runReaderT c2 r)

instance PM.ProbabilityMonad m => PM.ProbabilityMonad (ExceptT e m) where
  choose p c1 c2 = do
    errOrOk <- lift $ PM.choose p (runExceptT c1) (runExceptT c2)
    case errOrOk of
     Left err -> throwError err
     Right ok -> return ok

instance MonadEval (U.FreshMT (ReaderT Env (ExceptT RuntimeError PM.Sample))) where
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
      _ -> runtimeError (FunDefnNotLamRE e)
eval :: MonadEval m => Expr -> m Value
eval e =
  case e of
   VarE x -> do
     m <- lookupEnv x
     case m of
      Just ans -> return ans
      Nothing -> runtimeError $ UnboundVariableRE x
   ValE ans -> return ans
   LamE bnd -> do
     (x, e') <- U.unbind bnd
     env <- rho
     return $ CloV (U.bind (env, x) e')
   AppE e1 e2 -> do
     vclo <- eval e1
     ((env, x), e') <- case vclo of
       CloV bnd -> U.unbind bnd
       _ -> runtimeError $ AppliedUnexpectedRE vclo
     varg <- eval e2
     localEnv (const $ extendEnv x varg env) $ eval e'
   ConE conId es -> do
     vs <- mapM eval es
     return $ ConV conId vs
   CaseE e0 clauses -> do
     v <- eval e0
     matchClauses v clauses (runtimeError $ NoCaseMatchedRE v)
   ChooseE eprob etrue efalse -> do
     vprob <- eval eprob
     case vprob of
      LitV (RealL p) -> PM.choose p (eval etrue) (eval efalse)
      _ -> runtimeError $ ExpectedRealRE vprob
   LetE bnd -> do
     (bdgs, body) <- U.unbind bnd
     evalBindings bdgs (eval body)
   -- _ -> runtimeError $ InternalErrorRE ("eval unimplemented for " ++ show e)

evalBindings :: MonadEval m
                => Bindings
                -> m a
                -> m a
evalBindings (Bindings t) = appEndo (foldMapTelescope (Endo . evalBinding) t) 

evalBinding :: MonadEval m
               => Binding
               -> m a
               -> m a
evalBinding (ValB x e_) kont = do
  let e = U.unembed e_
  v <- eval e
  localEnv (extendEnv x v) kont

matchClauses :: MonadEval m => Value -> [Clause] -> m Value -> m Value
matchClauses _value [] fk = fk
matchClauses value (clause:clauses) fk =
  matchClause value clause (matchClauses value clauses fk)

matchClause :: MonadEval m => Value -> Clause -> m Value -> m Value
matchClause v (Clause bnd) fk = do
  (pat, body) <- U.unbind bnd
  matchPattern v pat (eval body) fk

matchPattern :: MonadEval m => Value -> Pattern -> m a -> m a -> m a
matchPattern v pat sk fk =
  case pat of
   WildP -> sk
   VarP x -> localEnv (extendEnv x v) sk
   ConP conId_ pats ->
     let conId = U.unembed conId_
     in case v of
      ConV conId' vals | conId == conId' -> do
                           when (length pats /= length vals) $ do
                             runtimeError $ ConstructorArityMismatchRE conId vals pats
                           matchPatterns (zip vals pats) sk fk
      _ -> fk

matchPatterns :: MonadEval m => [(Value, Pattern)] -> m a -> m a -> m a
matchPatterns [] sk _fk = sk
matchPatterns ((v, pat):vps) sk fk =
  matchPattern v pat (matchPatterns vps sk fk) fk
                            

runE :: Env -> E a -> PM.Sample (Either RuntimeError a)
runE env comp = runExceptT $ runReaderT (U.runFreshMT comp) env

runEval :: Env -> Expr -> PM.Sample (Either RuntimeError Value)
runEval env = runE env . eval 
     
emptyEnv :: Env
emptyEnv = Env M.empty

extendEnv :: Var -> Value -> Env -> Env
extendEnv x v env = Env $ M.insert x (U.embed v) (envMapping env)

-- > mapM (fmap (take 2) . samples) examples
examples :: [PM.Sample (Either RuntimeError Value)]
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
