-- | Translate an 'Insomnia.Toplevel.Toplevel' to an
-- 'Insomnia.Interp.Lam.Program' for evaluation.
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module Insomnia.Interp.ToLam where

import Prelude hiding (foldr)

import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Monoid (Monoid(..), (<>), Endo(..))
import Data.List (intercalate)
import Data.Foldable (Foldable(foldr))

import qualified Unbound.Generics.LocallyNameless as U

-- "I"nput language
import qualified Insomnia.Toplevel as I
import qualified Insomnia.Identifier as I
import qualified Insomnia.Model as I
import qualified Insomnia.TypeDefn as I
import qualified Insomnia.Expr as I

-- "O"output language
import qualified Insomnia.Interp.Lam as O
import  Insomnia.Common.Literal

-- @foldlMapCont (\kont -> interposeOn (kont initialSummary))
-- eachItemCPS items initialKont@ is a fold over @items@ in
-- continuation-passing style that builds up a monoidal summary and
-- additionally we get to interpose some computation on the final
-- continuation.
foldlMapCont :: (Monoid s, Foldable t)
                => ((s -> u) -> res)
                -> (a -> (s -> res) -> res)
                -> t a
                -> (s -> u)
                -> res
foldlMapCont f0 f = foldr g f0
  where
    g x frest k =
      f x $ \s1 ->
      frest $ \s2 ->
      k (s1 <> s2)

type Old a = a

data TranslationState = TranslationState {
  _tstModels :: M.Map I.Path (Either I.Path I.Model) -- either an alias or a definition
  , _tstQVarNames :: M.Map I.QVar O.Var
  , _tstLocalNames :: M.Map I.Var O.Var
  , _tstConInfo :: M.Map I.ValConPath (O.ConId, Int)
  }

$(makeLenses ''TranslationState)

class (U.Fresh m) => Translate m where
  recallModel :: I.Path -> m (Either I.Path I.Model)
  rememberModel :: I.Path -> (Either I.Path I.Model) -> m a -> m a
  -- generate the name in the output language corresponding to the given field,
  -- or return the previously generated such name, if available.
  named :: I.QVar -> (O.Var -> m a) -> m a
  -- @reexposeNamed oldQV newQV@ makes @newQV@ map to the same output language variable
  -- that @oldQV@ maps to.
  reexposeNamed :: Old I.QVar -> I.QVar -> m ()
  nameLocal :: I.Var -> m O.Var
  -- return the translated name of the given value constructor, along
  -- with its arity.
  recallConPathInfo :: I.ValConPath -> m (O.ConId,  Int)
  rememberConInfo :: I.ValConPath -> (O.ConId, Int) -> m ()

class LocalTranslate m where
  currentModulePath :: m I.Path

type TranslationMonad = StateT TranslationState U.FreshM

instance Translate (StateT TranslationState U.FreshM) where
  recallModel modPath = do
    mans <- use (tstModels . at modPath)
    case mans of
     Just ans -> return ans
     Nothing -> fail ("internal error: expected to find model with name " ++ show modPath)
  rememberModel modPath mdl kont = do
    (tstModels . at modPath) ?= mdl
    kont
  reexposeNamed oldQV newQV = do
    named oldQV $ \x -> do
      (tstQVarNames . at newQV) ?= x
  named qv kont = do
    mx <- use (tstQVarNames . at qv)
    x <- case mx of
     Just x -> return x
     Nothing -> do
       x <- inventFreshQVarName qv
       (tstQVarNames . at qv) ?= x
       return x
    kont x
  nameLocal v = do
    mx <- use (tstLocalNames . at v)
    case mx of
      Just x -> return x
      Nothing -> do
        -- change from Name I.Expr to Name O.Expr
        let xstale = (U.string2Name . U.name2String) v
        x <- U.fresh xstale
        (tstLocalNames . at v) ?= x
        return x
  recallConPathInfo c = do
    mci <- use (tstConInfo . at c)
    case mci of
     Just ans -> return ans
     Nothing -> do
       info <- use tstConInfo
       fail ("internal error: expected to find value constructor with name "
             ++ show c
             ++ " in " ++ show info)
  rememberConInfo c info =
    tstConInfo . at c ?= info

instance Translate m => Translate (ReaderT r m) where
  recallModel = lift . recallModel
  rememberModel p m c = do
    r <- ask
    lift (rememberModel p m (runReaderT c r))
  named q c = do
    r <- ask
    lift (named q (\q' -> runReaderT (c q') r))
  reexposeNamed o q = lift (reexposeNamed o q)
  nameLocal = lift . nameLocal
  recallConPathInfo = lift . recallConPathInfo
  rememberConInfo p info = lift (rememberConInfo p info)

instance Monad m => LocalTranslate (ReaderT I.Path m) where
  currentModulePath = ask

recallConInfo :: (Translate m, LocalTranslate m)
                 => I.ValueConstructor
                 -> m (O.ConId, Int)
recallConInfo vc = do
  vcp <- case vc of
   I.VCLocal vcName -> do
     modPath <- currentModulePath
     let shortName = U.name2String vcName
         vcp = I.ValConPath modPath shortName
     return vcp
   I.VCGlobal vcp -> return vcp
  recallConPathInfo vcp 

inventFreshQVarName :: U.Fresh m => I.QVar -> m O.Var
inventFreshQVarName (I.QVar modPath f) =
  -- M.N.P.f becomes M_N_P_f
  let (h, p) = I.pathHeadSkelForm modPath
      p0 = U.name2String h
      s = intercalate "_" (p0:p ++ [f])
      v_ = U.string2Name s
  in U.fresh v_
  
toConId :: I.ValConPath -> O.ConId
toConId (I.ValConPath p vc) =
  let (h, ps) = I.pathHeadSkelForm p
      p0 = U.name2String h
  in intercalate "_" (p0:ps ++ [vc])

runTranslation :: TranslationMonad a -> a
runTranslation comp = U.runFreshM (evalStateT comp initialState)
  where
    initialState = TranslationState mempty mempty mempty mempty

translateToplevel :: I.Toplevel -> O.Program
translateToplevel = runTranslation . toplevel


-- a target program in difference list form: translating each
-- input language form should return a transformation that prepends some number of
-- definitions to the given output program.
type DProgram = Endo O.Program

toplevel :: Translate m => I.Toplevel -> m O.Program
toplevel (I.Toplevel its_) = do
  d <- foldlMapCont
       (\k -> k mempty)
       toplevelItem
       its_
       return
  return $ appEndo d (O.EvalP okVal)
  where
    okVal :: O.Expr
    okVal = O.ValE (O.LitV $ IntL 0)

toplevelItem :: Translate m => I.ToplevelItem -> (DProgram -> m DProgram) -> m DProgram
toplevelItem it kont =
  case it of
  -- model types are just erased, they do not have runtime content
   I.ToplevelModelType {} -> kont mempty
  -- models translate to their constituent definitions.
   I.ToplevelModel ident me -> modelExpr (I.IdP ident) me False kont

modelExpr :: Translate m
             => I.Path
             -> I.ModelExpr
             -> Bool -- ^ generate new definitions?
             -> (DProgram -> m DProgram)
             -> m DProgram
modelExpr modPath me isGenerative kont =
  case me of
   I.ModelId oldPath -> do
     mdlOrAlias <- recallModel oldPath
     case mdlOrAlias of
      Left alias -> modelExpr modPath (I.ModelId alias) isGenerative kont
      Right mdl -> if not isGenerative
                   then
                      -- just an alias for existing definitions.  Call
                      -- the continuation in an environment where
                      -- additional input program names map to some
                      -- output program names.
                     reexpose mdl oldPath modPath kont
                   else
                     -- generative construction; emit new definitions
                     -- for a new copy of the model.
                     model modPath mdl kont
   I.ModelAssume {} -> kont mempty -- should expose some names here?
   I.ModelSeal me' _mt ->
     -- sealing is generative.  We want new copies now.
     modelExpr modPath me' True kont
   I.ModelStruct mdl ->
     model modPath mdl kont

-- | given an existing model and its path, and a new path, expose all
-- the contents of the old model using the new names.  This is the
-- non-generative case.  We are just mapping additional input language
-- names to the same output language values.
reexpose :: Translate m
            => Old I.Model
            -> Old I.Path
            -> I.Path
            -> (DProgram -> m DProgram)
            -> m DProgram
reexpose (I.Model decls) oldPath newPath =
  foldlMapCont
  (\kont ->
    -- in the continuation, remember that the new path is an alias for the old path
    rememberModel newPath (Left oldPath) $ kont mempty)
  (reexposeDecl oldPath newPath)
  decls

reexposeDecl :: Translate m
                => Old I.Path
                -> I.Path
                -> Old I.Decl
                -> (DProgram -> m DProgram)
                -> m DProgram
reexposeDecl oldPath newPath d_ kont =
  case d_ of
   I.ValueDecl f _vd -> do
     reexposeNamed (I.QVar oldPath f) (I.QVar newPath f)
     kont mempty
   I.TypeDefn {} -> error "unimplemented translation to reexpose a TypeDefn (in particular, value constructors)"
   I.TypeAliasDefn {} -> kont mempty
   I.SubmodelDefn f _me -> do
     let oldSubpath = I.ProjP oldPath f
         newSubpath = I.ProjP newPath f
     mans <- recallModel oldSubpath
     -- if the old subpath was itself an alias, continue with that alias
     -- otherwise, reexpose the submodel that the old subpath maps to.
     case mans of
      Left alias -> modelExpr newSubpath (I.ModelId alias) False kont
      Right mdl -> reexpose mdl oldSubpath newSubpath kont

-- | given a model and a new path, expose all the contents of the
-- model using the new names.  This is the generative case.  If the
-- model has side effects, or generates new data type definitions,
-- they will be present in the output language program at the current
-- point in the translation.
model :: Translate m
         => I.Path
         -> I.Model
         -> (DProgram -> m DProgram)
         -> m DProgram
model modPath mdl@(I.Model decls_) = 
  foldlMapCont
  (\kont ->
    -- in translating the rest of the input program, remember that the
    -- current path refers to the model we started with.
    rememberModel modPath (Right mdl) $ kont mempty)
  (decl modPath)
  decls_

decl :: Translate m
        => I.Path
        -> I.Decl
        -> (DProgram -> m DProgram)
        -> m DProgram
decl modPath d_ kont = do
  case d_ of
   I.ValueDecl f vd -> valueDecl modPath f vd kont
   I.TypeDefn f td -> typeDefn modPath f td kont
   I.TypeAliasDefn {} -> kont mempty
   I.SubmodelDefn f me ->
     modelExpr (I.ProjP modPath f) me False kont

typeDefn :: Translate m
            => I.Path
            -> I.Field
            -> I.TypeDefn
            -> (DProgram -> m DProgram)
            -> m DProgram
typeDefn modPath typeField td_ kont =
  case td_ of
   I.DataDefn dd -> dataDefn modPath typeField dd kont
   I.EnumDefn {} -> kont mempty

dataDefn :: Translate m
            => I.Path
            -> I.Field
            -> I.DataDefn
            -> (DProgram -> m DProgram)
            -> m DProgram
dataDefn modPath _typeField dd_ kont = do
  (_tvks, cnstrs) <- U.unbind dd_
  foldlMapCont (\k -> k mempty)
    (constructorDef modPath)
    cnstrs
    kont

constructorDef :: Translate m
                  => I.Path
                  -> I.ConstructorDef
                  -> (DProgram -> m DProgram)
                  -> m DProgram
constructorDef modPath (I.ConstructorDef valConName args) kont =
  let arity = length args
      shortName = U.name2String valConName
      vcp = I.ValConPath modPath shortName
      conId = toConId vcp
  in do
    rememberConInfo vcp (conId, arity)
    kont mempty
  
  

valueDecl :: Translate m
             => I.Path
             -> I.Field
             -> I.ValueDecl
             -> (DProgram -> m DProgram)
             -> m DProgram
valueDecl modPath valField vd_ kont =
  case vd_ of
   I.ValDecl e -> do
     e' <- runReaderT (expr e) modPath
     named (I.QVar modPath valField) $ \x ->
       kont (emitVarDefn x e')
   I.FunDecl e -> do
     e' <- runReaderT (expr e) modPath
     named (I.QVar modPath valField) $ \f ->
       kont (emitFunDefn f e')
   I.SigDecl {} ->
     named (I.QVar modPath valField) $ \_ -> kont mempty
   I.SampleDecl {} -> error "unimplemented translation form SampleDecl"

expr :: (Translate m, LocalTranslate m)
        => I.Expr
        -> m O.Expr
expr e_ =
  case e_ of
   I.V v -> do
     x <- nameLocal v
     return (O.VarE x)
   I.Q qid  ->
     named qid $ \x -> return (O.VarE x)
   I.C con -> do
     (c, arity) <- recallConInfo con
     return (constructor c arity)
   I.L lit -> return (O.ValE $ O.LitV lit)
   I.App e1 e2 -> do
     e1' <- expr e1
     e2' <- expr e2
     return $ O.AppE e1' e2'
   I.Lam bnd -> do
     ((v, _), e) <- U.unbind bnd
     x <- nameLocal v
     e' <- expr e
     return $ O.LamE $ U.bind x e'
   I.Ann e _ty -> expr e
   I.Case e clauses -> do
     e' <- expr e
     clauses' <- mapM clause clauses
     return $ O.CaseE e' clauses'
   I.Let bnd -> do
     (bdgs, body) <- U.unbind bnd
     bindings bdgs $ \bdgs' -> do
       body' <- expr body
       return $ O.LetE $ U.bind bdgs' body'

bindings :: (Translate m, LocalTranslate m)
            => I.Bindings
            -> (O.Bindings -> m a)
            -> m a
bindings bdgs_ kont =
  case bdgs_ of
   I.NilBs -> kont O.NilBs
   I.ConsBs rbd ->
     let (bdg, bdgs) = U.unrebind rbd
     in
      binding bdg $ \bdg' ->
      bindings bdgs $ \bdgs' ->
      kont (O.ConsBs $ U.rebind bdg' bdgs')

binding :: (Translate m, LocalTranslate m)
           => I.Binding
           -> (O.Binding -> m a)
           -> m a
binding b_ kont =
  case b_ of
   I.ValB (x, _ty) e_ -> do
     x' <- nameLocal x
     let e = U.unembed e_
     e' <- expr e
     kont (O.ValB x' $ U.embed e')
   I.SampleB {} -> error "unimplemented translation for SampleB"
   I.TabB x _tabfun -> do
     x' <- nameLocal x
     kont (O.ValB x' $ U.embed $ error "unimplemented translation for TabB")


clause :: (Translate m, LocalTranslate m)
          => I.Clause
          -> m O.Clause
clause (I.Clause bnd) = do
  (pat, body) <- U.unbind bnd
  pattern pat $ \pat' -> do
    body' <- expr body
    return (O.Clause $ U.bind pat' body')

pattern :: (Translate m, LocalTranslate m)
           => I.Pattern
           -> (O.Pattern -> m a)
           -> m a
pattern p_ kont =
  case p_ of
   I.WildcardP -> kont O.WildP
   I.VarP x -> do
     x' <- nameLocal x
     kont (O.VarP x')
   I.ConP c_ pats -> do
     let c = U.unembed c_
     (c', _) <- recallConInfo c
     patterns pats $ \pats' ->
       kont (O.ConP (U.embed c') pats')
   I.RecordP {} -> error "unimplemented translation for RecordP"

patterns :: (Translate m, LocalTranslate m)
            => [I.Pattern]
            -> ([O.Pattern] -> m a)
            -> m a
patterns [] kont = kont []
patterns (pat:pats) kont =
  pattern pat $ \pat' ->
  patterns pats $ \pats' ->
  kont (pat' : pats')

-- | given a conId and an arity N, returns
-- \x1 . ... \xN . c@[x1, ..., xN]
constructor :: O.ConId -> Int -> O.Expr
constructor conId n =
  let xs = map (U.makeName "a") [1 .. fromIntegral n]
      body = O.ConE conId (map O.VarE xs)
  in wrap body xs
  where
    wrap e [] = e
    wrap e (y:ys) =
      wrap (O.LamE $ U.bind y e) ys

    
emitVarDefn :: O.Var -> O.Expr -> DProgram
emitVarDefn x e = emitDefinition (O.VarDefn x (U.embed e))

emitFunDefn :: O.Var -> O.Expr -> DProgram
emitFunDefn f e = emitDefinition (O.FunDefn f (U.embed e))

emitDefinition :: O.Definition -> DProgram
emitDefinition d = Endo (O.DefineP . U.bind d)
