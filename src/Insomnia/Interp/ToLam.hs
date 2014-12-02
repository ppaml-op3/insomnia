-- | Translate an 'Insomnia.Toplevel.Toplevel' to an
-- 'Insomnia.Interp.Lam.Program' for evaluation.
module Insomnia.Interp.ToLam where

import Data.Monoid (Monoid(..), (<>), Endo(..))

import qualified Unbound.Generics.LocallyNameless as U

-- "I"nput language
import qualified Insomnia.Toplevel as I
import qualified Insomnia.Identifier as I
import qualified Insomnia.Model as I
import qualified Insomnia.Types as I
import qualified Insomnia.Expr as I

-- "O"output language
import qualified Insomnia.Interp.Lam as O
import  Insomnia.Common.Literal

type Old a = a

class (U.Fresh m) => Translate m where
  reexpose :: Old I.Path -> I.Path -> m a -> m a
  recallModel :: I.Path -> m I.Model
  rememberModel :: I.Path -> I.Model -> m a -> m a
  -- generate the name in the output language corresponding to the given field,
  -- or return the previously generated such name, if available.
  named :: I.QVar -> (O.Var -> m a) -> m a
  nameLocal :: I.Var -> m O.Var
  -- return the translated name of the given value constructor, along
  -- with its arity.
  recallNamedCon :: I.Con -> m (O.ConId,  Int)

-- a target program in difference list form: translating each
-- input language form should return a transformation that prepends some number of
-- definitions to the given output program.
type DProgram = Endo O.Program

toplevel :: Translate m => I.Toplevel -> m O.Program
toplevel (I.Toplevel its_) = do
  d <- go its_
  return $ appEndo d (O.EvalP okVal)
  where
    go :: Translate m => [I.ToplevelItem] -> m DProgram
    go [] = return mempty
    go (it:its) = 
      toplevelItem it (\pgm -> do
                          pgm' <- go its
                          return (pgm <> pgm'))
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
   I.ModelId oldPath ->
     if not isGenerative
        -- just an alias for existing definitions.  Call the continuation
        -- in an environment where additional input program names map to
        -- some output program names.
     then reexpose oldPath modPath $ kont mempty
     else do
       -- generative construction; emit new definitions for a new copy of the model.
       mdl <- recallModel oldPath
       model modPath mdl kont
   I.ModelAssume {} -> kont mempty -- should expose some names here?
   I.ModelSeal me' _mt ->
     -- sealing is generative.  We want new copies now.
     modelExpr modPath me' True kont
   I.ModelStruct mdl ->
     model modPath mdl kont

model :: Translate m
         => I.Path
         -> I.Model
         -> (DProgram -> m DProgram)
         -> m DProgram
model modPath mdl@(I.Model decls_) = go decls_
  where
    go [] kont =
      -- in translating the rest of the input program,
      -- remember that the current path refers to the model we started with.
      rememberModel modPath mdl $ kont mempty
    go (d:ds) kont =
      decl modPath d (\pgm ->
                       go ds $ \pgm' ->
                       kont (pgm <> pgm'))

decl :: Translate m
        => I.Path
        -> I.Decl
        -> (DProgram -> m DProgram)
        -> m DProgram
decl modPath d_ kont =
  case d_ of
   I.ValueDecl f vd ->
     valueDecl modPath f vd kont
   I.TypeDefn {} -> error "unimplemtned translation for TypeDefn (need to generate value constructor names)"
   I.TypeAliasDefn {} -> kont mempty
   I.SubmodelDefn f me ->
     modelExpr (I.ProjP modPath f) me False kont

valueDecl :: Translate m
             => I.Path
             -> I.Field
             -> I.ValueDecl
             -> (DProgram -> m DProgram)
             -> m DProgram
valueDecl modPath valField vd_ kont =
  case vd_ of
   I.ValDecl e -> do
     e' <- expr e
     named (I.QVar modPath valField) $ \x ->
       kont (emitVarDefn x e')
   I.FunDecl e -> do
     e' <- expr e
     named (I.QVar modPath valField) $ \f ->
       kont (emitFunDefn f e')
   I.SigDecl {} ->
     named (I.QVar modPath valField) $ \_ -> kont mempty
   I.SampleDecl {} -> error "unimplemented translation form SampleDecl"

expr :: Translate m
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
     (c, arity) <- recallNamedCon con
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
