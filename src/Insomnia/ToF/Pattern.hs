-- | Pattern Translation
--
--
-- This is a naive, but straightforward compilation of pattern match to sum and product types.
-- 
-- We translate
--  case x of {p -> e' | ps}
-- into
--   let
--     kf = \() -> case x of ps
--   in
--     m 
--  where  x match p then Succes e' else FailCont (kf x) ---> m
--
-- We translate (case x of {} : T) to 'abort T'
--
-- The judgment  x match (p -> e) then ks else kf  ---> m
-- is defined as as
--    x match {f1 = p1, ..., fN = pN) then ks else kf ---> let ... xi = x.fi ... in m
--      where x1 match p1 then (x2 match p2 then ... xN match pN then ks) else kf ---> m
--    x match Con p1 ... pN then ks else kf ---> case coerceOutδ x of { fCon x1 .... xN -> m | |kf| }
--      where x1 match p1 then (x2 match p2 then ... xN match pN then ks) else kf ---> m
--    x match _ then Success e else kf ---> |e|
--    x match _ then (y match p then ks) else kf  ---> m
--      where y match p then ks else kf ---> m
--    x match y then Success e else kf ---> |e[x/y]|
--    x match y then (y' match p then ks) else kf ---> m
--      where y'[x/y] match p[x/y] then ks[x/y] else kf ---> m
--
-- coerceOutδ is the term (δ.data [λα:⋆.α]) that witnesses
-- the unrolling from δ τs to
-- Sum { fCon1 : σ1[τs/βs], ... fConN : σN[τs/βs] }
-- for the datatype δ β = fCon1 : σ1 | ... | fConN : σN
{-# LANGUAGE ViewPatterns, DeriveDataTypeable, DeriveGeneric #-}
module Insomnia.ToF.Pattern where

import Control.Lens
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Monoid (Monoid(..), Endo(..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.ToF.Env

import Insomnia.Expr
import Insomnia.Types (Label(..))

import qualified FOmega.Syntax as F

import Insomnia.ToF.Type (type')
import Insomnia.ToF.Expr (expr, valueConstructor)

patternTranslation :: ToF m
                      => Var
                      -> [Clause]
                      -> F.Type
                      -> m (U.Bind F.Var F.Term)
patternTranslation v clauses_ resultTy =
  withFreshName (U.name2String v) $ \v' -> 
  local (valEnv %~ M.insert v (v', LocalTermVar)) $ do
    let defaultClause = F.DefaultClause $ Left $ F.CaseMatchFailure resultTy
    j <- patternTranslation' v' clauses_ defaultClause
    m <- translateJob j
    return $ U.bind v' m

patternTranslation' :: ToF m
                       => F.Var
                       -> [Clause]
                       -> F.DefaultClause
                       -> m Job
patternTranslation' v' clauses_ defaultClause =
  case clauses_ of
   [] -> return $ FailJ v' $ FailCont defaultClause
   [clause] -> do
     task <- clauseToTask v' clause
     return $ TryTaskJ task (FailJ v' $ FailCont defaultClause)
   (clause:clauses') ->  do
     js <- patternTranslation' v' clauses' defaultClause
     task <- clauseToTask v' clause
     return $ TryTaskJ task js
     
data Task =
  SuccessTk !Expr
  | LetTk !F.Var (U.Bind Var Task)
  | ProjectTk !F.Var (U.Bind [(U.Embed F.Field, F.Var)] Task)
  | SplitTk !F.Var !InstantiationCoercion !DtInOut ![SplitTaskInfo]
    -- try each split task in turn until one succeeds, or else fail.
    -- Note that we expect the split tasks to share a failure
    -- continuation
    deriving (Typeable, Generic, Show)

-- wrapper around an extracted datatype injection/projection term
newtype DtInOut = DtInOut F.Term
                deriving (Typeable, Generic, Show)

-- split the subject by matching on the given value constructor and
-- then running the continuation task.
data SplitTaskInfo =
  SplitTaskInfo !F.Field  (U.Bind [(U.Embed F.Field, F.Var)] Task)
  deriving (Typeable, Generic, Show)

data Job =
  FailJ !F.Var !FailCont
  | TryTaskJ !Task !Job -- try task otherwise job
  deriving (Typeable, Generic, Show)

newtype FailCont = FailCont F.DefaultClause
                   deriving (Show, Generic, Typeable)

instance U.Alpha Task
instance U.Alpha SplitTaskInfo
instance U.Alpha DtInOut
instance U.Alpha Job
instance U.Alpha FailCont

clauseToTask :: ToF m => F.Var -> Clause -> m Task
clauseToTask v' (Clause bnd) =
  let (pat, e) = UU.unsafeUnbind bnd
      sk = SuccessTk e
  in patternToTask v' pat sk

-- | @patternToTask y pat j@ matches the subject @y@ with pattern @pat@ and the continues with job @j@
patternToTask :: ToF m => F.Var -> Pattern -> Task -> m Task
patternToTask v' pat sj =
  case pat of
   WildcardP -> return $ sj
   VarP y -> return $ LetTk v' (U.bind y sj)
   RecordP lps -> 
     let fps = map (\(U.unembed -> (Label lbl), x) -> (F.FUser lbl, x)) lps
     in freshPatternVars fps $ \fys yps -> do
       task' <- matchTheseAndThen yps sj
       return $ ProjectTk v' (U.bind fys task')
   ConP (U.unembed -> vc) (U.unembed -> mco) ps -> do
     (dtInOut, f) <- valueConstructor vc
     co <- case mco of
       Nothing -> throwError "ToF.Pattern.translateTask: Expected a type instantiation annotation on constructor pattern"
       Just co -> return co
     let fps = zip (map F.FTuple [0..]) ps
     freshPatternVars fps $ \fys yps -> do
       task' <- matchTheseAndThen yps sj
       return $ SplitTk v' co (DtInOut dtInOut) [SplitTaskInfo f (U.bind fys task')]

matchTheseAndThen :: ToF m => [(F.Var, Pattern)] -> Task -> m Task
matchTheseAndThen [] sk = return sk
matchTheseAndThen ((v',pat):rest) sk = do
  task' <- matchTheseAndThen rest sk
  patternToTask v' pat task'

translateJob :: ToF m =>
                Job -> m F.Term
translateJob (FailJ v' (FailCont defaultClause)) =
  return $ F.Case (F.V v') [] defaultClause     
translateJob (TryTaskJ task (FailJ _subj fk)) =
  translateTask task fk
translateJob (TryTaskJ task j@(TryTaskJ {})) = do
  mfk <- translateJob j
  let fk = FailCont $ F.DefaultClause $ Right mfk
  translateTask task fk

translateTask :: ToF m =>
                Task -> FailCont -> m F.Term
translateTask (SuccessTk e) _fk = expr e
translateTask (LetTk v' bnd) fk =
  U.lunbind bnd $ \(y, sk) ->
  -- instead of doing substitution or anything like that, just
  -- run the rest of the translation in an env where y is also mapped to v'
  local (valEnv %~ M.insert y (v', LocalTermVar))
  $ translateTask sk fk
translateTask (ProjectTk v' bnd) fk =
  U.lunbind bnd $ \(fys, sk) -> do
    m_ <- translateTask sk fk
    return (projectFields fys v' m_)
translateTask (SplitTk v' co dtInOut splitTasks) fk = do
  clauses <- mapM (translateSplitTask fk) splitTasks
  caseConstruct v' dtInOut co clauses fk

translateSplitTask :: ToF m =>
                      FailCont 
                      -> SplitTaskInfo
                      -> m F.Clause
translateSplitTask fk (SplitTaskInfo f bnd) =
  U.lunbind bnd $ \(fys, sk) -> do
    m_ <- translateTask sk fk
    clauseConstruct f fys m_

clauseConstruct :: ToF m
                   => F.Field
                   -> [(U.Embed F.Field, F.Var)]
                   -> F.Term
                   -> m F.Clause
clauseConstruct f fys successTm =
  withFreshName "z" $ \z ->
    return $ F.Clause f $ U.bind z (projectFields fys z successTm)

-- | caseConstruct y Con {0 = y1, ..., n-1 = yN} ms mf
-- builds the term
--   case outδ y of { Con z -> let {y1, ... yN} = z in ms | _ -> mf }
-- where outδ = δ.data [λα:⋆.α] and "let {vs...} = z in m" is sugar for lets and projections
caseConstruct :: ToF m
                 => F.Var
                 -> DtInOut
                 -> InstantiationCoercion
                 -> [F.Clause]
                 -> FailCont
                 -> m F.Term
caseConstruct ysubj (DtInOut dtInOut)
  (InstantiationSynthesisCoercion _ tyargs _) clauses (FailCont defaultClause) = do
  (tyArgs', ks) <- liftM unzip $ mapM type' tyargs
  let
    dtOut = dtInOut `F.Proj` F.FDataOut
    -- For  polymorphic types constructors we need to build a higher-order context.
    -- Consider the clause: case l of (Cons x ·¢· [Int] xs) -> x + sum xs 
    -- In that case, we need to translate to:
    --    case Δ.out [λ (δ:⋆→⋆) . δ Int] l of (Cons z) -> let x = z.0 xs = z.1 in ...
    -- That is, we have to know that the polymorphic type Δ was instantiated with τs
    -- and the context should be λ (δ:κ1→⋯κN→⋆) . (⋯ (δ τ1) ⋯ τN)
    --
    here = let d = U.s2n "δ"
               kD = (ks `F.kArrs` F.KType)
               appdD = (F.TV d) `F.tApps` tyArgs'
           in F.TLam $ U.bind (d, U.embed kD) appdD
    subject = F.App (F.PApp dtOut here) (F.V ysubj)
  return $ F.Case subject clauses defaultClause


freshPatternVars :: ToF m
                    => [(F.Field, Pattern)]
                    -> ([(U.Embed F.Field, F.Var)] -> [(F.Var, Pattern)] -> m ans)
                    -> m ans
freshPatternVars [] kont = kont [] []
freshPatternVars ((f, p):fps) kont =
  let n = case f of
           F.FUser s -> s
           _ -> "ω" -- can't happen, I think
  in withFreshName n $ \y ->
  freshPatternVars fps $ \fys yps ->
  kont ((U.embed f,y):fys) ((y,p):yps)
  

-- | projectFields {... fi = yi ... } x body
-- returns
-- let ... let yi = x . fi in ... in body
projectFields :: [(U.Embed F.Field, F.Var)] -> F.Var -> F.Term -> F.Term
projectFields fys vsubj mbody =
  let
    ms = map (\(f, y) ->
               let
                 p = F.Proj (F.V vsubj) (U.unembed f)
               in Endo (F.Let . U.bind (y, U.embed p)))
         fys
  in
   appEndo (mconcat ms) mbody
