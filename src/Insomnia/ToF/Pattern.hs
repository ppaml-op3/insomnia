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
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.ToF.Env

import Insomnia.Expr
import Insomnia.TypeDefn (ValueConstructor)
import Insomnia.Types (Label(..))

import qualified FOmega.Syntax as F

import {-# SOURCE #-} Insomnia.ToF.Expr (expr)

patternTranslation :: ToF m
                      => Var
                      -> [Clause]
                      -> F.Type
                      -> m (U.Bind F.Var F.Term)
patternTranslation v clauses_ resultTy =
  withFreshName (U.name2String v) $ \v' -> 
  local (valEnv %~ M.insert v (v', LocalTermVar)) $ do
    m <- patternTranslation' v' clauses_ resultTy
    return $ U.bind v' m

patternTranslation' v' clauses_ resultTy =
  case clauses_ of
   [] -> return (F.abortThunk resultTy)
   (clause:clauses') -> do
     fkTerm <- withFreshName "_thunk" $ \thunkVar -> do
       mfk <- patternTranslation' v' clauses' resultTy
       return $ F.Lam $ U.bind (thunkVar, U.embed F.unitT) mfk
     let fk = FailCont $ F.App fkTerm F.unitVal
         job = clauseToJob v' clause
     translateJob job fk

     
data Job =
  SuccessJ !Expr
  | MatchAndThenJ  !F.Var !(U.Bind Pattern Job)
    deriving (Typeable, Generic, Show)

instance U.Alpha Job             

newtype FailCont = FailCont F.Term

clauseToJob :: F.Var -> Clause -> Job
clauseToJob v' (Clause bnd) =
  let (pat, e) = UU.unsafeUnbind bnd
  in MatchAndThenJ v' (U.bind pat $ SuccessJ e)

translateJob :: ToF m =>
                Job -> FailCont -> m F.Term
translateJob (SuccessJ e) _fk = expr e
translateJob j@(MatchAndThenJ v' bnd) fk =
  U.lunbind bnd $ \(p, sk) ->
  case p of
   WildcardP -> translateJob sk fk
   VarP y ->
     -- instead of doing substitution or anything like that, just
     -- run the rest of the translation in an env where y is also mapped to v'
     local (valEnv %~ M.insert y (v', LocalTermVar))
     $ translateJob sk fk
   RecordP lps ->
     let fps = map (\(U.unembed -> (Label lbl), x) -> (F.FUser $ lbl, x)) lps
     in freshPatternVars fps $ \fys yps -> do
       let j' = matchTheseAndThen yps sk
       m_ <- translateJob j' fk
       let m = projectFields fys v' m_
       return m
   ConP (U.unembed -> vc) ps ->
     let fps = zip (map F.FTuple [0..]) ps
     in freshPatternVars fps $ \fys yps -> do
       let j' = matchTheseAndThen yps sk
       m_ <- translateJob j' fk
       m <- caseConstruct v' vc fys m_ fk
       return m

-- | caseConstruct y Con {0 = y1, ..., n-1 = yN} ms mf
-- builds the term
--   case outδ y of { Con z -> let {y1, ... yN} = z in ms | _ -> mf }
-- where outδ = δ.data [λα:⋆.α] and "let {vs...} = z in m" is sugar for lets and projections
caseConstruct :: ToF m
                 => F.Var
                 -> ValueConstructor
                 -> [(F.Field, F.Var)]
                 -> F.Term
                 -> FailCont
                 -> m F.Term
caseConstruct vc fys successTm failCont = undefined

matchTheseAndThen :: [(F.Var, Pattern)] -> Job -> Job
matchTheseAndThen [] = id
matchTheseAndThen ((v',pat):rest) = MatchAndThenJ v' . U.bind pat . matchTheseAndThen rest

freshPatternVars :: ToF m
                    => [(F.Field, Pattern)]
                    -> ([(F.Field, F.Var)] -> [(F.Var, Pattern)] -> m ans)
                    -> m ans
freshPatternVars fps kont = undefined

-- | projectFields {... fi = yi ... } x body
-- returns
-- let ... let yi = x . fi in ... in body
projectFields :: [(F.Field, F.Var)] -> F.Var -> F.Term -> F.Term
projectFields fys vsubj mbody = undefined
