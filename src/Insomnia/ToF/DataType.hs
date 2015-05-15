module Insomnia.ToF.DataType where

import Control.Lens
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Monoid (Endo(..))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.ToF.Env
import Insomnia.ToF.Summary
import Insomnia.ToF.Type


datatypeDefinition :: ToF m
                      => Field
                      -> TyConName
                      -> DataDefn
                      -> (ModSummary -> m ans)
                      -> m ans
datatypeDefinition f selfTc bnd kont =
  U.lunbind bnd $ \(tvks, constrs) ->
  withFreshName "Δ" $ \dataTyModV ->
  withFreshName "δ" $ \dtv -> do
    (dataSem, conEnv, thisOne) <-
      withTyVars tvks $ \tvks' -> do
        let kdoms = map snd tvks'
            k = kdoms `F.kArrs` F.KType
        (conVs, constructorFields) <-
          -- extend env for constructos so they can be recursive
          local (tyConEnv %~ M.insert selfTc (F.TypeSem (F.TV dtv) k)) $
          liftM unzip $ forM constrs $ \(ConstructorDef cname tDoms) -> do
            tDoms' <- mapM (liftM fst . type') tDoms
            let fcon = F.FCon (U.name2String cname)
            return ((cname, (dataTyModV, fcon)), (fcon, tDoms'))
        let
          dtsem = let tveks = map (\(tv,k) -> (tv, U.embed k)) tvks'
                  in F.DataTypeSem (U.bind tveks constructorFields)
          dataSem = F.DataSem dtv dtsem k
          conEnv  = M.fromList conVs
          abstr = [(dtv, U.embed k)]
        dataTyModM <- buildDatatypeModule dtv dtsem k
        let
          unpackHole = Endo (F.Unpack . U.bind (dtv, dataTyModV, U.embed dataTyModM))
          absSig = (abstr, [(F.FUser f, dataSem)])
          fieldData = [(F.FUser f, F.V dataTyModV)]
          thisOne = (absSig, fieldData, unpackHole)
        return (dataSem, conEnv, thisOne)
    local (tyConEnv %~ M.insert selfTc dataSem)
      . local (valConEnv %~ M.union conEnv)
      $ kont thisOne

-- | Given: δ, (λαs:κs. {fi : τ1i,⋯,τmi}), κ(= κs→⋆) where δ may occur in τs
-- construct
--   dataIn = { fi = Λαs:κs. λ x1:τ1i . ⋯ λ xm:τmi . roll σ , inj fi Σ (tuple x1 … xm) as ε.ε αs }
--   dataOut = Λ γ:κ→⋆ . λ x : γ σ . unroll σ, x as ε . γ ε
-- and return pack σ , { dataOut = dataOut , dataIn = dataIn[σ/δ] } as ∃ δ . ⋯
--                                                    ^^^^^^^^^^^ Note1
-- where σ = μδ:κ . λαs:κs . Σ
--   and Σ = { fi : τ1i× ⋯ × τmi }
--
-- Note1: if the τij's contain references to δ (ie a recursive datatype) we need to plug in the
-- datatype in those places in the implementation lambdas.
buildDatatypeModule :: ToF m
                       => F.TyVar
                       -> F.DataTypeSem
                       -> F.Kind
                       -> m F.Term
buildDatatypeModule dtv dtsem@(F.DataTypeSem bnd) k = do
  fixPtTy <- datatypeFixpointType dtv k dtsem
  injections_ <- U.lunbind bnd $ \(tveks, constructorFields) -> do
    let sumTy = datatypeSumType constructorFields
    rollCtx <- withFreshName "ε" $ \eps ->
      let b = F.TV eps `F.tApps` (map (F.TV . fst) tveks)
      in return $ U.bind eps b
    injectors <- forM constructorFields $ \(f, tArgs) ->
        withFreshNames (map (const "x") tArgs) $ \xs ->
          let i = F.Inj f (F.tuple (map F.V xs)) sumTy
              r = F.Roll fixPtTy i rollCtx
              l = let xts = zip xs tArgs
                  in F.lams xts r
          in return (f, F.pLams' tveks l)
    return $ F.Record injectors
  let injections = U.subst dtv fixPtTy injections_
  projection <- withFreshName "γ" $ \gamma ->
    U.lunbind bnd $ \(tveks, constructorFields) ->
    withFreshName "x" $ \x -> do
      unrollCtx <- withFreshName "ε" $ \eps ->
        return $ U.bind eps (F.TV gamma `F.TApp` F.TV eps)
      let u = F.Unroll fixPtTy (F.V x) unrollCtx
          xty = F.TV gamma `F.TApp` fixPtTy
          l = F.Lam $ U.bind (x, U.embed xty) $ u
          p = let gk = k `F.KArr` F.KType
               in F.PLam $ U.bind (gamma, U.embed gk) l
      return p
  let
    r = F.Record [(F.FDataIn, injections)
                 , (F.FDataOut, projection)
                 ]
    dataSem = F.DataSem dtv dtsem k
  semTy <- F.embedSemanticSig dataSem
  let
    -- δ.{dataIn : ... ; dataOut : ... }
    d = U.bind (dtv, U.embed k) semTy
  return $ F.Pack fixPtTy r d
  where
    -- given αs:κs, return ε.ε αs

-- given δ:κ⊢λαs:κs.{fi : τ1i,⋯,τmi }
-- construct σ = μδ:κ.λαs:κs. Σ
--     where Σ = { fi : τ11×⋯×τ1i }
-- returns σ
datatypeFixpointType :: U.LFresh m => F.TyVar -> F.Kind -> F.DataTypeSem -> m F.Type
datatypeFixpointType dtv k (F.DataTypeSem bnd) =
  U.lunbind bnd $ \(tveks, constrs) ->
    let sumTy = datatypeSumType constrs
        lams = F.tLams' tveks sumTy
    in return $ F.TFix $ U.bind (dtv, U.embed k) $ lams

datatypeSumType :: [(F.Field, [F.Type])] -> F.Type
datatypeSumType =
  F.TSum . map (\(f, argTys) ->
                 let p = F.tupleT argTys
                 in (f, p))
                   
