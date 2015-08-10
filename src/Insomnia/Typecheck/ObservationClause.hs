{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Typecheck.ObservationClause where

import Data.Monoid ((<>))
import Data.Traversable(Traversable(..))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Path(..))
import Insomnia.ModuleType (Signature(..), ModuleTypeNF(..), SigV(..))
import Insomnia.Common.ModuleKind
import Insomnia.Module (ObservationClause(..))

import Insomnia.Typecheck.Env

import Insomnia.Typecheck.Module (inferModuleExpr)
import Insomnia.Typecheck.LookupModuleSigPath (projectModuleField)
import Insomnia.Typecheck.MayAscribe (mayAscribeNF)

-- checkObservationClause pmod mdlsig obss
-- checks that each "where f is M" observation clause is well-formed with
-- respect to (model) signature mdlsig.  The path pmod is just for error messages.
--
-- The observation clauses each pick a new i.i.d. sample from the submodel f and immediately
-- observe its values as "M" which as a result gives 'observe M where f is M' as the posterior.
-- The signature of the overall observe model expression is the same as the signature of 'M'.
checkObservationClauses :: Path -> Signature -> [ObservationClause] -> TC [ObservationClause]
checkObservationClauses pmod mdlsig =
  traverse (checkObservationClause pmod mdlsig)

checkObservationClause :: Path -> Signature -> ObservationClause -> TC ObservationClause
checkObservationClause pmod mdlsig (ObservationClause f m) = do
  (m', obsSigNF) <- inferModuleExpr (IdP $ U.s2n "<observation>") m
                    <??@ ("while checking observation of field " <> formatErr f
                          <> " of " <> formatErr pmod)
  kernNF <- projectModuleField pmod f mdlsig
            <??@ ("while projecting the field " <> formatErr f <> " for observation of "
                  <> formatErr pmod)
  case (kernNF, obsSigNF) of
    (SigMTNF (SigV k ModelMK), SigMTNF (SigV o ModuleMK)) -> do
      -- Check that k ≤ o ∧ o ≤ k
      let k' = SigMTNF (SigV k ModuleMK)
          o' = SigMTNF (SigV o ModuleMK)
      _ <- mayAscribeNF k' o'
           <??@ ("while checking that the observation kernel "
                 <> formatErr f
                 <> " has all the fields of the given observation module")
      _ <- mayAscribeNF o' k'
           <??@ ("while checking that the observation module  has all the fields "
                 <> "of the given observation kernel " <> formatErr f)
      return ()
    (SigMTNF (SigV _ ModuleMK), _) ->
      typeError ("expected field " <> formatErr f <> " to be a submodel, but it's a submodule "
                 <> "in observation " <> formatErr pmod)
    (FunMTNF {}, _) -> 
      typeError ("expected field " <> formatErr f <> " to be a submodel, but it's a functor "
                 <> "in observation " <> formatErr pmod)
    (_, SigMTNF (SigV _ ModelMK)) ->
      typeError ("expected the observation of field " <> formatErr f <> " to be a module, "
                 <> "but it's a model, in observation " <> formatErr pmod)
    (_, FunMTNF {}) ->
      typeError ("expected the observation of field " <> formatErr f <> " to be a module, "
                 <> "but it's a functor, in observation " <> formatErr pmod)
  return (ObservationClause f m')
