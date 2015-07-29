-- | Typecheck functor application
--
-- To check F (P1, ..., Pk), we check:
-- 1. that the functor F has a functor signature (X1:S1, .... Xm:Sm) → S'
-- 2. that k = m
-- 3. that each P1, ... Pk has signature T1,... Tk
-- 4. ⊢ Ti <: Si[P1...P(i-1)/X1...X(i-1)] for all 0≤i≤k
-- 5. Return the signature S'[P1...Pk/X1...Xk]
--
-- To do steps 4 and 5, we substitute each Pi for Xi into the remainder of the Si+1...Sm and S' as soon
-- as each step is complete.
{-# LANGUAGE ViewPatterns, OverloadedStrings, FlexibleContexts #-}
module Insomnia.Typecheck.FunctorApplication (checkFunctorApplication) where

import Control.Monad (unless)
import Data.Monoid ((<>), Sum(..))
import Data.Traversable (forM)

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Telescope
import Insomnia.Identifier

import Insomnia.ModuleType

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.LookupModuleSigPath (lookupModuleSigPath)
import Insomnia.Typecheck.MayAscribe (mayAscribeNF)

checkFunctorApplication :: Path -> [Path] -> TC ModuleTypeNF
checkFunctorApplication pfun pargs = do
  funNF <- lookupModuleSigPath pfun
  argNFs <- forM pargs $ \parg -> do
    nf <- lookupModuleSigPath parg
    return (parg, nf)
  case funNF of
   SigMTNF {} -> typeError ("functor application of " <> formatErr pfun <> ", but it isn't a functor")
   FunMTNF bnd -> U.lunbind bnd $ \(teleParams, modRslt_) -> do
     let (Sum m) = foldMapTelescope (const (Sum 1)) teleParams
         k = length pargs
     unless (k == m) $
       typeError ("functor " <> formatErr pfun
                  <> " takes " <> formatErr m
                  <> " arguments, but given " <> formatErr k)
     checkFunctorArgumentsTelescope teleParams argNFs modRslt_ $ \modRslt ->
       return modRslt

checkFunctorArgumentsTelescope :: U.Subst Path s
                                  => Telescope (FunctorArgument ModuleTypeNF)
                                  -> [(Path, ModuleTypeNF)]
                                  -> s
                                  -> (s -> TC r)
                                  -> TC r
checkFunctorArgumentsTelescope tele_ pargNFs_ rest0 kont =
  case (tele_, pargNFs_) of
   (NilT, []) -> kont rest0
   (ConsT (U.unrebind -> (funParam , tele)), (parg, argNF):pargNFs) -> do
     checkFunctorArgument funParam parg argNF (rest0, tele) $ \(rest1, tele') -> do
       checkFunctorArgumentsTelescope tele' pargNFs rest1 $ \rest2 ->
         kont rest2
   (_, _) -> fail ("internal error: checkFunctorArgumentsTelescope expected to be called "
                   ++ " with telescope and list of equal lengths")
                                      
checkFunctorArgument :: U.Subst Path s
                        => FunctorArgument ModuleTypeNF
                        -> Path
                        -> ModuleTypeNF
                        -> s
                        -> (s -> TC r)
                        -> TC r
checkFunctorArgument (FunctorArgument paramIdent embNF) parg argNF rest_ kont = do
  let -- paramMK = U.unembed embMK
      paramNF = U.unembed embNF
  _sigEnv <- mayAscribeNF argNF paramNF
    <??@ (" while checking argument " <> formatErr parg
          <> " against parameter " <> formatErr paramIdent)
  let rest = U.subst paramIdent parg rest_
  kont rest
  
     
