{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Typecheck.Query where

import Data.Monoid ((<>))

import Insomnia.Common.ModuleKind
import Insomnia.ModuleType
import Insomnia.Query

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.LookupModuleSigPath (lookupModuleSigPath)

checkQueryExpr :: QueryExpr -> TC QueryExpr
checkQueryExpr qe@(GenSamplesQE mdlPath _params) = do
  mtnf <- lookupModuleSigPath mdlPath
  case mtnf of
   SigMTNF (SigV _ ModelMK) -> return qe
   SigMTNF (SigV _ ModuleMK) -> typeError ("query expression " <> formatErr qe
                                           <> " refers to a module, not a model")
   FunMTNF {} -> typeError ("query expression " <> formatErr qe
                            <> " refers to a functor, not a model")
