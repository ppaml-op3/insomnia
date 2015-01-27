{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Typecheck.Toplevel (checkToplevel) where

import Data.Monoid ((<>))
import Control.Applicative ((<$>))

import Insomnia.Identifier
import Insomnia.Toplevel

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.ModuleType (checkModuleType)
import Insomnia.Typecheck.ExtendModuleCtx (extendModuleCtxNF)
import Insomnia.Typecheck.Module (inferModuleExpr)

checkToplevel :: Toplevel -> TC Toplevel
checkToplevel (Toplevel items_) =
  Toplevel <$> go items_ return
  where
    go [] kont = kont []
    go (item:items) kont =
      checkToplevelItem item $ \item' ->
      go items $ \items' ->
      kont (item':items')

checkToplevelItem :: ToplevelItem -> (ToplevelItem -> TC a) -> TC a
checkToplevelItem item kont =
  case item of
    ToplevelModule moduleIdent me ->
      let pmod = IdP moduleIdent
      in (inferModuleExpr pmod me
          .??@ ("while infering the module type of " <> formatErr pmod))
         $ \me' sigNF ->
            (extendModuleCtxNF pmod sigNF
             .??@ ("while extending the context with module type of " <> formatErr pmod))
            $ kont $ ToplevelModule moduleIdent me'
          
    ToplevelModuleType modTypeIdent modType -> do
      (modType', sigV) <- checkModuleType modType
                          <??@ ("while checking module type "
                                <> formatErr modTypeIdent)
      extendModuleTypeCtx modTypeIdent sigV
        $ kont $ ToplevelModuleType modTypeIdent modType'
        

