module Insomnia.ToF.Query where

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Query

import Insomnia.ToF.Env
import Insomnia.ToF.Module (modulePath)

import qualified FOmega.Syntax as F

queryExpr :: ToF m => QueryExpr -> m F.Command
queryExpr qe_ =
  case qe_ of
   GenSamplesQE p params -> do
     (_absSig, m) <- modulePath p
     let
       vl = U.s2n "l"
       l = F.V vl
       queryCmd = F.EffectC (F.SamplePC params) m
       printCmd = F.EffectC F.PrintPC l
       c = F.BindC $ U.bind (vl, U.embed queryCmd) printCmd
     return c
