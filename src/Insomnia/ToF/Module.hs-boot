module Insomnia.ToF.Module where

import Insomnia.Module (ModuleExpr)
import Insomnia.ModuleType (ModuleType)

import qualified FOmega.SemanticSig as F
import qualified FOmega.Syntax as F

import Insomnia.ToF.Env (ToF)

sealing :: ToF m => ModuleExpr -> ModuleType -> m (F.AbstractSig, F.Term)