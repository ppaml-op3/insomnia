module Insomnia.Typecheck.Module where

import Insomnia.Identifier (Path)
import Insomnia.ModuleType (ModuleTypeNF)
import Insomnia.Module (ModuleExpr)

import Insomnia.Typecheck.Env (TC)

inferModuleExpr :: Path -> ModuleExpr -> TC (ModuleExpr, ModuleTypeNF)