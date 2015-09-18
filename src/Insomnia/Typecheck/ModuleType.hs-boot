module Insomnia.Typecheck.ModuleType where

import Insomnia.ModuleType (ModuleType, ModuleTypeNF)
import Insomnia.Typecheck.Env (TC)

checkModuleType :: ModuleType -> TC (ModuleType, ModuleTypeNF)
