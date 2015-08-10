module Insomnia.Typecheck.ObservationClause where

import Insomnia.Identifier (Path)
import Insomnia.ModuleType (Signature)
import Insomnia.Module (ObservationClause)

import Insomnia.Typecheck.Env (TC)

checkObservationClauses :: Path -> Signature -> [ObservationClause] -> TC [ObservationClause]
