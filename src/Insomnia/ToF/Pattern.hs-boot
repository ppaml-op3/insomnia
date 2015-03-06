module Insomnia.ToF.Pattern where

import Insomnia.ToF.Env (ToF)

import qualified Unbound.Generics.LocallyNameless as U

import qualified FOmega.Syntax as F

import Insomnia.Expr (Var, Clause)

patternTranslation :: ToF m
                      => Var
                      -> [Clause]
                      -> F.Type
                      -> m (U.Bind F.Var F.Term)
