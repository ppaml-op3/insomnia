module Insomnia.ToF.Expr where

import Insomnia.ToF.Env (ToF)

import Insomnia.TypeDefn (ValueConstructor)
import Insomnia.Expr (Expr)

import qualified FOmega.Syntax as F

expr :: ToF m => Expr -> m F.Term

valueConstructor :: ToF m
                    => ValueConstructor
                    -> m (F.Term, F.Field, F.Term)

