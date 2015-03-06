module Insomnia.ToF.Expr where

import Insomnia.ToF.Env (ToF)

import Insomnia.Expr (Expr)

import qualified FOmega.Syntax as F

expr :: ToF m => Expr -> m F.Term
