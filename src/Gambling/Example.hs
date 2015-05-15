{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
module Gambling.Example where

import Unbound.Generics.LocallyNameless

import Gambling.Racket
import Gambling.Emit (Emit(..), emitIt)

var :: String -> (Var, Expr)
var s = let x = s2n s
        in (x, Var x)

lam :: [Var] -> Body -> Expr
lam vs = Lam . bind vs

body :: [InternalDefn] -> Expr -> Body
body ds = Body . bind (rec ds) 

class DefinitionInContext ctx d where
  injDefn :: d -> ctx

instance DefinitionInContext InternalDefn Definition where
  injDefn = DefnID

instance DefinitionInContext ModuleBinding Definition where
  injDefn = DefnMB

instance DefinitionInContext InternalDefn Expr where
  injDefn = ExprID . embed

instance DefinitionInContext ModuleBinding Expr where
  injDefn = ExprMB . embed


define :: DefinitionInContext ctx Definition => Var -> Expr -> ctx
define x = injDefn . Define . rebind x . embed

effect :: DefinitionInContext ctx Expr => Expr -> ctx
effect = injDefn

ex1 :: Expr
ex1 = let
  (vx, x) = var "x"
  (vy, y) = var "y"
  in lam [vx]
     $ body
     [
       define vy $ App [x, x]
     , effect $ App [y,  x]
     ]
     $ App [y, App [y, x], y]
  

moduleBody :: [Var] -> [ModuleBinding] -> ModuleDefnCtx
moduleBody ps defs = ModuleDefnCtx $ bind (rec defs) $ Provides ps

require :: ModulePath -> [Var] -> ModuleBinding
require modPath = RequireMB . Requires (embed modPath) 

ex2 :: Module
ex2 = Module (s2n "ex2") "racket"
      $ moduleBody []
      [
        require "A" [s2n "x"]
      , effect ex1
      ]
