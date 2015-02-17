-- | Routines for typechecking instantiation and generalization in
-- Insomnia.
--
-- The algorithm is inspired by "Practical Type Inference for
-- arbitrary-rank types" Peyton Jones, Vytiniotis, Weirch and Shields,
-- 2007. (2011).
module Insomnia.Typecheck.Polymorphism where

import Insomnia.Expr

import Insomnia.Typecheck.Env


