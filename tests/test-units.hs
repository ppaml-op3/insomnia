module Main where

import Test.Tasty (defaultMain, testGroup)

import TestToAST (units)

main = defaultMain $ testGroup "Unit tests " [
  TestToAST.units
  ]
