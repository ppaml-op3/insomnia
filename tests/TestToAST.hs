module TestToAST where

import Test.Tasty (testGroup, TestTree)
import Test.Tasty.HUnit 

import Insomnia.SurfaceSyntax.ToAST (example1, example1_expected,
                                     example2, example2_expected,
                                     example3, example3_expected,
                                     example4, example4_expected)
  
infixParsingUnits :: TestTree
infixParsingUnits = testGroup "infix parsing "
  [ testCase "example1" $ example1 () @?= example1_expected
  , testCase "example2" $ example2 () @?= example2_expected
  , testCase "example3" $ example3 () @?= example3_expected
  , testCase "example4" $ example4 () @?= example4_expected
  ]

units :: TestTree
units = testGroup "ToAST" [
  infixParsingUnits
  ]
