{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)

import Data.Monoid (Monoid(..), (<>))

import Data.Format (Format)
import qualified Data.Format as F

import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST
import Insomnia.Toplevel (Toplevel)
import Insomnia.Typecheck
import Insomnia.Pretty
import qualified Insomnia.IReturn as IReturn
import qualified Insomnia.Interp.Lam as Interp
import qualified Insomnia.Interp.ToLam as Interp


main :: IO ()
main = do
  act <- processArguments
  case act of
    Typecheck fp -> parseAndCheck fp
    HelpUsage -> printUsage


data Command =
  Typecheck !FilePath
  | HelpUsage

processArguments :: IO Command
processArguments = do
  args <- getArgs
  case args of
    [arg] | arg == "--help" -> return HelpUsage
          | otherwise -> return $ Typecheck arg
    _ -> return HelpUsage

printUsage :: IO ()
printUsage = putStrLn "Usage: insomnia [FILE | --help]"

parseAndCheck :: FilePath -> IO ()
parseAndCheck fp =
  startingFrom fp
  $ parsing
  ->->- desugaring
  ->->- checking
  ->->- demodularizing
  ->->- compilerDone

parsing :: Stage FilePath Toplevel
parsing = Stage {
  bannerStage = "Parsing"
  , performStage = \fp -> do
     result <- P.parseFile fp
     case result of
       Left err -> showErrorAndDie "alternate Parser" err
       Right surfaceAst -> return (ToAST.toAST surfaceAst)
  , formatStage = F.format . ppDefault 
  }

desugaring :: Stage Toplevel Toplevel
desugaring = Stage {
  bannerStage = "Desugaring"
  , performStage = \t ->
     let t' = IReturn.toplevel t
     in return t'
  , formatStage = F.format . ppDefault
  }

checking :: Stage Toplevel Toplevel
checking = Stage {
  bannerStage = "Typechecking"
  , performStage = \ast -> do
    let tc = runTC $ checkToplevel ast
    (elab, m) <- case tc of
      Left err -> showErrorAndDie "typechecking" err
      Right ans -> return ans
    putStrLn "Typechecked OK."
    putStrLn "Unification state:"
    F.putStrDoc (F.format $ ppDefault m)
    return elab
  , formatStage = F.format . ppDefault
  }

demodularizing :: Stage Toplevel Interp.Program
demodularizing = Stage {
  bannerStage = "Demodularizing"
  , performStage = \elab -> do
    let lam = Interp.translateToplevel elab
    return lam
  , formatStage = F.format . F.WrapShow
  }

data Stage a b = Stage { bannerStage :: F.Doc 
                       , performStage :: a -> IO b
                       , formatStage :: b -> F.Doc }

(->->-) :: Stage a b -> Stage b c -> Stage a c
stage1 ->->- stage2 = Stage {
  bannerStage = bannerStage stage1
  , performStage = \x -> do
    y <- performStage stage1 x
    F.putStrDoc (formatStage stage1 y <> F.newline)
    putStrLn "--------------------✂✄--------------------"
    F.putStrDoc (bannerStage stage2 <> F.newline)
    performStage stage2 y
  , formatStage = formatStage stage2
  }

infixr 6 ->->-

compilerDone :: Stage a ()
compilerDone = Stage { bannerStage = mempty
                     , performStage = const (return ())
                     , formatStage = mempty
                     }

startingFrom :: a -> Stage a () -> IO ()
startingFrom a stages = do
  F.putStrDoc (bannerStage stages <> F.newline)
  performStage stages a

showErrorAndDie :: (Format err) => String -> err -> IO a
showErrorAndDie phase msg = do
  putStrLn $ "Encountered error while " ++ phase
  F.putStrDoc (F.format $ msg)
  putStrLn ""
  exitFailure
