{-# LANGUAGE OverloadedStrings, RankNTypes #-}
module Insomnia.Main.Stage (Stage(..)
                           , (->->-)
                           , simpleStage
                           , conditionalStage
                           , maybeStage
                           , startingFrom
                           , compilerDone) where

import Data.Monoid

import qualified Pipes

import qualified Data.Format as F

import Insomnia.Main.Monad

data Stage a b = Stage { bannerStage :: F.Doc 
                       , performStage :: Pipes.Pipe a b InsomniaMain ()
                       , formatStage :: b -> F.Doc }

simpleStage :: F.Format b => String -> (a -> b) -> Stage a b
simpleStage name f =
  Stage { bannerStage = F.format name
        , performStage = Pipes.await >>= Pipes.yield . f
        , formatStage = F.format
        }

(->->-) :: Stage a b -> Stage b c -> Stage a c
stage1 ->->- stage2 = Stage {
  bannerStage = bannerStage stage1
  , performStage =
    performStage stage1
    Pipes.>-> do
      y <- Pipes.await
      Pipes.lift $ do
        putDebugDoc (formatStage stage1 y <> F.newline)
        putDebugStrLn "--------------------✂✄--------------------"
        putDebugDoc (bannerStage stage2 <> F.newline)
      Pipes.yield y
    Pipes.>-> performStage stage2
  , formatStage = formatStage stage2
  }

infixr 6 ->->-

compilerDone :: Stage a b
compilerDone = Stage { bannerStage = mempty
                     , performStage = Pipes.await >> return ()
                     , formatStage = mempty
                     }

maybeStage :: InsomniaMain (Maybe c) -> (Stage (c,a) a) -> Stage a a
maybeStage shouldRun stage =
  Stage { bannerStage = bannerStage stage
        , performStage = do
          inp <- Pipes.await
          m <- Pipes.lift $ shouldRun
          case m of
           Nothing -> do
             Pipes.lift $ putErrorDoc ("SKIPPED " <> bannerStage stage)
             Pipes.yield inp
           Just c ->
             Pipes.yield (c, inp) Pipes.>-> performStage stage
        , formatStage = formatStage stage
        }

conditionalStage :: InsomniaMain Bool -> Stage a a -> Stage a a
conditionalStage shouldRun stage =
  Stage { bannerStage = bannerStage stage
        , performStage = do
          inp <- Pipes.await
          b <- Pipes.lift $ shouldRun
          case b of
           True -> Pipes.yield inp Pipes.>-> performStage stage
           False -> do
             Pipes.lift $ putErrorDoc ("SKIPPED " <> bannerStage stage)
             Pipes.yield inp
        , formatStage = formatStage stage
        }


startingFrom :: a -> (forall b . Stage a b) -> Pipes.Effect InsomniaMain ()
startingFrom a stages = do
  Pipes.lift $ putDebugDoc (bannerStage stages <> F.newline)
  return a Pipes.>~ performStage stages

