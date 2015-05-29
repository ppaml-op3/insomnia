{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.SaveFinalProductStage where

import Control.Monad.Reader (asks, lift)
import Data.Monoid (Monoid(..), (<>))

import qualified System.IO as IO

import qualified Data.Format as F


import Insomnia.Main.Config
import Insomnia.Main.Stage

saveFinalProductStage :: (F.Format a) => F.Doc -> Stage a a
saveFinalProductStage thing =
  maybeStage f (saveResultStage thing)
  where f = asks ismCfgFinalProductOut

saveResultStage :: (F.Format a) => F.Doc -> Stage (IO.Handle, a) a
saveResultStage thing =
  Stage {
    bannerStage = "Saving " <> thing
    , performStage = \(h, inp) -> do
      lift $ F.hPutStrLnDoc h (F.format inp)
      return inp
    , formatStage = mempty
    }
