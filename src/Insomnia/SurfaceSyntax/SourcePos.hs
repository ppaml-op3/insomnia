{-# LANGUAGE TemplateHaskell #-}
module Insomnia.SurfaceSyntax.SourcePos where

import Control.Applicative
import Control.Lens

import qualified Text.Parsec as P

data SourcePos = SourcePos {
  _sourcePosName :: String
  , _sourcePosLine :: !Int
  , _sourcePosColumn :: !Int
  } deriving (Show)

data Positioned a = Positioned !SourcePos !a
                  deriving (Show)

makeLenses ''SourcePos

positioned :: Lens (Positioned a) (Positioned b) a b
positioned = lens getter setter
  where
    getter :: Positioned a -> a
    getter (Positioned _pos x) = x
    setter :: Positioned a -> b -> Positioned b
    setter (Positioned pos _x) y = Positioned pos y

positionedSourcePos :: Lens' (Positioned a) SourcePos
positionedSourcePos = lens getter setter
  where
    getter (Positioned pos _x) = pos
    setter (Positioned _pos x) pos' = (Positioned pos' x)


parsePositioned :: Monad m => P.ParsecT s u m a -> P.ParsecT s u m (Positioned a)
parsePositioned p =
  Positioned <$> getPosition <*> p
  where
    getPosition = fmap pos2pos P.getPosition
    pos2pos :: P.SourcePos -> SourcePos
    pos2pos posn =
      SourcePos (P.sourceName posn) (P.sourceLine posn) (P.sourceColumn posn)
