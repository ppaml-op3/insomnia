{-# LANGUAGE TemplateHaskell #-}
module Insomnia.SurfaceSyntax.SourcePos where

import Control.Applicative
import Control.Lens

import qualified Text.Parsec as P

data SourcePos = SourcePos {
  _sourcePosName :: String
  , _sourcePosLine :: !Int
  , _sourcePosColumn :: !Int
  }

data Positioned a = Positioned !SourcePos !a

instance Functor Positioned where
  fmap f (Positioned p x) = Positioned p $ f x

instance Show a => Show (Positioned a) where
  showsPrec _ (Positioned p x) = prettySourcePos p . showsPrec 10 x
  
prettySourcePos :: SourcePos -> ShowS
prettySourcePos (SourcePos f l c) =
  showString f . showString ":"
  . shows l . showString ":"
  . shows c . showString ":"

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
