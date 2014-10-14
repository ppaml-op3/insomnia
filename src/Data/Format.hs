{-# LANGUAGE OverloadedStrings, DefaultSignatures #-}
module Data.Format
       (
         Doc
       , Format(..)
       , docToText
       , putStrDoc
       , WrapShow(..)
       ) where

import Data.Monoid (Monoid(..), (<>))

import Data.String (IsString(..))
import qualified Data.Text as TStrict
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import qualified Data.Text.Lazy.Builder as TB
import qualified Unbound.Generics.LocallyNameless as U
  
newtype Doc = Doc { unDoc :: TB.Builder }

instance Monoid Doc where
  mempty = Doc mempty
  mappend d1 d2 = Doc $ mappend (unDoc d1) (unDoc d2)
  mconcat ds = Doc $ mconcat (map unDoc ds)

instance IsString Doc where
  fromString = Doc . fromString

class Format a where
  format :: a -> Doc
  default format :: Show a => a -> Doc
  format = format . WrapShow

  formatList :: [a] -> Doc
  formatList = formatList__ format

formatList__ :: (a -> Doc) -> [a] -> Doc
formatList__ _f [] = Doc "[]"
formatList__ f (x:xs) = Doc (TB.singleton '['
                             <> unDoc (f x)
                             <> go xs)
  where go [] = TB.singleton ']'
        go (y:ys) = TB.singleton ',' <> unDoc (f y) <> go ys
  
-- | Format @a@ by calling its 'show' method
newtype WrapShow a = WrapShow { unwrapShow :: a }

instance Show a => Format (WrapShow a) where
  format = Doc . TB.fromString . show . unwrapShow
  formatList = Doc . TB.fromString . flip showList [] . map unwrapShow

instance Format ()
instance Format Bool
instance Format Int
instance Format Integer
instance Format Double
instance Format Char where
  format = Doc . TB.singleton
  formatList = Doc . TB.fromString
instance Format TStrict.Text where
  format = Doc . TB.fromText
instance Format T.Text where
  format = Doc . TB.fromLazyText
instance Format a => Format [a] where
  format = formatList

instance Format Doc where
  format = id

instance Format (U.Name a)

-- | convert the given 'Doc' to a 'T.Text'
docToText :: Doc -> T.Text
docToText = TB.toLazyText . unDoc

-- | display the given Doc on stdOut
putStrDoc :: Doc -> IO ()
putStrDoc = T.putStr . docToText
