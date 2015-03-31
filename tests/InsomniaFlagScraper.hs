module InsomniaFlagScraper where

import Control.Applicative
import Data.Text.Lazy as T
import Data.Text.Lazy.IO as T
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Error (ParseError)
import Text.Parsec.Prim hiding ((<|>))
import Text.Parsec.Text.Lazy (Parser)
import qualified System.IO as IO

newtype ScrapedFlags = ScrapedFlags {
  getEvalScrapedFlag :: Bool
  }
                     deriving Show

scrapeFlags :: FilePath -> IO (Maybe ScrapedFlags)
scrapeFlags fp = do
  e <- parseFlags fp
  case e of
   Left err -> fail (show err)
   Right ok -> return ok

parseFlags :: FilePath -> IO (Either ParseError (Maybe ScrapedFlags))
parseFlags fp =
  IO.withFile fp IO.ReadMode $ \fh -> do
    txt <- T.hGetContents fh
    return $! parse findFlags fp txt

findFlags :: Parser (Maybe ScrapedFlags)
findFlags =
  (Just <$> scrapedFlags)
  <|> (skipMany (noneOf "\r\n") -- skip junk until next newline
       *> ((newline *> findFlags) <|> eofNothing)) -- and try again or Nothing if eof
  where
    eofNothing = Nothing <$ eof

scrapedFlags :: Parser ScrapedFlags
scrapedFlags =
  ScrapedFlags <$ (try beginFlagsLine)
  <*> evalFlagLine
  

beginFlagsLine :: Parser ()
beginFlagsLine =
  keywordLine "insomnia test flags" (pure ())

evalFlagLine :: Parser Bool
evalFlagLine = 
  keywordLine "eval" boolean


boolean :: Parser Bool
boolean =
  (True <$ string "True")
  <|> (False <$ string "False")

keywordLine :: String -> Parser a -> Parser a
keywordLine kw p =
  commentLine (reserved kw *> colon *> lexeme p)

colon :: Parser Char
colon = lexeme (char ':')

whiteSpace :: Parser ()
whiteSpace = skipMany (oneOf "\t ")

reserved :: String -> Parser ()
reserved kw = () <$ lexeme (string kw)

commentLine :: Parser a -> Parser a
commentLine p =
  (string "--" *> whiteSpace) *> p <* (whiteSpace <* endOfLine)

lexeme :: Parser a -> Parser a
lexeme p = p <* whiteSpace
