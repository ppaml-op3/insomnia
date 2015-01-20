{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FunctionalDependencies #-}
module Insomnia.SurfaceSyntax.FixityParser
       (Assoc(..)
       , Fixity(..)
       , FixityParseable(..)
       , runFixityParser
       , fixityParser
       ) where

import Control.Applicative ((<*))
import qualified Data.Map as M
import Data.Monoid ((<>))

import Text.Parsec

import Text.Parsec.Expr (Assoc(..), Operator(..),
                         OperatorTable,
                         buildExpressionParser)

class FixityParseable tok op m t | t -> op, tok -> op where
  term :: Stream s m tok => ParsecT s u m t
  juxt :: Stream s m tok => ParsecT s u m (t -> t -> t)
  infx :: Stream s m tok => op -> ParsecT s u m (t -> t -> t)

data Fixity = Fixity !Assoc !Rational

instance Show Fixity where
  showsPrec _ (Fixity assoc prec) =
    showString "Fixity " . showsAssoc assoc . showString " " . shows prec

showsAssoc :: Assoc -> ShowS
showsAssoc AssocLeft = showString "AssocLeft"
showsAssoc AssocRight = showString "AssocRight"
showsAssoc AssocNone = showString "AssocNone"

runFixityParser :: (FixityParseable tok op m t, Monad m, Show tok)
                   => ParsecT [tok] () m t
                   -> [tok]
                   -> SourceName
                   -> m (Either ParseError t)
runFixityParser p toks fileName = runParserT (p <* eof) () fileName toks

fixityParser :: (FixityParseable tok op m t, Stream s m tok)
                => M.Map op Fixity
                -> ParsecT s u m t
fixityParser operators =
  buildExpressionParser ([Infix juxt AssocLeft]
                         : makeOperatorTable operators) term

type PrecedenceMap a = M.Map Rational [a]

makeOperatorTable :: (FixityParseable tok op m t, Stream s m tok)
                     => M.Map op Fixity
                     -> OperatorTable s u m t
makeOperatorTable =
  map snd
  . M.toDescList
  . fmap (map makeInfxParser)
  . toPrecedenceMap
  where
    makeInfxParser :: (FixityParseable tok op m t,
                       Stream s m tok)
                      => (op, Assoc)
                      -> Operator s u m t
    makeInfxParser (op, assoc) = Infix (infx op) assoc
    toPrecedenceMap :: M.Map op Fixity
                       -> PrecedenceMap (op, Assoc)
    toPrecedenceMap = M.foldrWithKey intoPrecedenceMap M.empty
    intoPrecedenceMap :: op -> Fixity -> PrecedenceMap (op, Assoc)
                         -> PrecedenceMap (op, Assoc)
    intoPrecedenceMap op (Fixity assoc prec) =
      M.insertWith (<>) prec [(op, assoc)] 
