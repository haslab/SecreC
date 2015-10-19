module Language.SecreC.Parser (
    parseFile, parseFileIO
    , module Language.SecreC.Parser.Lexer
    , module Language.SecreC.Parser.Tokens
    ) where

import qualified Language.SecreC.Parser.Parsec as Parsec
import qualified Language.SecreC.Parser.Derp as Derp
import Language.SecreC.Parser.Lexer
import Language.SecreC.Parser.Tokens
import Language.SecreC.Monad
import Language.SecreC.Position
import Language.SecreC.Syntax

import Control.Monad.Reader

parseFileIO :: Options -> String -> IO (Module Position)
parseFileIO opts fn = case parser opts of
    Parsec -> Parsec.parseFileIO opts fn
    Derp -> Derp.parseFileIO opts fn

parseFile :: String -> SecrecM (Module Position)
parseFile s = do
    opts <- ask
    case parser opts of
        Parsec -> Parsec.parseFile s
        Derp -> Derp.parseFile s
    