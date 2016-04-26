module Language.SecreC.Parser (
    parseFile, parseFileIO
    , module Language.SecreC.Parser.Lexer
    , module Language.SecreC.Parser.Tokens
    ) where

import qualified Language.SecreC.Parser.Parsec as Parsec
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Parser.Lexer
import Language.SecreC.Parser.Tokens
import Language.SecreC.Monad
import Language.SecreC.Position
import Language.SecreC.Syntax

import Control.Monad.Reader
import Control.Monad.Catch

parseFileIO :: Options -> String -> IO (PPArgs,Module Identifier Position)
parseFileIO opts fn = do
    pps <- runSecrecM opts $ runPP fn
    ast <- Parsec.parseFileIO opts fn
    return (pps,ast)

parseFile :: (MonadIO m,MonadCatch m) => String -> SecrecM m (PPArgs,Module Identifier Position)
parseFile s = do
    opts <- ask
    pps <- runPP s
    ast <- Parsec.parseFile s
    return (pps,ast)
    