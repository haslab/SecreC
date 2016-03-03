{-# LANGUAGE FlexibleContexts, DeriveDataTypeable, TupleSections, TypeFamilies #-}

module Language.SecreC.Parser.PreProcessor where

import Language.SecreC.Position
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Monad
import Language.SecreC.Pretty hiding (sepBy)
import Language.SecreC.Parser.Tokens
import Language.SecreC.Parser.Lexer

import Text.Parsec
import Text.Parsec.Pos

import Control.Applicative hiding ((<|>),optional,many)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ask,local,MonadReader(..))
import Control.Monad.Identity

import System.IO
import System.Console.CmdArgs 
import System.Console.CmdArgs.Explicit hiding (modes)
import System.Exit

import Safe

import qualified Data.Foldable as Foldable
import Data.Maybe
import Data.Typeable
import Data.Data
import Data.List.Split (splitOn)
import Data.Version (showVersion)

withPPArgs :: (MonadReader Options m) => (a -> m b) -> (PPArgs,a) -> m b
withPPArgs f (ppargs,x) = local (`mappend` ppOptions ppargs) (f x)

ppOptions :: PPArgs -> Options
ppOptions = mconcat . map (\(SecrecOpts x) -> x)

type PPArgs = [PPArg]

data PPArg
    = SecrecOpts Options
  deriving (Data,Show,Typeable)

type PPParserT u m a = ParsecT [Char] u m a
    
runPP :: (MonadIO m) => FilePath -> SecrecM m PPArgs
runPP file = do
    str <- liftIO $ readFile file
    mb <- runParserT parsePPArgs () file str 
    case mb of
        Left err -> throwError $ ParserError $ PreProcessorException $ show err
        Right x -> return x

anyLine :: MonadIO m => PPParserT u m String
anyLine = manyTill anyChar newline

parsePPArgs :: MonadIO m => PPParserT u m PPArgs
parsePPArgs = liftM catMaybes $ sepBy (liftM Just parsePPArg <|> (anyLine >> return Nothing)) newline

parsePPArg :: MonadIO m => PPParserT u m PPArg
parsePPArg = do
    char '#'
    string "OPTIONS_SECREC"
    spaces
    str <- anyLine
    o <- cmdArgsRunPP ppMode (words str)
    return $ SecrecOpts $ processOpts o

-- * CmdArgs options

cmdArgsRunPP :: MonadIO m => Mode (CmdArgs a) -> [String] -> PPParserT u m a
cmdArgsRunPP m xs = do
    args <- case process m xs of
            Left err -> unexpected $ show err
            Right x -> return x
    liftIO $ cmdArgsApply args

opts  :: Options
opts  = Opts { 
      inputs                = inputs defaultOptions &= args &= typ "FILE.sc"
    , outputs               = outputs defaultOptions &= typ "FILE1.sc:...:FILE2.sc" &= help "Output SecreC files"
    , paths                 = paths defaultOptions &= typ "DIR1:...:DIRn" &= help "Import paths for input SecreC program"
    , parser                = parser defaultOptions &= typ "parsec OR derp" &= help "backend Parser type"
    , implicitBuiltin       = implicitBuiltin defaultOptions &= name "builtin" &= help "Implicitly import the builtin module"
    
    -- Optimization
    , knowledgeInference    = knowledgeInference defaultOptions &= name "ki" &= help "Infer private data from public data" &= groupname "Optimization"
    
    -- Verification
    , typeCheck             = typeCheck defaultOptions &= name "tc" &= help "Typecheck the SecreC input" &= groupname "Verification"

    -- Debugging
    , debugLexer            = debugLexer defaultOptions &= name "debug-lexer" &= explicit &= help "Print lexer tokens to stderr" &= groupname "Debugging"
    , debugParser           = debugParser defaultOptions &= name "debug-parser" &= explicit &= help "Print parser result to stderr" &= groupname "Debugging"
    , debugTypechecker           = debugTypechecker defaultOptions &= name "debug-typechecker" &= explicit &= help "Print typechecker result to stderr" &= groupname "Debugging"
    
    -- Typechecker
    , implicitClassify   = implicitClassify defaultOptions &= name "implicit" &= help "Enables implicit classification of public data" &= groupname "Verification:Typechecker"
    , externalSMT   = externalSMT defaultOptions &= name "smt" &= help "Use an external SMT solver for index constraints" &= groupname "Verification:Typechecker"
    , constraintStackSize   = constraintStackSize defaultOptions &= name "k-stack-size" &= help "Sets the constraint stack size for the typechecker" &= groupname "Verification:Typechecker"
    , evalTimeOut           = evalTimeOut defaultOptions &= name "eval-timeout" &= explicit &= help "Timeout for evaluation expression in the typechecking phase" &= groupname "Verification:Typechecker"
    , failTypechecker = failTypechecker defaultOptions &= name "fail-tc" &= help "Typechecker should fail" &= groupname "Verification:Typechecker"
    }
    &= help "SecreC analyser"

ppMode  :: Mode (CmdArgs Options)
ppMode  = cmdArgsMode $ modes [opts &= auto]

processOpts :: Options -> Options
processOpts opts = opts
    { outputs = parsePaths $ outputs opts
    , paths = parsePaths $ paths opts
    , typeCheck = typeCheck opts || knowledgeInference opts
    }

parsePaths :: [FilePath] -> [FilePath]
parsePaths = concatMap (splitOn ":")


