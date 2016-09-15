{-# LANGUAGE DeriveGeneric, FlexibleInstances, TypeSynonymInstances, FlexibleContexts, DeriveDataTypeable, TupleSections, TypeFamilies #-}

module Language.SecreC.Parser.PreProcessor where

import Language.SecreC.Position
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Monad
import Language.SecreC.Pretty hiding (sepBy)
import qualified Language.SecreC.Pretty as PP
import Language.SecreC.Parser.Tokens
import Language.SecreC.Parser.Lexer

import Text.PrettyPrint ((<+>),(<>),text)
import qualified Text.PrettyPrint as PP
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
import Data.Binary
import Data.Hashable
import Data.Typeable
import Data.Data
import Data.List.Split (splitOn)
import Data.Version (showVersion)

import GHC.Generics (Generic)

withPPArgs :: (MonadReader Options m) => (a -> m b) -> (PPArgs,a) -> m b
withPPArgs f (ppargs,x) = local (`mappend` ppOptions ppargs) (f x)

ppOptions :: PPArgs -> Options
ppOptions = mconcat . map (\(SecrecOpts x) -> x)

type PPArgs = [PPArg]

data PPArg
    = SecrecOpts Options
  deriving (Data,Show,Typeable,Generic)

instance Binary PPArg
instance Hashable PPArg

instance PP PPArgs where
    pp args = PP.vcat $ map pp args

instance PP PPArg where
    pp (SecrecOpts opts) = text "#OPTIONS_SECREC" <+> pp opts

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

instance PP Options where
    pp opts = PP.sepBy PP.space (map pp $ inputs opts)
          <+> text "--outputs=" <> PP.sepBy (PP.char ':') (map pp $ outputs opts)
          <+> text "--paths=" <> PP.sepBy (PP.char ':') (map pp $ paths opts)
          <+> text "--verify=" <> pp (verify opts)
          <+> text "--simplify=" <> pp (simplify opts)
          <+> text "--printoutput=" <> pp (printOutput opts)
          <+> text "--typecheck=" <> pp (typeCheck opts)
          <+> text "--debuglexer=" <> pp (debugLexer opts)
          <+> text "--debugparser=" <> pp (debugParser opts)
          <+> text "--debugtypechecker=" <> pp (debugTypechecker opts)
          <+> text "--debugtransformation=" <> pp (debugTransformation opts)
          <+> text "--debugverify=" <> pp (debugVerification opts)
          <+> text "--implicitcoercions=" <> pp (implicitCoercions opts)
          <+> text "--backtrack=" <> pp (backtrack opts)
          <+> text "--writesci=" <> pp (writeSCI opts)
          <+> text "--implicitbuiltin=" <> pp (implicitBuiltin opts)
          <+> text "--constraintstacksize=" <> pp (constraintStackSize opts)
          <+> text "--evaltimeout=" <> pp (evalTimeOut opts)
          <+> text "--failtypechecker=" <> pp (failTypechecker opts)
          <+> text "--externalsmt=" <> pp (externalSMT opts)
          <+> text "--checkassertions" <> pp (checkAssertions opts)
          <+> text "--forcerecomp" <> pp (forceRecomp opts)
          <+> text "--entrypoints" <> PP.sepBy (PP.char ':') (map pp $ entryPoints opts)

optionsDecl  :: Options
optionsDecl  = Opts { 
      inputs                = inputs defaultOptions &= args &= typ "FILE.sc"
    , outputs               = outputs defaultOptions &= typ "FILE1.sc:...:FILE2.sc" &= help "Output SecreC files"
    , paths                 = paths defaultOptions &= typ "DIR1:...:DIRn" &= help "Import paths for input SecreC program"
    , implicitBuiltin       = implicitBuiltin defaultOptions &= name "builtin" &= help "Implicitly import the builtin module"
    
    -- Transformation
    , simplify        = simplify defaultOptions &= help "Simplify the SecreC program" &= groupname "Transformation"
    , printOutput   = printOutput defaultOptions &= help "Print the output SecreC program to stdout" &= groupname "Transformation"
    
    -- Verification
    , typeCheck             = typeCheck defaultOptions &= name "tc" &= help "Typecheck the SecreC input" &= groupname "Verification"
    , verify    = verify defaultOptions &= help "Verify annotations" &= groupname "Verification"

    -- Debugging
    , debugLexer            = debugLexer defaultOptions &= help "Print lexer tokens to stderr" &= groupname "Debugging"
    , debugParser           = debugParser defaultOptions &= help "Print parser result to stderr" &= groupname "Debugging"
    , debugTypechecker      = debugTypechecker defaultOptions &= help "Print typechecker result to stderr" &= groupname "Debugging"
    , debugTransformation   = debugTransformation defaultOptions &= help "Print transformation result to stderr" &= groupname "Debugging"
    , debugVerification   = debugVerification defaultOptions &= help "Print verification result to stderr" &= groupname "Debugging"
    
    -- Typechecker
    , implicitCoercions   = implicitCoercions defaultOptions &= name "implicit" &= help "Enables implicit coercions" &= groupname "Verification:Typechecker"
    , backtrack   = backtrack defaultOptions &= help "Tells the typechecker to allow ambiguities arising form implicit coercions, and to resolve them by attempting multiple options" &= groupname "Verification:Typechecker"
    , externalSMT   = externalSMT defaultOptions &= name "smt" &= help "Use an external SMT solver for index constraints" &= groupname "Verification:Typechecker"
    , constraintStackSize   = constraintStackSize defaultOptions &= name "k-stack-size" &= help "Sets the constraint stack size for the typechecker" &= groupname "Verification:Typechecker"
    , evalTimeOut           = evalTimeOut defaultOptions &= help "Timeout for evaluation expression in the typechecking phase" &= groupname "Verification:Typechecker"
    , failTypechecker = failTypechecker defaultOptions &= name "fail-tc" &= help "Typechecker should fail" &= groupname "Verification:Typechecker"
    , checkAssertions = checkAssertions defaultOptions &= help "Check SecreC assertions" &= groupname "Verification:Typechecker"
    , forceRecomp = forceRecomp defaultOptions &= help "Force recompilation of SecreC modules" &= groupname "Verification:Typechecker"
    , writeSCI = writeSCI defaultOptions &= help "Write typechecking result to SecreC interface files" &= groupname "Verification:Typechecker"
    
    -- Analysis
    , entryPoints = entryPoints defaultOptions &= help "starting procedures and structs for analysis" &= groupname "Verification:Analysis"
    }
    &= help "SecreC analyser"

ppMode  :: Mode (CmdArgs Options)
ppMode  = cmdArgsMode $ modes [optionsDecl &= auto]

processOpts :: Options -> Options
processOpts opts = opts
    { outputs = parsePaths $ outputs opts
    , paths = parsePaths $ paths opts
    , entryPoints = parsePaths $ entryPoints opts
    , typeCheck = typeCheck opts || verify opts
    , checkAssertions = if verify opts then False else checkAssertions opts
    , simplify = if verify opts then True else simplify opts
    }

parsePaths :: [FilePath] -> [FilePath]
parsePaths = concatMap (splitOn ":")


