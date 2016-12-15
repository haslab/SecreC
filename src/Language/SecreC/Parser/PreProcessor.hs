{-# LANGUAGE MultiParamTypeClasses, DeriveGeneric, FlexibleInstances, TypeSynonymInstances, FlexibleContexts, DeriveDataTypeable, TupleSections, TypeFamilies #-}

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

import Text.PrettyPrint ((<+>),(<>),text,($+$),Doc(..))
import qualified Text.PrettyPrint as PP
import Text.Parsec
import Text.Parsec.Pos
import Text.Read

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
import Data.List
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

instance Monad m => PP m PPArgs where
    pp args = liftM PP.vcat $ mapM pp args

instance Monad m => PP m PPArg where
    pp (SecrecOpts opts) = liftM (text "#OPTIONS_SECREC" <+>) (pp opts)

type PPParserT u m a = ParsecT [Char] u m a
    
runPP :: (MonadIO m) => FilePath -> SecrecM m PPArgs
runPP file = do
--    liftIO $ putStrLn $ "parsing ppfile " ++ show file
    str <- liftIO $ readFile file
    mapM (parsePP file) (filter (isPrefixOf "#") $ lines str)

parsePP :: MonadIO m => FilePath -> String -> SecrecM m PPArg
parsePP file str = do
--    liftIO $ putStrLn $ "parsing pp " ++ show str
    mb <- runParserT parsePPArg () file str
    case mb of
        Left err -> throwError $ ParserError $ PreProcessorException $ show err
        Right x -> return x

parsePPArg :: MonadIO m => PPParserT u m PPArg
parsePPArg = do
    char '#'
    string "OPTIONS_SECREC"
    spaces
    str <- many anyChar
    o <- cmdArgsRunPP ppMode (words str)
    return $ SecrecOpts $ processOpts o

-- * CmdArgs options

cmdArgsRunPP :: MonadIO m => Mode (CmdArgs a) -> [String] -> PPParserT u m a
cmdArgsRunPP m xs = do
    args <- case process m (preprocessArgs xs) of
            Left err -> unexpected $ "Error parsing pre-processor options " ++ show xs ++": " ++ show err
            Right x -> return x
    liftIO $ cmdArgsApply args

instance Monad m => PP m Options where
    pp opts = do
        pp1 <- (mapM pp $ inputs opts)
        pp2 <- (mapM pp $ outputs opts)
        pp3 <- (mapM pp $ paths opts)
        pp4 <- pp (verify opts)
        pp5 <- pp (simplify opts)
        pp6 <- pp (printOutput opts)
        pp7 <- pp (debug opts)
        pp8 <- pp (typeCheck opts)
        pp9 <- pp (debugLexer opts)
        pp10 <- pp (debugParser opts)
        pp11 <- pp (debugTypechecker opts)
        pp12 <- pp (debugTransformation opts)
        pp13 <- pp (debugVerification opts)
        pp14 <- pp (implicitCoercions opts)
        pp141 <- pp (implicitContext opts)
        pp142 <- pp (promote opts)
        pp15 <- pp (backtrack opts)
        pp151 <- pp (matching opts)
        pp16 <- pp (writeSCI opts)
        pp17 <- pp (implicitBuiltin opts)
        pp18 <- pp (constraintStackSize opts)
        pp19 <- pp (evalTimeOut opts)
        pp20 <- pp (failTypechecker opts)
        pp21 <- pp (externalSMT opts)
        pp22 <- pp (checkAssertions opts)
        pp23 <- pp (forceRecomp opts)
        pp24 <- (mapM pp $ entryPoints opts)
        pp25 <- pp (defaults opts)
        pp26 <- pp (progress opts)
        return $ PP.sepBy PP.space pp1
            <+> text "--outputs=" <> PP.sepBy (PP.char ':') pp2
            <+> text "--paths=" <> PP.sepBy (PP.char ':') pp3
            <+> text "--verify=" <> pp4
            <+> text "--simplify=" <> pp5
            <+> text "--printoutput=" <> pp6
            <+> text "--debug=" <+> pp7
            <+> text "--typecheck=" <> pp8
            <+> text "--debuglexer=" <> pp9
            <+> text "--debugparser=" <> pp10
            <+> text "--debugtypechecker=" <> pp11
            <+> text "--debugtransformation=" <> pp12
            <+> text "--debugverify=" <> pp13
            <+> text "--implicitcoercions=" <> pp14
            <+> text "--promote=" <> pp142
            <+> text "--implicitcontext=" <> pp141
            <+> text "--backtrack=" <> pp15
            <+> text "--matching=" <> pp151
            <+> text "--writesci=" <> pp16
            <+> text "--implicitbuiltin=" <> pp17
            <+> text "--constraintstacksize=" <> pp18
            <+> text "--evaltimeout=" <> pp19
            <+> text "--failtypechecker=" <> pp20
            <+> text "--externalsmt=" <> pp21
            <+> text "--checkassertions" <> pp22
            <+> text "--forcerecomp" <> pp23
            <+> text "--entrypoints" <> PP.sepBy (PP.char ':') pp24
            <+> text "--defaults" <> pp25
            <+> text "--progress" <> pp26

contextMsg :: Doc
contextMsg = PP.text "Controls template constraint resolution" $+$ PP.nest 4 (
        PP.text "delayctx" <+> PP.char '=' <+> PP.text "Delay template resolution"
    $+$ PP.text "inferctx" <+> PP.char '=' <+> PP.text "Try to solve as many constraints as possible"
    )

coercionMsg :: Doc
coercionMsg = PP.text "Controls implicit coercions" $+$ PP.nest 4 (
        PP.text "offc" <+> PP.char '=' <+> PP.text "No implicit coercions"
    $+$ PP.text "defaultsc" <+> PP.char '=' <+> PP.text "Only for default declarations"
    $+$ PP.text "onc" <+> PP.char '=' <+> PP.text "For regular code (Default)"
    $+$ PP.text "extendedc" <+> PP.char '=' <+> PP.text "For regular code and annotations"
    )

matchingMsg :: Doc
matchingMsg = PP.text "Solving order for constraints" $+$ PP.nest 4 (
        PP.text "orderedc" <+> PP.char '=' <+> PP.text "In code order for all constraints"
    $+$ PP.text "gorderedc" <+> PP.char '=' <+> PP.text "In code order for global constraints"
    $+$ PP.text "unorderedc" <+> PP.char '=' <+> PP.text "In any order (Default)"
    )

promoteMsg :: Doc
promoteMsg = PP.text "Promote constraints when matching template instantiations" $+$ PP.nest 4 (
        PP.text "localp" <+> PP.char '=' <+> PP.text "Promote only local constraints"
    $+$ PP.text "globalp" <+> PP.char '=' <+> PP.text "Promote global constraints"
    $+$ PP.text "nop" <+> PP.char '=' <+> PP.text "Do not promote constraints"
    )

backtrackMsg :: Doc
backtrackMsg = PP.text "Control ambiguities in template matching arising from template overloading and implicit coercions" $+$ PP.nest 4 (
        PP.text "noneb" <+> PP.char '=' <+> PP.text "Do not allow multiple matches"
    $+$ PP.text "tryb" <+> PP.char '=' <+> PP.text "Try first match (not exhaustive)"
    $+$ PP.text "fullb" <+> PP.char '=' <+> PP.text "Backtrack and try all matches (Default)"
    )

verifyMsg :: Doc
verifyMsg = PP.text "Verify annotations" $+$ PP.nest 4 (
        PP.text "bothv" <+> PP.char '=' <+> PP.text "Verify both functional correctness and leakage properties"
    $+$ PP.text "leakv" <+> PP.char '=' <+> PP.text "Verify only leakage properties"
    $+$ PP.text "funcv" <+> PP.char '=' <+> PP.text "Verify only functional correctness properties"
    $+$ PP.text "nonev" <+> PP.char '=' <+> PP.text "Do not verify annotations (Default)"
    )

optionsDecl  :: Options
optionsDecl  = Opts { 
      inputs                = inputs defaultOptions &= args &= typ "FILE.sc"
    , outputs               = outputs defaultOptions &= typ "FILE1.sc:...:FILE2.sc" &= help "Output SecreC files"
    , progress              = progress defaultOptions &= help "Show progress bar"
    , paths                 = paths defaultOptions &= typ "DIR1:...:DIRn" &= help "Import paths for input SecreC program"
    , implicitBuiltin       = implicitBuiltin defaultOptions &= name "builtin" &= help "Implicitly import the builtin module"
    
    -- Transformation
    , simplify        = simplify defaultOptions &= help "Simplify the SecreC program" &= groupname "Transformation"
    , printOutput   = printOutput defaultOptions &= help "Print the output SecreC program to stdout" &= groupname "Transformation"
    
    -- Verification
    , typeCheck             = typeCheck defaultOptions &= name "tc" &= help "Typecheck the SecreC input" &= groupname "Verification"
    , verify    = verify defaultOptions &= help (show verifyMsg) &= groupname "Verification"

    -- Debugging
    , debug   = debug defaultOptions &= help "Prints developer debugging information" &= groupname "Debugging"
    , debugCheck            = debugCheck defaultOptions &= help "Check for inconsistencies during typechecking" &= groupname "Debugging"
    , debugLexer            = debugLexer defaultOptions &= help "Print lexer tokens to stderr" &= groupname "Debugging"
    , debugParser           = debugParser defaultOptions &= help "Print parser result to stderr" &= groupname "Debugging"
    , debugTypechecker      = debugTypechecker defaultOptions &= help "Print typechecker result to stderr" &= groupname "Debugging"
    , debugTransformation   = debugTransformation defaultOptions &= help "Print transformation result to stderr" &= groupname "Debugging"
    , debugVerification   = debugVerification defaultOptions &= help "Print verification result to stderr" &= groupname "Debugging"
    
    -- Typechecker
    , defaults   = defaults defaultOptions &= help "Generate default variable initializations" &= groupname "Verification:Typechecker"
    , implicitCoercions   = implicitCoercions defaultOptions &= name "implicit" &= help (show coercionMsg) &= groupname "Verification:Typechecker"
    , promote      = promote defaultOptions &= help (show promoteMsg) &= groupname "Verification:TypeChecker"
    , implicitContext   = implicitContext defaultOptions &= help (show contextMsg) &= groupname "Verification:Typechecker"
    , backtrack   = backtrack defaultOptions &= help (show backtrackMsg) &= groupname "Verification:Typechecker"
    , matching   = matching defaultOptions &= help (show matchingMsg) &= groupname "Verification:Typechecker"
    , externalSMT   = externalSMT defaultOptions &= name "smt" &= help "Use an external SMT solver for index constraints" &= groupname "Verification:Typechecker"
    , constraintStackSize   = constraintStackSize defaultOptions &= name "k-stack-size" &= help "Sets the constraint stack size for the typechecker" &= groupname "Verification:Typechecker"
    , evalTimeOut           = evalTimeOut defaultOptions &= help "Timeout for evaluation expression in the typechecking phase" &= groupname "Verification:Typechecker"
    , failTypechecker = failTypechecker defaultOptions &= name "fail-tc" &= help "Typechecker should fail" &= groupname "Verification:Typechecker"
    , checkAssertions = checkAssertions defaultOptions &= help "Check SecreC assertions" &= groupname "Verification:Typechecker"
    , forceRecomp = forceRecomp defaultOptions &= help "Force recompilation of SecreC modules" &= groupname "Verification:Typechecker"
    , writeSCI = writeSCI defaultOptions &= help "Write typechecking result to SecreC interface files" &= groupname "Verification:Typechecker"
    , ignoreSpecDomains = ignoreSpecDomains defaultOptions &= help "Ignore domains in specifications" &= groupname "Verification:Typechecker"
    
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
    , typeCheck = if verify opts /= NoneV then True else typeCheck opts
    , checkAssertions = if verify opts /= NoneV then False else checkAssertions opts
    , simplify = if verify opts /= NoneV then True else simplify opts
    , backtrack = if (implicitCoercions opts > OffC) then backtrack opts else NoneB
    }

parsePaths :: [FilePath] -> [FilePath]
parsePaths = map unAspas . concatMap (splitOn ":")
    where
    unAspas :: String -> String
    unAspas x = case readMaybe x :: Maybe String of
        Just str -> str
        Nothing -> x


