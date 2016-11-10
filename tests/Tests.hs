module Main where

import Data.List as List

import Control.Monad (when)

import System.IO (Handle, stderr, hPutStr, hPutStrLn)
import System.FilePath.Find as FilePath
import System.FilePath
import System.Process
import System.Exit
import System.Timeout

import Test.HUnit.Base
import Test.Hspec
import Test.Hspec.Contrib.HUnit (fromHUnitTest)
import Test.Hspec.Core.Runner (hspecWith, Config(..),defaultConfig)

-- Configs
fastfail = True
timelimit = 10 * 60

buildTestTree :: IO Test
buildTestTree = do
    
    tests <- buildTestDirectoryTree "tests"
--    return $ TestList [tests0]
    
    --    tests2 <- buildTestDirectoryTree "imports/stdlib"
    --    tests3 <- buildTestDirectoryTree "examples"
    
    tests5 <- buildTestDirectoryTree "examples/leakage/cut/cut.sc"
    tests6 <- buildTestDirectoryTree "examples/leakage/qsort/qsort.sc"
    return $ TestList [tests,tests5,tests6]
    

buildTestDirectoryTree :: FilePath -> IO Test
buildTestDirectoryTree path = fold (depth >=? 0) addTestFile (TestList []) path
    
addTestFile :: Test -> FileInfo -> Test
addTestFile t i = if evalClause (extension ==? ".sc") i
    then let p = evalClause filePath i in addTestToTree t (splitPath p) p
    else t

addTestToTree :: Test -> [FilePath] -> FilePath -> Test
addTestToTree (TestList xs) [] f = TestList $ testTypeChecker f : xs
addTestToTree (TestList xs) (d:ds) f = TestList $ addTestToList xs d ds f
addTestToTree (TestLabel l t) (d:ds) f | l == d = TestLabel l (addTestToTree t ds f)
addTestToTree t ds f = TestList [t,addTestToTree (TestList []) ds f]

addTestToList :: [Test] -> FilePath -> [FilePath] -> FilePath -> [Test]
addTestToList [] d ds f = [TestLabel d $ addTestToTree (TestList []) ds f]
addTestToList (TestLabel l t:xs) d ds f | l == d = TestLabel l (addTestToTree t ds f) : xs
addTestToList (x:xs) d ds f = x : addTestToList xs d ds f

hasLabel :: String -> Test -> Bool
hasLabel s (TestLabel l _) = s == l
hasLabel s t = False

data Result = ResSuccess | ResFailure Int | ResTimeout Int
  deriving (Eq,Show)

instance Assertable Result where
    assert ResSuccess = return ()
    assert (ResFailure i) = assertFailure $ "test failed with error code " ++ show i
    assert (ResTimeout t) = assertFailure $ "test timed out after " ++ show t ++ " seconds"

testTypeChecker :: FilePath -> Test
testTypeChecker f = test $ do
    code <- timeout (timelimit *10^6) (system $ "cabal exec -- secrec " ++ f)
    case code of
        Just ExitSuccess -> return ResSuccess
        Just (ExitFailure i) -> return $ ResFailure i
        Nothing -> return $ ResTimeout timelimit

--main = buildTestTree >>= runTestTT 

--HSpec main
main :: IO ()
main = do
    testSuite <- buildTestTree
    let cfg = defaultConfig { configFastFail = fastfail }
    hspecWith cfg $ describe "SecreC tests" $ fromHUnitTest testSuite


-- | Text-based test controller for running HUnit tests and reporting
--   results as text, usually to a terminal.


-- | As the general text-based test controller ('runTestText') executes a
--   test, it reports each test case start, error, and failure by
--   constructing a string and passing it to the function embodied in a
--   'PutText'.  A report string is known as a \"line\", although it includes
--   no line terminator; the function in a 'PutText' is responsible for
--   terminating lines appropriately.  Besides the line, the function
--   receives a flag indicating the intended \"persistence\" of the line:
--   'True' indicates that the line should be part of the final overall
--   report; 'False' indicates that the line merely indicates progress of
--   the test execution.  Each progress line shows the current values of
--   the cumulative test execution counts; a final, persistent line shows
--   the final count values.
--
--   The 'PutText' function is also passed, and returns, an arbitrary state
--   value (called 'st' here).  The initial state value is given in the
--   'PutText'; the final value is returned by 'runTestText'.

data PutText st = PutText (String -> Bool -> st -> IO st) st


-- | Two reporting schemes are defined here.  @putTextToHandle@ writes
-- report lines to a given handle.  'putTextToShowS' accumulates
-- persistent lines for return as a whole by 'runTestText'.
--
-- @putTextToHandle@ writes persistent lines to the given handle,
-- following each by a newline character.  In addition, if the given flag
-- is @True@, it writes progress lines to the handle as well.  A progress
-- line is written with no line termination, so that it can be
-- overwritten by the next report line.  As overwriting involves writing
-- carriage return and blank characters, its proper effect is usually
-- only obtained on terminal devices.

putTextToHandle
    :: Handle
    -> Bool -- ^ Write progress lines to handle?
    -> PutText Int
putTextToHandle handle showProgress = PutText put initCnt
 where
  initCnt = if showProgress then 0 else -1
  put line pers (-1) = do when pers (hPutStrLn handle line); return (-1)
  put line True  cnt = do hPutStrLn handle (erase cnt ++ line); return 0
  put line False _   = do hPutStr handle ('\r' : line); return (length line)
    -- The "erasing" strategy with a single '\r' relies on the fact that the
    -- lengths of successive summary lines are monotonically nondecreasing.
  erase cnt = if cnt == 0 then "" else "\r" ++ replicate cnt ' ' ++ "\r"


-- | Accumulates persistent lines (dropping progess lines) for return by
--   'runTestText'.  The accumulated lines are represented by a
--   @'ShowS' ('String' -> 'String')@ function whose first argument is the
--   string to be appended to the accumulated report lines.

putTextToShowS :: PutText ShowS
putTextToShowS = PutText put id
 where put line pers f = return (if pers then acc f line else f)
       acc f line rest = f (line ++ '\n' : rest)


-- | Executes a test, processing each report line according to the given
--   reporting scheme.  The reporting scheme's state is threaded through calls
--   to the reporting scheme's function and finally returned, along with final
--   count values.

runTestText :: PutText st -> Test -> IO (Counts, st)
runTestText (PutText put us0) t = do
  (counts', us1) <- performTest reportStart reportError reportFailure us0 t
  us2 <- put (showCounts counts') True us1
  return (counts', us2)
 where
  reportStart ss us = put (showCounts (counts ss)) False us
  reportError   = reportProblem "Error:"   "Error in:   "
  reportFailure = reportProblem "Failure:" "Failure in: "
  reportProblem p0 p1 loc msg ss us = put line True us >> error "stop"
   where line  = "### " ++ kind ++ path' ++ "\n" ++ formatLocation loc ++ msg
         kind  = if null path' then p0 else p1
         path' = showPath (path ss)

formatLocation :: Maybe Location -> String
formatLocation Nothing = ""
formatLocation (Just loc) = locationFile loc ++ ":" ++ show (locationLine loc) ++ "\n"

-- | Converts test execution counts to a string.

showCounts :: Counts -> String
showCounts Counts{ cases = cases', tried = tried',
                   errors = errors', failures = failures' } =
  "Cases: " ++ show cases' ++ "  Tried: " ++ show tried' ++
  "  Errors: " ++ show errors' ++ "  Failures: " ++ show failures'


-- | Converts a test case path to a string, separating adjacent elements by
--   the colon (\':\'). An element of the path is quoted (as with 'show') when
--   there is potential ambiguity.

showPath :: Path -> String
showPath [] = ""
showPath nodes = foldl1 f (map showNode nodes)
 where f b a = a ++ ":" ++ b
       showNode (ListItem n) = show n
       showNode (Label label) = safe label (show label)
       safe s ss = if ':' `elem` s || "\"" ++ s ++ "\"" /= ss then ss else s


-- | Provides the \"standard\" text-based test controller. Reporting is made to
--   standard error, and progress reports are included. For possible
--   programmatic use, the final counts are returned.
--
--   The \"TT\" in the name suggests \"Text-based reporting to the Terminal\".

runTestTT :: Test -> IO Counts
runTestTT t = do (counts', 0) <- runTestText (putTextToHandle stderr True) t
                 return counts'
