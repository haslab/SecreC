{-# LANGUAGE DeriveGeneric, ScopedTypeVariables, ConstraintKinds, FlexibleContexts, DoAndIfThenElse #-}

module Language.SecreC.Modules where

import Prelude hiding (elem)

import Data.Foldable as Foldable
import Data.Maybe as Maybe
import Data.UnixTime
import Data.Either
import Data.Binary
import Data.Binary.Get
import Data.ByteString.Lazy (ByteString(..))
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Internal as BL
import Data.Graph.Inductive
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (MonadReader(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Catch hiding (catchIOError)
import Control.Monad.Writer as Writer
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (Reader(..),ReaderT(..),ask)
import qualified Control.Monad.Reader as Reader

import System.FilePath.Find as FilePath hiding (modificationTime,canonicalPath)
import System.FilePath
import System.Directory
import System.IO
import System.IO.Error
import System.Posix.Files

import Language.SecreC.Syntax
import Language.SecreC.Monad
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Parser
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Utils
import Language.SecreC.TypeChecker.Base

import GHC.Generics (Generic(..))

import Foreign.C.Types

type IdNodes = Map Identifier (FilePath -- ^ module's file
                              ,Node -- ^ module's node id
                              ,Bool) -- ^ opened (@True@) or closed (@False@) module

type ModuleGraph = Gr ModuleFile Position

type ModuleM m = StateT (IdNodes,Int) (SecrecM m)

-- | Parses and resolves imports, returning all the modules to be loaded, in evaluation order 
parseModuleFiles :: ModK m => [FilePath] -> SecrecM m [ModuleFile]
parseModuleFiles files = do
    g <- flip State.evalStateT (Map.empty,0) $ openModuleFiles files empty
    opts <- ask
    let modules = topsort' g
    return modules

resolveModule :: ModK m => FilePath -> SecrecM m FilePath
resolveModule file = do
    let m = ModuleName (UnhelpfulPos "resolveModule") (takeBaseName file)
    opts <- ask
    f <- findModule (takeDirectory file : paths opts) m   
    liftIO $ canonicalPath f

-- | Opens a list of modules by filename
openModuleFiles :: ModK m => [FilePath] -> ModuleGraph -> ModuleM m ModuleGraph
openModuleFiles fs g = foldlM open g fs
    where
    open g f = do
        f' <- lift $ resolveModule f
        mfile <- lift $ parseModuleFile f'
        openModule Nothing g f' (moduleFileId mfile) noloc (return mfile)

-- | Collects a graph of module dependencies from a list of SecreC input files
-- ^ Keeps a mapping of modules to node ids and a node counter
openModule :: ModK m => Maybe (Position,Node) -> ModuleGraph -> FilePath -> Identifier -> Position -> SecrecM m ModuleFile -> ModuleM m ModuleGraph
openModule parent g f n pos load = do
    (ns,c) <- State.get
    g' <- case Map.lookup n ns of
        Just (f',i,False) -> if f == f'
            -- open an already closed module
            then do
                return $ insParent parent i g
            -- two files with the same module name
            else modError pos $ DuplicateModuleName n f f'
        -- dependency cycle
        Just (f',i,True) -> do
            let g' = insParent parent i g
            cycle <- lift $ findModuleCycle i g'
            modError pos $ CircularModuleDependency cycle
        Nothing -> do
            -- parse the module or load it from an interface
            mfile <- lift load
            -- add new node and edge to parent
            State.put (Map.insert n (f,c,True) ns,succ c)
            let g' = insParent parent c $ insNode (c,mfile) g
            -- open imports
            foldlM (openImport c) g' (moduleFileImports mfile)
    g'' <- dirtyParents c g'
    closeModule n
    return g''
  where
    insParent Nothing i = id
    insParent (Just (l,j)) i = insEdge (i,j,l)

closeModule :: ModK m => Identifier -> ModuleM m ()
closeModule n = State.modify $ \(ns,c) -> (Map.adjust (\(x,y,z) -> (x,y,False)) n ns,c) 

openImport :: ModK m => Node -> ModuleGraph -> ImportDeclaration Identifier Position -> ModuleM m ModuleGraph
openImport parent g (Import sl mn@(ModuleName l n)) = do
    f <- lift $ resolveModule n
    openModule (Just (sl,parent)) g f n l (parseModuleFile f)

parseModuleFile :: ModK m => String -> SecrecM m ModuleFile
parseModuleFile fn = do
    opts <- ask
    if forceRecomp opts
        then parse
        else do
            mb <- readModuleSCI fn
            case mb of
                Nothing -> parse
                Just x -> return $ Right x
  where
    parse = do
        (args,m,mlength) <- parseFileWithBuiltin fn
        t <- liftIO $ fileModificationTime fn
        return $ Left (t,args,m,mlength)

parseFileWithBuiltin :: ModK m => FilePath -> SecrecM m (PPArgs,Module Identifier Position,Int)
parseFileWithBuiltin fn = flushWarnings $ do
    opts <- ask
    (args,m,mlength) <- parseFile fn
    let m' = if (implicitBuiltin (opts `mappend` ppOptions args) && moduleIdMb m /= Just "builtin")
        then addModuleImport (Import noloc $ ModuleName noloc "builtin") m
        else m
    return (args,m',mlength)

-- recursively update the modification time of parent modules
dirtyParents :: ModK m => Node -> ModuleGraph -> ModuleM m ModuleGraph
dirtyParents i g = case contextGr g i of
    Nothing -> return g
    Just (_,_,n,parents) -> dirtyParents' (map snd parents) (moduleFileModificationTime n) g
  where
    dirtyParents' :: ModK m => [Node] -> UnixTime -> ModuleGraph -> ModuleM m ModuleGraph
    dirtyParents' [] t g = return g
    dirtyParents' (i:is) t g = case contextGr g i of
        Nothing -> dirtyParents' is t g
        Just (_,_,inode,iparents) -> if moduleFileModificationTime inode >= t
            -- we can stop if the parent module has a more recent modification time
            then dirtyParents' is t g
            -- dirty recursively
            else do
                inode' <- lift $ update inode t
                dirtyParents' (is++map snd iparents) t (insNode (i,inode') g)
    update (Left (_,args,m,mlength)) t = return $ Left (t,args,m,mlength)
    update (Right sci) t = do
        sciError $ "A dependency of the SecreC file " ++ show (sciFile sci) ++ " has changed"
        (args,m,mlines) <- parseFileWithBuiltin (sciFile sci)
        return $ Left (t,args,m,mlines)

-- | Finds a file in the path from a module name
findModule :: ModK m => [FilePath] -> ModuleName Identifier Position -> SecrecM m FilePath
findModule [] (ModuleName l n) = modError l $ ModuleNotFound n
findModule (p:ps) mn@(ModuleName l n) = do
    files <- liftIO $ FilePath.find (depth ==? 0) (canonicalName ==? addExtension n "sc") p
    case files of
        [] -> findModule ps mn
        [file] -> return file
        otherwise -> modError l $ ModuleNotFound n 

findModuleCycle :: ModK m => Node -> ModuleGraph -> SecrecM m [(Identifier,Identifier,Position)]
findModuleCycle i g = do
    let ns = fromJust $ Foldable.find (i `elem`) (scc g)
    let g' = nfilter (`elem` ns) g
    let es = labEdges g'
    let label = moduleFileId . fromJust . lab g'
    let xs = map (\(from,to,lab) -> (label from,label to,lab)) es
    return xs

type ModK m = (MonadIO m,MonadCatch m)

fileModificationTime :: FilePath -> IO UnixTime
fileModificationTime fn = catchIOError
    (liftM (fromEpochTime . modificationTime) $ getFileStatus fn)
    (const $ return $ UnixTime (CTime 0) 0)

writeModuleSCI :: (MonadIO m,Location loc) => PPArgs -> ModuleTcEnv -> Module Identifier loc -> Int -> SecrecM m ()
writeModuleSCI ppargs menv m mlength = do
    opts <- ask
    when (writeSCI opts) $ do
        let fn = moduleFile m
        t <- liftIO $ fileModificationTime fn
        let scifn = replaceExtension fn "sci"
        let header = SCIHeader fn t (moduleId m) mlength
        let body = SCIBody (map (fmap locpos) $ moduleImports m) ppargs menv
        e <- trySCI ("Error writing SecreC interface file " ++ show scifn) $ encodeFile scifn $ ModuleSCI header body
        case e of
            Nothing -> return ()
            Just () -> sciError $ "Wrote SecreC interface file " ++ show scifn
    
readModuleSCI :: MonadIO m => FilePath -> SecrecM m (Maybe ModuleSCI)
readModuleSCI fn = do
    let scifn = replaceExtension fn "sci"
    e <- trySCI ("SecreC interface file " ++ show scifn ++ " not found") $ BL.readFile scifn
    case e of
        Just input -> go (runGetIncremental get) input fn scifn
        Nothing -> return Nothing
  where
    go :: MonadIO m => Decoder SCIHeader -> ByteString -> FilePath -> FilePath -> SecrecM m (Maybe ModuleSCI)
    go (Done leftover consumed header) input fn scifn = do
        t <- liftIO $ fileModificationTime fn
        if (sciHeaderFile header == fn && t <= sciHeaderModTime header)
            then do
                sciError $ "SecreC file " ++ show fn ++ " has not changed"
                let e = runGetOrFail get (BL.chunk leftover input)
                case e of
                    Right (_,_,body) -> return $ Just $ ModuleSCI header body
                    Left (_,_,err) -> sciError ("Error loading SecreC interface file body " ++ show scifn) >> return Nothing
            else sciError ("SecreC file " ++ show fn ++ " has changed") >> return Nothing
    go (Partial k) input fn scifn = go (k . takeHeadChunk $ input) (dropHeadChunk input) fn scifn
    go (Fail leftover consumed msg) input fn scifn = sciError ("Error loading SecreC interface file header " ++ show scifn) >> return Nothing
 
trySCI :: MonadIO m => String -> IO a -> SecrecM m (Maybe a)
trySCI msg io = do
    e <- liftIO $ tryIOError io
    case e of
        Left ioerr -> sciError msg >> return Nothing
        Right x -> return $ Just x

sciError :: MonadIO m => String -> SecrecM m ()
sciError msg = do
    opts <- Reader.ask
    when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr msg

moduleVarId :: Module VarIdentifier loc -> VarIdentifier
moduleVarId m = maybe (mkVarId "main") id $ moduleIdMb m

moduleGId :: Module GIdentifier loc -> GIdentifier
moduleGId m = maybe (MIden $ mkVarId "main") id $ moduleIdMb m
    
type ModuleFile = Either (UnixTime,PPArgs,Module Identifier Position,Int) ModuleSCI
type TypedModuleFile = Either (UnixTime,PPArgs,Module GIdentifier (Typed Position),Int) ModuleSCI

moduleFileName :: ModuleFile -> FilePath
moduleFileName (Left (_,_,m,ml)) = moduleFile m
moduleFileName (Right sci) = sciFile sci

moduleFileId :: ModuleFile -> Identifier
moduleFileId (Left (_,_,m,ml)) = moduleId m
moduleFileId (Right sci) = sciId sci

moduleFileImports :: ModuleFile -> [ImportDeclaration Identifier Position]
moduleFileImports (Left (_,_,m,ml)) = moduleImports m
moduleFileImports (Right sci) = sciImports sci

moduleFileModificationTime :: ModuleFile -> UnixTime
moduleFileModificationTime (Left (t,_,_,ml)) = t
moduleFileModificationTime (Right sci) = sciModTime sci

updModuleFileModificationTime :: ModuleFile -> UnixTime -> ModuleFile
updModuleFileModificationTime (Left (t,a,m,ml)) t' = Left (t',a,m,ml)
updModuleFileModificationTime (Right sci) t' = Right $ updModTime sci t'

-- module interface data
data ModuleSCI = ModuleSCI {
      sciHeader :: SCIHeader
    , sciBody :: SCIBody
    } deriving Generic

sciFile = sciHeaderFile . sciHeader
sciModTime = sciHeaderModTime . sciHeader
sciId = sciHeaderId . sciHeader
sciLines = sciHeaderLines . sciHeader
sciImports = sciBodyImports . sciBody
sciPPArgs = sciBodyPPArgs . sciBody
sciEnv = sciBodyEnv . sciBody

updModTime sci t = sci { sciHeader = (sciHeader sci) { sciHeaderModTime = t } }

instance Binary ModuleSCI

data SCIHeader = SCIHeader {
      sciHeaderFile :: FilePath
    , sciHeaderModTime :: UnixTime
    , sciHeaderId :: Identifier -- module identifier
    , sciHeaderLines :: Int -- number of lines
    } deriving Generic
instance Binary SCIHeader

data SCIBody = SCIBody {
      sciBodyImports :: [ImportDeclaration Identifier Position] -- module dependencies 
    , sciBodyPPArgs :: PPArgs -- preprocessor arguments used for typechecking the module
    , sciBodyEnv :: ModuleTcEnv -- typechecking environment
    } deriving Generic
instance Binary SCIBody
