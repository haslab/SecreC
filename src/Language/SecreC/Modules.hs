{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, ScopedTypeVariables, ConstraintKinds, FlexibleContexts, DoAndIfThenElse #-}

module Language.SecreC.Modules where

import Prelude hiding (elem)

import Data.Foldable as Foldable
import Data.Maybe as Maybe
import Data.UnixTime
import Data.Either
import Data.Typeable
import Data.Binary
import Data.Data
import Data.Binary.Get
import Data.Binary.Put
import Data.ByteString.Lazy (ByteString(..))
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
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
import Control.Monad.Writer.Strict as Writer
import Control.Monad.State.Strict (State(..),StateT(..))
import qualified Control.Monad.State.Strict as State
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

-- | Parses and resolves imports, returnSing all the modules to be loaded, in evaluation order 
parseModuleFiles :: ModK m => [FilePath] -> SecrecM m [ModuleFile]
parseModuleFiles files = do
    g <- flip State.evalStateT (Map.empty,0) $ openModuleFiles files empty
    opts <- ask
    let modules = topsort' g
    returnS modules

resolveModule :: ModK m => FilePath -> SecrecM m FilePath
resolveModule file = do
    let m = ModuleName (UnhelpfulPos "resolveModule") (takeBaseName file)
    opts <- ask
    f <- findModule (takeDirectory file : paths opts) m   
    liftIO $ canonicalPath f

localOptsModuleM :: Monad m => (Options -> Options) -> ModuleM m a -> ModuleM m a
localOptsModuleM f m = State.mapStateT (Reader.local f) m

-- | Opens a list of modules by filename
openModuleFiles :: ModK m => [FilePath] -> ModuleGraph -> ModuleM m ModuleGraph
openModuleFiles fs g = foldlM open g fs
    where
    open g f = do
        f' <- lift $ resolveModule f
        mfile <- lift $ parseModuleFile f'
        localOptsModuleM (`mappend` ppOptions (moduleFilePPArgs mfile)) $
            openModule Nothing g f' (moduleFileId mfile) noloc (returnS mfile)

-- | Collects a graph of module dependencies from a list of SecreC input files
-- ^ Keeps a mapping of modules to node ids and a node counter
openModule :: ModK m => Maybe (Position,Node) -> ModuleGraph -> FilePath -> Identifier -> Position -> SecrecM m ModuleFile -> ModuleM m ModuleGraph
openModule parent g f n pos load = do
    (ns,c) <- State.get
    g' <- case Map.lookup n ns of
        Just (f',i,False) -> if f == f'
            -- open an already closed module
            then do
                returnS $ insParent parent i g
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
    returnS g''
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
        then do
            sciError $ "Forcing load of SecreC file " ++ show fn
            parse
        else do
            mb <- readModuleSCI fn
            case mb of
                Nothing -> parse
                Just x -> returnS $ Right x
  where
    parse = do
        (args,m,mlength) <- parseFileWithBuiltin fn
        t <- liftIO $ fileModificationTime fn
        returnS $ Left (t,args,m,mlength)

parseFileWithBuiltin :: ModK m => FilePath -> SecrecM m (PPArgs,Module Identifier Position,Int)
parseFileWithBuiltin fn = flushWarnings $ do
    opts <- ask
    (args,m,mlength) <- parseFile fn
    let m' = if (implicitBuiltin (opts `mappend` ppOptions args) && moduleIdMb m /= Just "builtin")
        then addModuleImport (Import noloc $ ModuleName noloc "builtin") m
        else m
    returnS (args,m',mlength)

-- recursively update the modification time of parent modules
dirtyParents :: ModK m => Node -> ModuleGraph -> ModuleM m ModuleGraph
dirtyParents i g = case contextGr g i of
    Nothing -> returnS g
    Just (_,_,n,parents) -> dirtyParents' (map snd parents) (moduleFileName n) (moduleFileModificationTime n) g
  where
    dirtyParents' :: ModK m => [Node] -> FilePath -> UnixTime -> ModuleGraph -> ModuleM m ModuleGraph
    dirtyParents' [] pn pt g = returnS g
    dirtyParents' (i:is) pn pt g = case contextGr g i of
        Nothing -> dirtyParents' is pn pt g
        Just (_,_,inode,iparents) -> if moduleFileModificationTime inode >= pt
            -- we can stop if the parent module has a more recent modification time
            then dirtyParents' is pn pt g
            -- dirty recursively
            else do
                lift $ sciError $ "Child " ++ show pn ++ " changed at timestamp " ++ show pt
                lift $ sciError $ "Parent " ++ show (moduleFileName inode) ++ " changed at timestamp " ++ show (moduleFileModificationTime inode)
                inode' <- lift $ update inode pn pt
                dirtyParents' (is++map snd iparents) pn pt (insNode (i,inode') g)
    update (Left (_,args,m,mlength)) pn pt = returnS $ Left (pt,args,m,mlength)
    update (Right sci) pn t = do
        let fn = sciFile sci
        sciError $ "The dependency " ++ show pn ++ " of the SecreC file " ++ show fn ++ " has changed"
        (args,m,mlines) <- parseFileWithBuiltin (sciFile sci)
        returnS $ Left (t,args,m,mlines)

-- | Finds a file in the path from a module name
findModule :: ModK m => [FilePath] -> ModuleName Identifier Position -> SecrecM m FilePath
findModule [] (ModuleName l n) = modError l $ ModuleNotFound n
findModule (p:ps) mn@(ModuleName l n) = do
    files <- liftIO $ FilePath.find (depth ==? 0) (canonicalName ==? addExtension n "sc") p
    case files of
        [] -> findModule ps mn
        [file] -> returnS file
        otherwise -> modError l $ ModuleNotFound n 

findModuleCycle :: ModK m => Node -> ModuleGraph -> SecrecM m [(Identifier,Identifier,Position)]
findModuleCycle i g = do
    let ns = fromJust $ Foldable.find (i `elem`) (scc g)
    let g' = nfilter (`elem` ns) g
    let es = labEdges g'
    let label = moduleFileId . fromJust . lab g'
    let xs = map (\(from,to,lab) -> (label from,label to,lab)) es
    returnS xs

type ModK m = (MonadIO m,MonadCatch m)

fileModificationTime :: FilePath -> IO UnixTime
fileModificationTime fn = catchIOError
    (liftM (fromEpochTime . modificationTime) $ getFileStatus fn)
    (const $ returnS $ UnixTime (CTime 0) 0)

writeModuleSCI :: (MonadIO m,Location loc) => PPArgs -> ModuleTcEnv -> Module Identifier loc -> Int -> SecrecM m ()
writeModuleSCI ppargs menv m mlength = do
    opts <- ask
    when (writeSCI opts) $ do
        let fn = moduleFile m
        t <- liftIO $ fileModificationTime fn
        let scifn = replaceExtension fn "sci"
        let header = SCIHeader fn t (moduleId m) mlength Map.empty
        let body = SCIBody ppargs (map (fmap locpos) $ moduleImports m) menv
        e <- trySCI ("Error writing SecreC interface file " ++ show scifn) $ encodeFile scifn $ ModuleSCI header body
        case e of
            Nothing -> returnS ()
            Just () -> sciError $ "Wrote SecreC interface file " ++ show scifn ++ " with timestamp " ++ show (sciHeaderModTime header)
    
readModuleSCI :: MonadIO m => FilePath -> SecrecM m (Maybe ModuleSCI)
readModuleSCI fn = do
    let scifn = replaceExtension fn "sci"
    e <- trySCI ("SecreC interface file " ++ show scifn ++ " not found") $ BL.readFile scifn
    case e of
        Just input -> go (runGetIncremental get) input fn scifn
        Nothing -> returnS Nothing
  where
    go :: MonadIO m => Decoder SCIHeader -> ByteString -> FilePath -> FilePath -> SecrecM m (Maybe ModuleSCI)
    go (Done leftover consumed header) input fn scifn = do
        opts <- ask
        t <- liftIO $ fileModificationTime fn
        if (sciHeaderFile header == fn && t <= sciHeaderModTime header)
            then do
                sciError $ "SecreC file " ++ show fn ++ " has not changed"
                let e = runGetOrFail get (BL.chunk leftover input)
                case e of
                    Right (_,_,body) -> returnS $ Just $ ModuleSCI header body
                    Left (_,_,err) -> sciError ("Error loading SecreC interface file body " ++ show scifn) >> returnS Nothing
            else sciError ("SecreC file " ++ show fn ++ " has changed") >> returnS Nothing
    go (Partial k) input fn scifn = go (k . takeHeadChunk $ input) (dropHeadChunk input) fn scifn
    go (Fail leftover consumed msg) input fn scifn = sciError ("Error loading SecreC interface file header " ++ show scifn) >> returnS Nothing
    
readModuleSCIHeader :: MonadIO m => FilePath -> SecrecM m (Maybe (SCIHeader,ByteString))
readModuleSCIHeader fn = do
    let scifn = replaceExtension fn "sci"
    e <- trySCI ("SecreC interface file " ++ show scifn ++ " not found") $ liftM BL.fromStrict $ BS.readFile scifn
    case e of
        Just input -> case runGetOrFail get input of
            Left err -> sciError ("Error loading SecreC interface file header " ++ show scifn) >> returnS Nothing
            Right (leftover,consumed,header) -> do
                returnS $ Just (header,BL.append (BL.drop consumed input) leftover)
        Nothing -> returnS Nothing

updateModuleSCIHeader :: MonadIO m => FilePath -> (SCIHeader -> SecrecM m (Maybe SCIHeader)) -> SecrecM m ()
updateModuleSCIHeader scifn chg = do
    opts <- Reader.ask
    when (writeSCI opts) $ do
        mb <- readModuleSCIHeader scifn
        case mb of
            Nothing -> sciError ("Error updating SecreC interface file header " ++ show scifn)
            Just (header,body) -> do
                mb <- chg header
                case mb of
                    Nothing -> returnS ()
                    Just header' -> do
                        let bstr = runPut $ do
                            put header'
                            putLazyByteString body
                        e <- trySCI ("Error updating SecreC interface file header " ++ show scifn) $ BL.writeFile scifn bstr
                        case e of
                            Nothing -> returnS ()
                            Just () -> sciError $ "Updated SecreC interface file header " ++ show scifn

trySCI :: MonadIO m => String -> IO a -> SecrecM m (Maybe a)
trySCI msg io = do
    e <- liftIO $ tryIOError io
    case e of
        Left ioerr -> do
            opts <- Reader.ask
            sciError msg
            when (debug opts) $ liftIO $ putStrLn $ "trySCI: " ++ show ioerr
            returnS Nothing
        Right x -> returnS $ Just x

sciError :: MonadIO m => String -> SecrecM m ()
sciError msg = do
    opts <- Reader.ask
    when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr msg

moduleVarId :: Module VarIdentifier loc -> VarIdentifier
moduleVarId m = maybe (mkVarId "main") id $ moduleIdMb m

moduleGId :: Module GIdentifier loc -> GIdentifier
moduleGId m = maybe (MIden $ mkVarId "main") id $ moduleIdMb m

type ModuleFile = GModuleFile Identifier Position
type TypedModuleFile = GModuleFile GIdentifier (Typed Position)
type GModuleFile iden loc = Either (UnixTime,PPArgs,Module iden loc,Int) ModuleSCI

moduleFileName :: Location loc => GModuleFile iden loc -> FilePath
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

moduleFilePPArgs :: ModuleFile -> PPArgs
moduleFilePPArgs (Left (_,pp,_,_)) = pp
moduleFilePPArgs (Right sci) = sciPPArgs sci

-- module interface data
data ModuleSCI = ModuleSCI {
      sciHeader :: SCIHeader
    , sciBody :: SCIBody
    } deriving Generic

sciFile = sciHeaderFile . sciHeader
sciVerified = sciHeaderVerified . sciHeader
sciModTime = sciHeaderModTime . sciHeader
sciId = sciHeaderId . sciHeader
sciLines = sciHeaderLines . sciHeader
sciImports = sciBodyImports . sciBody
sciPPArgs = sciBodyPPArgs . sciBody
sciEnv = sciBodyEnv . sciBody

updModTime sci t = sci { sciHeader = (sciHeader sci) { sciHeaderModTime = t } }

instance Binary ModuleSCI

data DafnyId
    = PId POId ModuleTyVarId
    | FId POId ModuleTyVarId Bool
    | LId GIdentifier ModuleTyVarId Bool
    | SId GIdentifier ModuleTyVarId
    | AId ModuleTyVarId Bool
  deriving (Data,Typeable,Generic,Show,Eq,Ord)
instance Binary DafnyId

type VDafnyIds = Map DafnyId VerifyOpt

data SCIHeader = SCIHeader {
      sciHeaderFile :: FilePath
    , sciHeaderModTime :: UnixTime
    , sciHeaderId :: Identifier -- module identifier
    , sciHeaderLines :: Int -- number of lines
    , sciHeaderVerified :: VDafnyIds -- has been verified or not
    } deriving Generic
instance Binary SCIHeader

data SCIBody = SCIBody {
      sciBodyPPArgs :: PPArgs -- preprocessor arguments used for typechecking the module
    , sciBodyImports :: [ImportDeclaration Identifier Position] -- module dependencies 
    , sciBodyEnv :: ModuleTcEnv -- typechecking environment
    } deriving Generic
instance Binary SCIBody
