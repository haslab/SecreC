{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, FlexibleContexts, DoAndIfThenElse #-}

module Language.SecreC.Modules where

import Prelude hiding (elem)

import Data.Foldable as Foldable
import Data.Maybe as Maybe
import Data.UnixTime
import Data.Either
import Data.Binary
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
import Control.Monad.Catch
import Control.Monad.Writer as Writer
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (Reader(..),ReaderT(..),ask)
import qualified Control.Monad.Reader as Reader

import System.FilePath.Find as FilePath hiding (modificationTime)
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

type IdNodes = Map Identifier (FilePath -- ^ module's file
                              ,Node -- ^ module's node id
                              ,Bool) -- ^ opened (@True@) or closed (@False@) module

type ModuleGraph = Gr ModuleFile Position

-- | Parses and resolves imports, returning all the modules to be loaded, in evaluation order 
parseModuleFiles :: ModK m => [FilePath] -> SecrecM m [ModuleFile]
parseModuleFiles files = do
    g <- flip State.evalStateT (Map.empty,0) $ openModuleFiles files empty
    g' <- dirtyParents g
    let modules = topsort' g'
    return modules

resolveModule :: ModK m => FilePath -> SecrecM m FilePath
resolveModule file = do
    let m = ModuleName (UnhelpfulPos "resolveModule") (takeBaseName file)
    opts <- ask
    findModule (takeDirectory file : paths opts) m

-- | Opens a list of modules by filename
openModuleFiles :: ModK m => [FilePath] -> ModuleGraph -> StateT (IdNodes,Int) (SecrecM m) ModuleGraph
openModuleFiles fs g = foldlM open g fs
    where
    open g f = do
        f' <- lift $ resolveModule f
        mfile <- lift $ parseModuleFile f'
        opts <- ask
        let mfile' = case mfile of
                        Left (ppargs,ast) -> if (implicitBuiltin opts && moduleIdMb ast /= Just "builtin")
                            then Left (ppargs,addModuleImport (Import noloc $ ModuleName noloc "builtin") ast)
                            else Left (ppargs,ast)
                        Right sci -> Right sci
        openModule Nothing g f' (moduleFileId mfile') noloc (return mfile')

-- | Collects a graph of module dependencies from a list of SecreC input files
-- ^ Keeps a mapping of modules to node ids and a node counter
openModule :: ModK m => Maybe (Position,Node) -> ModuleGraph -> FilePath -> Identifier -> Position -> SecrecM m ModuleFile -> StateT (IdNodes,Int) (SecrecM m) ModuleGraph
openModule parent g f n pos load = do
    (ns,c) <- State.get
    g' <- case Map.lookup n ns of
        Just (f',i,False) -> if f == f'
            -- open an already closed module
            then return $ insParent parent i g
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
            let g' = case parent of
                        Nothing -> insNode (c,mfile) g
                        Just (l,j) -> insEdge (c,j,l) $ insNode (c,mfile) g
            -- open imports
            foldlM (openImport c) g' (moduleFileImports mfile)
    closeModule n
    return g'
  where
    insParent Nothing i = id
    insParent (Just (l,j)) i = insEdge (i,j,l)

closeModule :: ModK m => Identifier -> StateT (IdNodes,Int) (SecrecM m) ()
closeModule n = State.modify $ \(ns,c) -> (Map.adjust (\(x,y,z) -> (x,y,False)) n ns,c) 

openImport :: ModK m => Node -> ModuleGraph -> ImportDeclaration Identifier Position -> StateT (IdNodes,Int) (SecrecM m) ModuleGraph
openImport parent g (Import sl mn@(ModuleName l n)) = do
    f <- lift $ resolveModule n
    openModule (Just (sl,parent)) g f n l (parseModuleFile f)

parseModuleFile :: ModK m => String -> SecrecM m ModuleFile
parseModuleFile fn = do
    mb <- readModuleSCI fn
    case mb of
        Nothing -> liftM Left $ parseFile fn
        Just x -> return $ Right x

-- re-parse parent modules whose dependencies have changed
dirtyParents :: ModK m => ModuleGraph -> SecrecM m ModuleGraph
dirtyParents g = do
    let chgs = map fst $ filter (isLeft . snd) $ labNodes g
    let chgs' = Set.fromList (chgs ++ reachablesGr chgs g)
    mapGrM (reparse chgs') g
  where
    reparse is (froms,i,(Right sci),tos) | Set.member i is = do
        ast <- parseFile (sciFile sci)
        return (froms,i,Left ast,tos)
    reparse is ctx = return ctx

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


writeModuleSCI :: (MonadIO m,Location loc) => PPArgs -> Module Identifier loc -> TcM m ()
writeModuleSCI ppargs m = do
    let fn = moduleFile m
    menv <- State.gets (snd . moduleEnv)
    t <- liftIO $ liftM (fromEpochTime . modificationTime) $ getFileStatus fn
    let scifn = replaceExtension fn "sci"
    e <- liftIO $ tryIOError $ encodeFile scifn $ ModuleSCI fn (moduleId m) (map (fmap locpos) $ moduleImports m) t ppargs menv
    case e of
        Left ioerr -> when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr $ "Error writing SecreC interface file " ++ show scifn
        Right () -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr $ "Wrote SecreC interface file " ++ show scifn
            return ()

readModuleSCI :: (MonadReader Options m,MonadWriter SecrecWarnings m,MonadError SecrecError m,MonadIO m) => FilePath -> m (Maybe ModuleSCI)
readModuleSCI fn = do
    opts <- Reader.ask
    let scifn = replaceExtension fn "sci"
    e <- liftIO $ tryIOError $ decodeFileOrFailLazy scifn
    case e of
        Left ioerr -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr $ "Failed to find SecreC interface file " ++ show scifn
            return Nothing
        Right (Left (_,err)) -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr $ "Error loading SecreC interface file " ++ show scifn
            return Nothing
        Right (Right sci) -> do
            t <- liftIO $ liftM (fromEpochTime . modificationTime) $ getFileStatus fn
            if (sciFile sci == fn && t <= sciTime sci)
                then return $ Just sci
                else do
                    when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr $ "SecreC file " ++ show fn ++ " has changed."
                    return Nothing