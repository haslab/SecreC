{-# LANGUAGE DoAndIfThenElse #-}

module Language.SecreC.Modules where

import Prelude hiding (elem)

import Data.Foldable as Foldable
import Data.Maybe as Maybe

import Data.Graph.Inductive
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map

import Control.Monad
import Control.Monad.Writer as Writer
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (Reader(..),ReaderT(..),ask)
import qualified Control.Monad.Reader as Reader

import System.FilePath.Find as FilePath
import System.FilePath
import System.Directory

import Language.SecreC.Syntax
import Language.SecreC.Monad
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Parser
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Utils

type IdNodes = Map Identifier (FilePath -- ^ module's file
                              ,Node -- ^ module's node id
                              ,Bool) -- ^ opened (@True@) or closed (@False@) module

type ModuleGraph = Gr (PPArgs,Module Identifier Position) Position

-- | Parses and resolves imports, returning all the modules to be loaded, in evaluation order 
parseModuleFiles :: MonadIO m => [FilePath] -> SecrecM m [(PPArgs,Module Identifier Position)]
parseModuleFiles files = do
    g <- flip State.evalStateT (Map.empty,0) $ openModuleFiles files empty
    let modules = topsort' g
    return modules

resolveModule :: MonadIO m => FilePath -> SecrecM m FilePath
resolveModule file = do
    let m = ModuleName (UnhelpfulPos "resolveModule") (takeBaseName file)
    opts <- ask
    findModule (takeDirectory file : paths opts) m

-- | Opens a list of modules by filename
openModuleFiles :: MonadIO m => [FilePath] -> ModuleGraph -> StateT (IdNodes,Int) (SecrecM m) ModuleGraph
openModuleFiles fs g = foldlM open g fs
    where
    open g f = do
        f' <- lift $ resolveModule f
        (ppargs,ast) <- lift $ parseFile f'
        opts <- ask
        let ast' = if (implicitBuiltin opts && moduleId ast /= Just "builtin")
            then addModuleImport (Import noloc $ ModuleName noloc "builtin") ast
            else ast
        openModule Nothing g f' (modulePosId ast') (loc ast') (return (ppargs,ast'))

-- | Collects a graph of module dependencies from a list of SecreC input files
-- ^ Keeps a mapping of modules to node ids and a node counter
openModule :: MonadIO m => Maybe (Position,Node) -> ModuleGraph -> FilePath -> Identifier -> Position -> SecrecM m (PPArgs,Module Identifier Position) -> StateT (IdNodes,Int) (SecrecM m) ModuleGraph
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
            -- parse the module
            (ppargs,ast) <- lift load
            -- add new node and edge from parent
            State.put (Map.insert n (f,c,True) ns,succ c)
            let g' = case parent of
                        Nothing -> insNode (c,(ppargs,ast)) g
                        Just (p,n) -> insEdge (c,n,p) $ insNode (c,(ppargs,ast)) g
            -- open imports
            foldlM (openImport c) g' (moduleImports ast)
    closeModule n
    return g'
  where
    insParent Nothing i = id
    insParent (Just (l,j)) i = insEdge (i,j,l)

closeModule :: MonadIO m => Identifier -> StateT (IdNodes,Int) (SecrecM m) ()
closeModule n = State.modify $ \(ns,c) -> (Map.adjust (\(x,y,z) -> (x,y,False)) n ns,c) 

openImport :: MonadIO m => Node -> ModuleGraph -> ImportDeclaration Identifier Position -> StateT (IdNodes,Int) (SecrecM m) ModuleGraph
openImport parent g (Import sl mn@(ModuleName l n)) = do
    f <- lift $ resolveModule n
    openModule (Just (sl,parent)) g f n l (parseFile f)
    
-- | Finds a file in the path from a module name
findModule :: MonadIO m => [FilePath] -> ModuleName Identifier Position -> SecrecM m FilePath
findModule [] (ModuleName l n) = modError l $ ModuleNotFound n
findModule (p:ps) mn@(ModuleName l n) = do
    files <- liftIO $ FilePath.find (depth ==? 0) (canonicalName ==? addExtension n "sc") p
    case files of
        [] -> findModule ps mn
        [file] -> return file
        otherwise -> modError l $ ModuleNotFound n 

findModuleCycle :: MonadIO m => Node -> ModuleGraph -> SecrecM m [(Identifier,Identifier,Position)]
findModuleCycle i g = do
    let ns = fromJust $ Foldable.find (i `elem`) (scc g)
    let g' = nfilter (`elem` ns) g
    let es = labEdges g'
    let label = modulePosId . snd . fromJust . lab g'
    let xs = map (\(from,to,lab) -> (label from,label to,lab)) es
    return xs



