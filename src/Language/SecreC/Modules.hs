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

import Language.SecreC.Syntax
import Language.SecreC.Monad
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Parser.Parsec
--import Language.SecreC.Parser.Derp


type IdNodes = Map Identifier (FilePath -- ^ module's file
                              ,Node -- ^ module's node id
                              ,Bool) -- ^ opened (@True@) or closed (@False@) module

type ModuleGraph = Gr (Module Position) Position

-- | Parses and resolves imports, returning all the modules to be loaded, in evaluation order 
parseModuleFiles :: [FilePath] -> SecrecM [Module Position]
parseModuleFiles files = liftM topsort' $ State.evalStateT (openModuleFiles files empty) (Map.empty,1)

-- | Opens a list of modules by filename
openModuleFiles :: [FilePath] -> ModuleGraph -> StateT (IdNodes,Int) SecrecM ModuleGraph
openModuleFiles fs g = foldlM open g fs
    where
    open g f = do
        ast <- lift $ parseFile f
        openModule Nothing g f (moduleId ast) (loc ast) (return ast)

-- | Collects a graph of module dependencies from a list of SecreC input files
-- ^ Keeps a mapping of modules to node ids and a node counter
openModule :: Maybe (Position,Node) -> ModuleGraph -> FilePath -> Identifier -> Position -> SecrecM (Module Position) -> StateT (IdNodes,Int) SecrecM ModuleGraph
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
            ast <- lift load
            -- add new node and edge from parent
            State.put (Map.insert n (f,c,True) ns,succ c)
            let g' = (maybeToList parent,c,ast,[]) & g
            -- open imports
            foldlM (openImport c) g' (moduleImports ast)
    closeModule n
    return g'
  where
    insParent Nothing i = id
    insParent (Just (l,j)) i = insEdge (j,i,l)

closeModule :: Identifier -> StateT (IdNodes,Int) SecrecM ()
closeModule n = State.modify $ \(ns,c) -> (Map.adjust (\(x,y,z) -> (x,y,False)) n ns,c) 

openImport :: Node -> ModuleGraph -> ImportDeclaration Position -> StateT (IdNodes,Int) SecrecM ModuleGraph
openImport parent g (Import sl mn@(ModuleName l n)) = do
    opts <- ask
    f <- lift $ findModule (paths opts) mn
    openModule (Just (sl,parent)) g f n l (parseFile f)
    
-- | Finds a file in the path from a module name
findModule :: [FilePath] -> ModuleName Position -> SecrecM FilePath
findModule [] (ModuleName l n) = modError l $ ModuleNotFound n
findModule (p:ps) mn@(ModuleName l n) = do
    files <- liftIO $ FilePath.find (depth ==? 0) (canonicalName ==? addExtension n "sc") p
    case files of
        [] -> findModule ps mn
        [file] -> return file
        otherwise -> modError l $ ModuleNotFound n 

findModuleCycle :: Node -> ModuleGraph -> SecrecM [(Identifier,Identifier,Position)]
findModuleCycle i g = do
    let ns = fromJust $ Foldable.find (i `elem`) (scc g)
    let g' = nfilter (`elem` ns) g
    let es = labEdges g'
    let label = moduleId . fromJust . lab g'
    let xs = map (\(from,to,lab) -> (label from,label to,lab)) es
    return xs



