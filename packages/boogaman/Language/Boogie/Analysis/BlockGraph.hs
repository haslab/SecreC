{-# LANGUAGE ViewPatterns, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}

module Language.Boogie.Analysis.BlockGraph where

import Language.Boogie.Exts
import Language.Boogie.Position
import Language.Boogie.AST
import Language.Boogie.PrettyAST

import Data.Graph.Inductive.PatriciaTree as Gr
import Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.Basic as Gr
import Data.Graph.Inductive.Query.TransClos as Gr
import Data.Graph.Inductive.Query.ArtPoint as Gr
import Data.Monoid
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Data
import Data.Generics
import Data.Maybe
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.List

import Control.Monad.State as State

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace

type BlockM = State GraphSt

-- | A directed graph between blocks formed by gotos
type BlockGraph = Gr BasicBlock ()

basicBlocksGr :: [BasicBlock] -> BlockM BlockGraph
basicBlocksGr blocks = do
    let labels = map fst blocks
    nodes <- mapM labelGr labels
    let gr = Gr.mkGraph (zip nodes blocks) []
    foldM basicBlockGr gr blocks

basicBlockGr :: BlockGraph -> BasicBlock -> BlockM BlockGraph
basicBlockGr gr b@(l,ss) = do
    from <- labelGr l
    let add gr goto = do
        to <- labelGr goto
        return $ Gr.insEdge (from,to,()) gr
    foldM add gr (gotos ss)
    
gotos :: Data a => a -> [Id]
gotos = everything (++) (mkQ [] goto)
    where
    goto :: BareStatement -> [Id]
    goto (Goto ids) = ids
    goto _ = []

type BasicBlocksNext = ([BasicBlock],Maybe Id)

-- | Flattens a block graph into a sequence of consecutive blocks
flattenBlockGr :: Int -> BlockGraph -> Int -> [BasicBlocksNext]
flattenBlockGr start gr end = traverse [start] Set.empty gr' [] (Set.insert end points)
  where
    gr' = Gr.nfilter (flip Set.member reachable) gr
    reachable = Set.fromList $ Gr.suc (Gr.trc gr) start
    points = Set.fromList $ Gr.ap $ Gr.undir gr'
    traverse :: [Int] -> Set Int -> BlockGraph -> [BasicBlock] -> Set Int -> [BasicBlocksNext]
    traverse [] (Set.toList -> []) gr xs ps = wrap (xs,Nothing)
    traverse [] (Set.toList -> [l]) gr xs ps = case Gr.match l gr of
        (Just lctx@(_,_,_,outs),gr') -> wrap (xs,fmap fst $ lab gr l) ++ traverse (map snd outs) Set.empty gr' [fromJust $ lab gr l] (Set.delete l ps) 
        (Nothing,gr') -> error $ "label not found " ++ show l
    traverse [] as gr xs ps = error $ "multiple articulation points: " ++ show as
    traverse (l:ls) as gr xs ps = if Set.member l ps
        then traverse ls (Set.insert l as) gr xs ps
        else case Gr.match l gr of
            (Just lctx@(_,_,_,outs),gr') -> traverse ((map snd outs) ++ ls) as gr' (xs++[fromJust $ lab gr l]) ps
            (Nothing,gr') -> error $ "label not found " ++ show l
    wrap (xs,mb) = if null xs then [] else [(xs,mb)]

flattenBasicBlocks :: [BasicBlock] -> Id -> [BasicBlocksNext]
flattenBasicBlocks [] end = []
flattenBasicBlocks bs end = flip evalState (GraphSt Map.empty 0) $ do
    gr <- basicBlocksGr bs
    lstart <- labelGr (fst $ head bs)
    lend <- labelGr end
    let blocks = flattenBlockGr lstart gr lend
    --trace ("flatten: " ++ show end ++ "\n" ++ unlines (map (\(x,y) -> show (map fst x,y)) blocks) ++ "\n") $
    return blocks


prettifyBlockGr :: BlockGraph -> String
prettifyBlockGr g = prettify $ nmap fst g




