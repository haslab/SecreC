{-# LANGUAGE ViewPatterns, FlexibleContexts, DeriveDataTypeable, FlexibleInstances, TupleSections, DeriveTraversable, StandaloneDeriving #-}

module Language.Boogie.Exts where

import Language.Boogie.Position
import Language.Boogie.AST
import Language.Boogie.Pretty
import Language.Boogie.PrettyAST

import Control.Monad
import Control.Monad.State as State

import Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.PatriciaTree as Gr
import Data.Monoid hiding ((<>))
import Data.Data
import Data.Generics
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set

deriving instance Data NewType
deriving instance Data IdTypeWhere
deriving instance Data BareDecl
deriving instance Data Program
deriving instance Data BareStatement
deriving instance Data WildcardExpression
deriving instance Data SpecClause
deriving instance Data SpecType
deriving instance Data Contract

deriving instance Foldable Pos
deriving instance Traversable Pos

-- converts a block to a basic block (will fail if the block is not basic already)
toBasicBlocks' :: Block -> [BasicBlock]
toBasicBlocks' = toBasicBlocks'' Nothing
    where
    toBasicBlocks'' :: Maybe BasicBlock -> Block -> [BasicBlock]
    toBasicBlocks'' b (Left c:xs) = case toBasicBlocks'' b xs of
        (l,b):bs -> (l,Left c:b):bs
        [] -> []
    toBasicBlocks'' Nothing [] = []
    toBasicBlocks'' (Just b) [] = [b]
    toBasicBlocks'' Nothing (Right (unPos -> ([l],s)):ss) = toBasicBlocks'' (Just (l,[Right s])) ss
    toBasicBlocks'' (Just b) (Right (unPos -> ([l],s)):ss) = b : toBasicBlocks'' (Just (l,[Right s])) ss
    toBasicBlocks'' (Just (l,b)) (Right (unPos -> ([],s)):ss) = toBasicBlocks'' (Just (l,b++[Right s])) ss
    toBasicBlocks'' b bs = error $ "toBasicBlocks'' " ++ show b ++ " " ++ show bs

returnAsLastBlock :: [BasicBlock] -> [BasicBlock]
returnAsLastBlock bs = everywhere (mkT replaceReturn) bs ++ [(ret,[Right $ Pos noPos Return])]
    where
    replaceReturn :: BareStatement -> BareStatement
    replaceReturn Return = Goto [ret]
    replaceReturn s = s
    labels = Set.fromList $ map fst bs
    ret = freshLabel labels "ret_end"
    freshLabel :: Set Id -> Id -> Id
    freshLabel xs x = if Set.member x xs then freshLabel xs (x++"'") else x

mapFstM :: Monad m => (a -> m b) -> (a,c) -> m (b,c)
mapFstM f (x,y) = do
    x' <- f x
    return (x',y)

mapSndM :: Monad m => (c -> m b) -> (a,c) -> m (a,b)
mapSndM f (x,y) = do
    y' <- f y
    return (x,y')
    
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

instance Monoid (Gr.Gr a b) where
    mempty = Gr.empty
    mappend x y = Gr.insEdges (Gr.labEdges x ++ Gr.labEdges y) $ Gr.insNodes (Gr.labNodes x ++ Gr.labNodes y) Gr.empty

updLast :: (a -> a) -> [a] -> [a]
updLast f [] = []
updLast f xs = init xs ++ [f $ last xs]

data GraphSt = GraphSt { labels :: Map Id Int, next :: Int }

labelGr :: MonadState GraphSt m => Id -> m Int
labelGr l = do
    st <- State.get
    case Map.lookup l (labels st) of
        Just i -> return i
        Nothing -> do
            let i = next st
            State.modify $ \st -> st { labels = Map.insert l i (labels st) , next = succ i }
            return i

wildTT = Expr posTT
wildFF = Expr posFF
posTT = Pos noPos tt
posFF = Pos noPos ff

andExprs :: [Expression] -> Expression
andExprs [] = posTT
andExprs es = foldl1 (\e1 e2 -> Pos noPos $ BinaryExpression And e1 e2) es

impliesExpr :: Expression -> Expression -> Expression
impliesExpr e1 e2 = Pos noPos $ BinaryExpression Implies e1 e2

startLabelBBs :: [BasicBlock] -> Id
startLabelBBs [] = error "no start label"
startLabelBBs ((l,b):bs) = l

isBoolUnOp :: UnOp -> Bool
isBoolUnOp Not = True
isBoolUnOp o = False

isBoolBinOp :: BinOp -> Bool
isBoolBinOp And = True
isBoolBinOp Or = True
isBoolBinOp Implies = True
isBoolBinOp o = False

hasOldExpr :: Expression -> Bool
hasOldExpr = everything (||) (mkQ False aux)
    where
    aux :: BareExpression -> Bool
    aux (Old _) = True
    aux e = False

instance Pretty SpecClause where
    pretty (SpecClause _ isAssume e) = (if isAssume then text "assume" else text "assert") <+> pretty e

instance Pretty Contract where
    pretty (Requires free e) = option free (text "free") <+>
      text "requires" <+>
      pretty e <>
      semi
    pretty (Ensures free e) = option free (text "free") <+>
      text "ensures" <+>
      pretty e <>
      semi
    pretty (Modifies free ids) = option free (text "free") <+>
      text "modifies" <+>
      commaSep (map text ids) <>
      semi
      
bareDeclName :: BareDecl -> Maybe Id
bareDeclName (FunctionDecl _ n _ _ _ _) = Just n
bareDeclName (ProcedureDecl _ n _ _ _ _ _) = Just n
bareDeclName (ImplementationDecl _ n _ _ _ _) = Just n
bareDeclName bd = Nothing



