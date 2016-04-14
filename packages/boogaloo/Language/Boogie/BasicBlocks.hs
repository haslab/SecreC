{-# LANGUAGE TupleSections #-}

-- | Basic block transformation for imperative Boogie code
module Language.Boogie.BasicBlocks (toBasicBlocks,fromBasicBlocks,startLabel) where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as Set
import Control.Monad.State
import Control.Applicative

type BBSt = (Set Id,Int)

startLabel :: Block -> Id
startLabel [] = error "no start label"
startLabel (b:bs) = case fst (unPos b) of
    (l:ls) -> l
    otherwise -> startLabel bs

blockLabels :: Block -> Set Id
blockLabels = mconcat . map (bareLabels . unPos)
    where
    bareLabels (ids,s) = Set.fromList ids `Set.union` stmtLabels (unPos s)
    stmtLabels (If _ b1 b2) = blockLabels b1 `Set.union` maybe Set.empty blockLabels b2
    stmtLabels (While _ _ b) = blockLabels b
    stmtLabels s = Set.empty

-- | Transform procedure body into a sequence of basic blocks.
-- A basic block starts with a label and contains no jump, if or while statements,
-- except for the last statement, which can be a goto or return.
toBasicBlocks :: Block -> [BasicBlock]
toBasicBlocks body = flip evalState (blockLabels body,0) $ do
    -- Label of the first block in a procedure
    start <- state $ genFreshLabel "start"
    -- First flatten control flow with transform, and then convert to basic blocks
    tbs <- concat <$> (mapM (transform M.empty) (map node body))
    -- By the properties of transform, tbs' is a sequence of basic blocks
    let tbs' = attach start (tbs ++ [justBareStatement Return])  
    return $ reverse $ foldl append [] tbs'
  where
    -- Append a labeled statement to a sequence of basic blocks
    -- (the first labeled statement cannot have empty label)
    append :: [BasicBlock] -> BareLStatement -> [BasicBlock]
    append bbs ([l], Pos _ Skip) = (l, []) : bbs
    append bbs ([l], s) = (l, [s]) : bbs
    append ((l, ss) : bbs) ([], s) = (l, ss ++ [s]) :  bbs      

fromBasicBlocks :: [BasicBlock] -> Block
fromBasicBlocks = concatMap fromBasicBlock
    where
    fromBasicBlock :: BasicBlock -> Block
    fromBasicBlock (l,[]) = []
    fromBasicBlock (l,s:ss) = map (Pos noPos) $ ([l],s) : map ([],) ss

-- | Attach a label to the first statement (with an empty label) in a non-empty list of labeled statements    
attach :: Id -> [BareLStatement] -> [BareLStatement]
attach l (([], stmts) : lsts) = ([l], stmts) : lsts

-- | LStatement with no label (no source position, generated)
justBareStatement s = ([], gen s)

-- | LStatement with no label (with a source position, derived from a source statement)
justStatement pos s = ([], Pos pos s)

-- | LStatement with no statement
justLabel l = ([l], gen Skip)

-- | Special label value that denoted the innermost loop (used for break) 
innermost = "innermost"

-- | genFreshLabel kind i: returns a label of kind with id i and the id for the next label
genFreshLabel :: String -> BBSt -> (String,BBSt)
genFreshLabel kind (ks,i) = if Set.member k ks then genFreshLabel k (ks,i) else (k,(ks,succ i))
    where
    k = kind ++ "_" ++ show i

-- | transform m statement: transform statement into a sequence of basic blocks;
-- m is a map from statement labels to labels of their exit points (used for break)
transform :: Map Id Id -> BareLStatement -> State BBSt [BareLStatement]  
transform m (l:lbs, Pos p Skip) = do
  t <- transform m (lbs, Pos p Skip)
  return $ (justBareStatement $ Goto [l]) : attach l t
transform m (l:lbs, stmt) = do
  lDone <- state $ genFreshLabel "done"
  t <- transform (M.insert l lDone m) (lbs, stmt)
  return $ [justBareStatement $ Goto [l]] ++ attach l t ++ [justBareStatement $ Goto [lDone], justLabel lDone]
transform m ([], Pos p stmt) = case stmt of  
  Goto lbs -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [justStatement p (Goto lbs), justLabel lUnreach]
  Break (Just l) -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [justStatement p (Goto [m ! l]), justLabel lUnreach]
  Break Nothing -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [justStatement p (Goto [m ! innermost]), justLabel lUnreach]
  Return -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [justStatement p Return, justLabel lUnreach]
  If cond thenBlock Nothing -> transform m (justStatement p (If cond thenBlock (Just [])))
  If we thenBlock (Just elseBlock) -> do
    lThen <- state $ genFreshLabel "then"
    lElse <- state $ genFreshLabel "else"
    lDone <- state $ genFreshLabel "done"
    t1 <- transBlock m thenBlock
    t2 <- transBlock m elseBlock
    case we of
      Wildcard -> return $ 
        [justStatement p $ Goto [lThen, lElse]] ++ 
        attach lThen (t1 ++ [justStatement (lastPos thenBlock p) $ Goto [lDone]]) ++
        attach lElse (t2 ++ [justStatement (lastPos elseBlock p) $ Goto [lDone]]) ++
        [justLabel lDone]
      Expr e -> return $
        [justStatement p $ Goto [lThen, lElse]] ++
        [([lThen], assume e)] ++ t1 ++ [justStatement (lastPos thenBlock (position e)) $ Goto [lDone]] ++
        [([lElse], assume (enot e))] ++ t2 ++ [justStatement (lastPos elseBlock (position e)) $ Goto [lDone]] ++
        [justLabel lDone]      
  While Wildcard invs body -> do
    lHead <- state $ genFreshLabel "head"
    lBody <- state $ genFreshLabel "body"
    lDone <- state $ genFreshLabel "done"
    t <- transBlock (M.insert innermost lDone m) body
    return $
      [justStatement p $ Goto [lHead]] ++
      attach lHead (map checkInvariant invs ++ [justStatement p $ Goto [lBody, lDone]]) ++ 
      attach lBody (t ++ [justStatement (lastPos body p) $ Goto [lHead]]) ++
      [justLabel lDone]
  While (Expr e) invs body -> do
    lHead <- state $ genFreshLabel "head"
    lBody <- state $ genFreshLabel "body"
    lGDone <- state $ genFreshLabel "guarded_done"
    lDone <- state $ genFreshLabel "done"
    t <- transBlock (M.insert innermost lDone m) body
    return $
      [justStatement p $ Goto [lHead]] ++
      attach lHead (map checkInvariant invs ++ [justStatement p $ Goto [lGDone, lBody]]) ++
      [([lBody], assume e)] ++ t ++ [justStatement (lastPos body (position e)) $ Goto [lHead]] ++
      [([lGDone], assume (enot e))] ++ [justStatement (position e) $ Goto [lDone]] ++
      [justLabel lDone]    
  _ -> return [justStatement p stmt]  
  where
    transBlock m b = concat <$> mapM (transform m) (map node b)
    checkInvariant inv = justStatement (position (specExpr inv)) (Predicate [] inv)
    lastPos block def = if null block then def else position (last block)
