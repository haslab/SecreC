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
import Data.Either

type BBSt = (Set Id,Int)

startLabel :: Block -> Id
startLabel [] = error "no start label"
startLabel (Left c:bs) = startLabel bs
startLabel (Right b:bs) = case fst (unPos b) of
    (l:ls) -> l
    otherwise -> startLabel bs

blockLabels :: Block -> Set Id
blockLabels = mconcat . map (bareLabels . unPos) . rights
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
    tbs <- concat <$> (mapM (transformCommentOrLStatement M.empty) body)
    -- By the properties of transform, tbs' is a sequence of basic blocks
    let tbs' = attach start (tbs ++ [Right $ justBareStatement Return])  
    return $ reverse $ foldl append [] tbs'
  where
    -- Append a labeled statement to a sequence of basic blocks
    -- (the first labeled statement cannot have empty label)
    append :: [BasicBlock] -> Either Comment BareLStatement -> [BasicBlock]
    append ((l,ss):bbs) (Left c) = (l,Left c:ss):bbs
    append bbs (Right ([l], Pos _ Skip)) = (l, []) : bbs
    append bbs (Right ([l], s)) = (l, [Right s]) : bbs
    append ((l, ss) : bbs) (Right ([], s)) = (l, ss ++ [Right s]) :  bbs      

fromBasicBlocks :: [BasicBlock] -> Block
fromBasicBlocks = concatMap fromBasicBlock
    where
    fromBasicBlock :: BasicBlock -> Block
    fromBasicBlock (l,[]) = []
    fromBasicBlock (l,Left c:ss) = Left c : fromBasicBlock (l,ss)
    fromBasicBlock (l,Right s:ss) = Right (Pos noPos ([l],s)) : map (either Left (Right . Pos noPos . ([],))) ss

-- | Attach a label to the first statement (with an empty label) in a non-empty list of labeled statements    
attach :: Id -> [Either Comment BareLStatement] -> [Either Comment BareLStatement]
attach l (Left c:xs) = Left c : attach l xs
attach l (Right ([], stmts) : lsts) = Right ([l], stmts) : lsts

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

transformCommentOrLStatement :: Map Id Id -> Either Comment LStatement -> State BBSt [Either Comment BareLStatement]  
transformCommentOrLStatement m (Left c) = return [Left c]
transformCommentOrLStatement m (Right x) = transform m $ node x

transform :: Map Id Id -> BareLStatement -> State BBSt [Either Comment BareLStatement]  
transform m (l:lbs, Pos p Skip) = do
  t <- transform m (lbs, Pos p Skip)
  return $ (Right $ justBareStatement $ Goto [l]) : attach l t
transform m (l:lbs, stmt) = do
  lDone <- state $ genFreshLabel "done"
  t <- transform (M.insert l lDone m) (lbs, stmt)
  return $ [Right $ justBareStatement $ Goto [l]] ++ attach l t ++ [Right $ justBareStatement $ Goto [lDone], Right $ justLabel lDone]
transform m ([], Pos p stmt) = case stmt of  
  Goto lbs -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [Right $ justStatement p (Goto lbs), Right $ justLabel lUnreach]
  Break (Just l) -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [Right $ justStatement p (Goto [m ! l]), Right $ justLabel lUnreach]
  Break Nothing -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [Right $ justStatement p (Goto [m ! innermost]), Right $ justLabel lUnreach]
  Return -> do
    lUnreach <- state $ genFreshLabel "unreachable"
    return $ [Right $ justStatement p Return, Right $ justLabel lUnreach]
  If cond thenBlock Nothing -> transform m (justStatement p (If cond thenBlock (Just [])))
  If we thenBlock (Just elseBlock) -> do
    lThen <- state $ genFreshLabel "then"
    lElse <- state $ genFreshLabel "else"
    lDone <- state $ genFreshLabel "done"
    t1 <- transBlock m thenBlock
    t2 <- transBlock m elseBlock
    case we of
      Wildcard -> return $ 
        [Right $ justStatement p $ Goto [lThen, lElse]] ++ 
        attach lThen (t1 ++ [Right $ justStatement (lastPos thenBlock p) $ Goto [lDone]]) ++
        attach lElse (t2 ++ [Right $ justStatement (lastPos elseBlock p) $ Goto [lDone]]) ++
        [Right $ justLabel lDone]
      Expr e -> return $
        [Right $ justStatement p $ Goto [lThen, lElse]] ++
        [Right $ ([lThen], assume e)] ++ t1 ++ [Right $ justStatement (lastPos thenBlock (position e)) $ Goto [lDone]] ++
        [Right $ ([lElse], assume (enot e))] ++ t2 ++ [Right $ justStatement (lastPos elseBlock (position e)) $ Goto [lDone]] ++
        [Right $ justLabel lDone]      
  While Wildcard invs body -> do
    lHead <- state $ genFreshLabel "head"
    lBody <- state $ genFreshLabel "body"
    lDone <- state $ genFreshLabel "done"
    t <- transBlock (M.insert innermost lDone m) body
    return $
      [Right $ justStatement p $ Goto [lHead]] ++
      attach lHead (map checkInvariant invs ++ [Right $ justStatement p $ Goto [lBody, lDone]]) ++ 
      attach lBody (t ++ [Right $ justStatement (lastPos body p) $ Goto [lHead]]) ++
      [Right $ justLabel lDone]
  While (Expr e) invs body -> do
    lHead <- state $ genFreshLabel "head"
    lBody <- state $ genFreshLabel "body"
    lGDone <- state $ genFreshLabel "guarded_done"
    lDone <- state $ genFreshLabel "done"
    t <- transBlock (M.insert innermost lDone m) body
    return $
      [Right $ justStatement p $ Goto [lHead]] ++
      attach lHead (map checkInvariant invs ++ [Right $ justStatement p $ Goto [lGDone, lBody]]) ++
      [Right ([lBody], assume e)] ++ t ++ [Right $ justStatement (lastPos body (position e)) $ Goto [lHead]] ++
      [Right ([lGDone], assume (enot e))] ++ [Right $ justStatement (position e) $ Goto [lDone]] ++
      [Right $ justLabel lDone]    
  _ -> return [Right $ justStatement p stmt]  
  where
    transBlock :: Map Id Id -> Block -> State BBSt [Either Comment BareLStatement]
    transBlock m b = liftM concat $ mapM (transformCommentOrLStatement m) b
    checkInvariant :: SpecClause -> Either Comment BareLStatement
    checkInvariant inv = Right $ justStatement (position (specExpr inv)) (Predicate [] inv)
    lastPos :: Block -> SourcePos -> SourcePos
    lastPos block def = if null bs then def else position (last bs)
        where bs = rights block
