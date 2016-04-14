{-# LANGUAGE DeriveDataTypeable, TupleSections, ViewPatterns, TypeSynonymInstances, FlexibleInstances #-}

module Language.Boogie.Analysis.Leakage where

import Language.Boogie.AST
import Language.Boogie.Position
import Language.Boogie.Exts
import Language.Boogie.PrettyAST
import Language.Boogie.Pretty

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Maybe as Maybe
import Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.Basic as Gr
import Data.Graph.Inductive.Query.TransClos as Gr
import Data.Graph.Inductive.PatriciaTree as Gr
import Data.Data
import Data.Generics
import Data.List as List

import Control.Monad.State as State

-- * Variable dependencies

-- | An undirected data flow graph between variables
type VarGraph = Gr Id ()

class VarGr a where
    varGr :: a -> LeakM VarGraph

-- a set of modified global variables and a state for generating graphs
type LeakM = StateT (Set Id) (State GraphSt)

instance VarGr [BasicBlock] where
    varGr = liftM mconcat . mapM varGr

instance VarGr BasicBlock where
    varGr (l,ss) = liftM mconcat $ mapM (varGr . node) ss

instance FVS [(Id,[[Expression]])] where
    fvs = mconcat . map fvs

instance FVS (Id,[[Expression]]) where
    fvs (x,y) = fvs x `mappend` fvs y
instance FVS [[Expression]] where
    fvs = mconcat . map fvs

instance VarGr BareStatement where
    varGr (Predicate _ spec) = varGr spec
    varGr (Havoc {}) = return Gr.empty
    varGr Skip = return Gr.empty
    varGr Return = return Gr.empty
    varGr (If {}) = error "bareStatementVarGraph: If unexpected"
    varGr (While {}) = error "bareStatementVarGraph: While unexpected"
    varGr (Break {}) = return Gr.empty
    varGr (Goto {}) = return Gr.empty
    varGr (Assign lhs rhs) = do
        let lvs = fvs lhs
        let rvs = fvs rhs
        crossGraph $ Set.unions [lvs,rvs]
    varGr (Call _ ids n es) = do
        modifies <- State.get
        let lvs = fvs ids
        let rvs = fvs es
        crossGraph $ Set.unions [modifies,lvs,rvs]
    varGr (CallForall n es) = do
        modifies <- State.get
        let rvs = fvs es
        crossGraph rvs

instance VarGr SpecClause where
    varGr = varGr . specExpr

instance VarGr Expression where
    varGr = crossGraph . fvs

crossGraph :: Set Id -> LeakM VarGraph
crossGraph (Set.toList -> ids) = do
    ks <- lift $ mapM labelGr ids
    let ls = zip ks ids
    return $ mkGraph ls [(x,y,()) | x <- ks, y <- ks]

-- * Leakage

-- a variable is benign if it depends on both input and output, false if it only depends on input
type IsBenign = Bool

data Leakage = Leakage
    { publics :: Map Id PublicType -- set of public variables
    , declassifieds :: Map Id IsBenign -- map from declassified variables to benign flag
    } deriving (Data,Typeable,Show,Eq)
instance Monoid Leakage where
    mempty = Leakage Map.empty Map.empty
    mappend (Leakage p1 d1) (Leakage p2 d2) = Leakage (Map.unionWith mappend p1 p2) (Map.unionWith (||) d1 d2)

class Leaks a where
    leakage :: a -> Leakage

instance Leaks [BasicBlock] where
    leakage = mconcat . map leakage
instance Leaks BasicBlock where
    leakage = leakage . snd
instance Leaks [Statement] where
    leakage = mconcat . map leakage
instance Leaks a => Leaks (Pos a) where
    leakage (Pos _ x) = leakage x
instance Leaks a => Leaks (Maybe a) where
    leakage = maybe mempty leakage
instance Leaks BareStatement where
    leakage s@(hasPublicId -> Just is) = Leakage is Map.empty
    leakage s@(hasDeclassified -> Just is) = Leakage Map.empty (mapKeyVars is)
    leakage (If e b1 b2) = leakage b1 `mappend` leakage b2
    leakage (While e _ b) = leakage b
    leakage s = mempty   
instance Leaks Block where
    leakage = mconcat . map leakage
instance Leaks BareLStatement where
    leakage = leakage . snd

mapKeyVars :: Data a => Map a b -> Map Id b
mapKeyVars = Map.foldrWithKey (\k v xs -> Map.fromSet (const v) (vars k) `Map.union` xs) Map.empty

vars :: Data a => a -> Set Id
vars = everything Set.union (mkQ Set.empty aux)
    where
    aux :: BareExpression -> Set Id
    aux (Var i) = Set.singleton i
    aux _ = Set.empty

-- computes the extended leakage from the variable dependencies of a program slice
computeLeakage :: Set Id -> [BasicBlock] -> Leakage
computeLeakage modifies bs = flip evalState (GraphSt Map.empty 0) $ flip evalStateT modifies $ do
    varsgr <- varGr bs
    let leaks = leakage bs
    let (public_ins,public_rest) = Map.partition (\ptype -> ptype == PublicIn) $ publics leaks
    let (declassified_outs,declassified_ins) = Map.partition (\isBenign -> isBenign) $ declassifieds leaks
    let varsgr' = Gr.trc $ labfilter (\n -> not $ Set.member n $ Set.union (Map.keysSet public_ins) (Map.keysSet declassified_ins)) $ Gr.undir varsgr
    -- all variables connected to a declassified output may depend on a public output as well
    declassified_out_keys <- lift $ mapM labelGr (Map.keys declassified_outs)
    let declassified_outs' = Map.fromList $ concatMap (map ((,True) . fromJust . lab varsgr') . Gr.suc' . context varsgr') declassified_out_keys
    let leaks' = leaks { declassifieds = Map.unionWith (||) (declassifieds leaks) declassified_outs' }
    return leaks'

data PublicType = PublicIn | PublicMid | PublicOut
  deriving (Data,Typeable,Eq,Show)
  
instance Monoid PublicType where
    mempty = PublicIn
    mappend PublicIn y = y
    mappend x PublicIn = x
    mappend x PublicOut = PublicOut
    mappend PublicOut y = PublicOut
    mappend PublicMid PublicMid = PublicMid

hasLeakageAnn :: Data a => a -> Bool
hasLeakageAnn s = hasLeakName s || isJust (hasPublic s) || isJust (hasDeclassified s) || isJust (hasLeak s)

hasLeakageFunAnn :: Data a => a -> Bool
hasLeakageFunAnn s = hasLeakFunName s || isJust (hasPublic s) || isJust (hasDeclassified s) || isJust (hasLeak s)

isLeakFunName = isSubsequenceOf "Leakage"
isLeakVarName = isSubsequenceOf "Private"

hasLeakName x = hasLeakVarName x || hasLeakFunName x

hasLeakVarName :: Data a => a -> Bool
hasLeakVarName = everything (||) (mkQ False aux)
    where
    aux :: Id -> Bool
    aux n = isLeakVarName n

hasLeakFunName :: Data a => a -> Bool
hasLeakFunName = everything (||) (mkQ False aux)
    where
    aux :: BareExpression -> Bool
    aux (Application n _) = isLeakFunName n
    aux e = False

-- identifies a public annotation
hasPublic :: Data a => a -> Maybe (Map BareExpression PublicType)
hasPublic s = if Map.null m then Nothing else Just m
    where m = publicExprs s
    
hasPublicId :: Data a => a -> Maybe (Map Id PublicType)
hasPublicId s = if Map.null m then Nothing else Just m
    where m = publicIds s

hasPublicMid :: Data a => a -> Bool
hasPublicMid s = List.elem PublicMid (Map.elems m)
    where m = publicExprs s

publicExprs :: Data a => a -> Map BareExpression PublicType
publicExprs = everything (Map.unionWith mappend) (mkQ Map.empty aux)
    where
    aux = maybe Map.empty (uncurry Map.singleton) . isPublicExpr

publicIds :: Data a => a -> Map Id PublicType
publicIds = everything (Map.unionWith mappend) (mkQ Map.empty aux)
    where
    aux = maybe Map.empty (uncurry Map.singleton) . isPublicIdExpr

boxE :: BareExpression -> Maybe BareExpression
boxE (Application "$Box" [e]) = Just $ unPos e
boxE e = Nothing

isAnn :: Id -> BareExpression -> Maybe BareExpression
isAnn name (Application (isSuffixOf ("."++name) -> True) [_,unPos -> Var "$Heap",(boxE . unPos) -> Just e]) = Just e
isAnn _ e = Nothing

isPublicExpr :: BareExpression -> Maybe (BareExpression,PublicType)
isPublicExpr (isAnn "PublicIn" -> Just i) = Just (i,PublicIn)
isPublicExpr (isAnn "PublicOut" -> Just i) = Just (i,PublicOut)
isPublicExpr (isAnn "PublicMid" -> Just i) = Just (i,PublicMid)
isPublicExpr _ = Nothing

isPublicIdExpr :: BareExpression -> Maybe (Id,PublicType)
isPublicIdExpr (isPublicExpr -> Just (Var i,t)) = Just (i,t)
isPublicIdExpr e = Nothing

isLeakExpr :: BareExpression -> Maybe BareExpression
isLeakExpr (isAnn "Leak" -> Just i) = Just i
isLeakExpr _ = Nothing

isDeclassifiedExpr :: BareExpression -> Maybe (BareExpression,IsBenign)
isDeclassifiedExpr (isAnn "DeclassifiedIn" -> Just i) = Just (i,False)
isDeclassifiedExpr (isAnn "DeclassifiedOut" -> Just i) = Just (i,True)
isDeclassifiedExpr _ = Nothing

gReplaceCanCall :: Data a => a -> a
gReplaceCanCall = everywhere (mkT replaceCanCall)

replaceCanCall :: BareExpression -> BareExpression
replaceCanCall (isAnn "PublicIn#canCall" -> Just i) = tt
replaceCanCall (isAnn "PublicOut#canCall" -> Just i) = tt
replaceCanCall (isAnn "PublicMid#canCall" -> Just i) = tt
replaceCanCall (isAnn "Leak#canCall" -> Just i) = tt
replaceCanCall (isAnn "DeclassifiedIn#canCall" -> Just i) = tt
replaceCanCall (isAnn "DeclassifiedOut#canCall" -> Just i) = tt
replaceCanCall e = e

removeLeakageAnns :: Data a => a -> a
removeLeakageAnns = everywhere (mkT removeLeakageExpr)
    where
    removeLeakageExpr :: BareExpression -> BareExpression
    removeLeakageExpr (isPublicExpr -> Just _) = tt
    removeLeakageExpr (isLeakExpr -> Just _) = tt
    removeLeakageExpr (isDeclassifiedExpr -> Just _) = tt
    removeLeakageExpr e@(Application name@(isLeakFunName -> True) _) = tt
    removeLeakageExpr e@(hasLeakFunName -> True) = error $ "user-defined leakage functions not supported on non-dual mode: " ++ show (pretty e)
    removeLeakageExpr e = e

hasLeak :: Data a => a -> Maybe (Set BareExpression)
hasLeak s = if Set.null m then Nothing else Just m
    where m = leakExprs s

leakExprs :: Data a => a -> Set BareExpression
leakExprs = everything Set.union (mkQ Set.empty aux)
    where
    aux = maybe Set.empty (Set.singleton) . isLeakExpr

hasDeclassified :: Data a => a -> Maybe (Map BareExpression IsBenign)
hasDeclassified s = if Map.null m then Nothing else Just m
    where m = declassifiedExprs s

hasDeclassifiedOut :: Data a => a -> Bool
hasDeclassifiedOut s = List.elem True (Map.elems m)
    where m = declassifiedExprs s

declassifiedExprs :: Data a => a -> Map BareExpression IsBenign
declassifiedExprs = everything (Map.unionWith (||)) (mkQ Map.empty aux)
    where
    aux = maybe Map.empty (uncurry Map.singleton) . isDeclassifiedExpr

-- a program slice is benign if it uses at least one benign variable
isBenign :: FVS a => Leakage -> a -> IsBenign
isBenign leaks x = not (Set.null s)
    where
    s = Set.intersection (fvs x) (Map.keysSet $ Map.filter (\isBenign -> isBenign) $ declassifieds leaks)

class FVS a where
    fvs :: a -> Set Id

instance FVS a => FVS (Pos a) where
    fvs (Pos _ x) = fvs x
instance FVS [Expression] where
    fvs = mconcat . map fvs
instance FVS BareExpression where
    fvs (Literal {}) = Set.empty
    fvs (Var i) = Set.singleton i
    fvs (Logical {}) = Set.empty
    fvs (Application f es) = mconcat $ map fvs es
    fvs (MapSelection e es) = mconcat $ map fvs (e:es)
    fvs (MapUpdate e es e1) = mconcat $ map fvs (e:e1:es)
    fvs (Old e) = fvs e
    fvs (IfExpr e1 e2 e3) = mconcat $ map fvs [e1,e2,e2]
    fvs (Coercion e t) = fvs e
    fvs (UnaryExpression _ e) = fvs e
    fvs (BinaryExpression _ e1 e2) = mconcat $ map fvs [e1,e2]
    fvs (Quantified _ _ ids trggs e) = (fvs trggs `Set.union` fvs e) `Set.difference` (fvs $ map fst ids)
    
instance FVS [QTriggerAttribute] where
    fvs = mconcat . map fvs
instance FVS QTriggerAttribute where
    fvs (Left xs) = mconcat $ map fvs xs
    fvs (Right a) = fvs a
    
instance FVS [Id] where
    fvs = mconcat . map fvs
instance FVS Id where
    fvs = Set.singleton
instance FVS [WildcardExpression] where
    fvs = mconcat . map fvs
instance FVS WildcardExpression where
    fvs (Wildcard) = Set.empty
    fvs (Expr e) = fvs e
instance FVS [BasicBlock] where
    fvs = mconcat . map fvs
instance FVS BasicBlock where
    fvs (i,ss) = fvs i `Set.union` fvs ss
instance FVS [Statement] where
    fvs = mconcat . map fvs
instance FVS BareStatement where
    fvs (Predicate _ s) = fvs s
    fvs (Havoc ids) = Set.fromList ids
    fvs (Assign lhs rhs) = fvs lhs `Set.union` fvs rhs
    fvs (Call atts lhs _ es) = fvs atts `Set.union` fvs lhs `Set.union` fvs es
    fvs (CallForall _ es) = fvs es
    fvs (If e b1 b2) = fvs e `Set.union` fvs b1 `Set.union` fvs b2
    fvs (While e ss b) = fvs e `Set.union` fvs ss `Set.union` fvs b
    fvs (Break _) = Set.empty
    fvs Return = Set.empty
    fvs (Goto _) = Set.empty
    fvs Skip = Set.empty
instance FVS a => FVS (Maybe a) where
    fvs = maybe Set.empty fvs
instance FVS Block where
    fvs = mconcat . map fvs
instance FVS BareLStatement where
    fvs = fvs . snd
instance FVS [Attribute] where
    fvs = mconcat . map fvs
instance FVS Attribute where
    fvs (Attribute _ vs) = mconcat $ map fvs vs
instance FVS AttrValue where
    fvs (EAttr e) = fvs e
    fvs (SAttr s) = Set.empty
    
instance FVS SpecClause where
    fvs = fvs . specExpr
instance FVS [SpecClause] where
    fvs = mconcat . map fvs
    
programDefs :: Program -> Set Id
programDefs (Program decls) = mconcat $ map (declDefs . unPos) decls

declDefs :: BareDecl -> Set Id
declDefs (TypeDecl {}) = Set.empty
declDefs (ConstantDecl _ _ ids _ _ _) = Set.fromList ids
declDefs (FunctionDecl _ n _ _ _ _) = Set.singleton n
declDefs (AxiomDecl {}) = Set.empty
declDefs (VarDecl _ ids) = Set.fromList $ map itwId ids
declDefs (ProcedureDecl _ n _ _ _ _ _) = Set.singleton n
declDefs (ImplementationDecl _ n _ _ _ _) = Set.singleton n


globalVars :: Program -> ([Attribute],[IdTypeWhere])
globalVars = everything mappend (mkQ mempty aux)
    where
    aux :: BareDecl -> ([Attribute],[IdTypeWhere])
    aux (VarDecl atts itws) = (atts,itws)
    aux d = mempty






