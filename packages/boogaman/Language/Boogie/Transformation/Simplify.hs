{-# LANGUAGE ConstrainedClassMethods, ViewPatterns, FlexibleInstances #-}

module Language.Boogie.Transformation.Simplify where

import Language.Boogie.Util
import Language.Boogie.Exts
import Language.Boogie.AST
import Language.Boogie.Position
import Language.Boogie.PrettyAST
import Language.Boogie.Pretty
import Language.Boogie.BasicBlocks
import Language.Boogie.Analysis.Leakage
import Language.Boogie.Analysis.Annotation
import Language.Boogie.Options hiding (simplify)

import Control.Monad.Identity
import Control.Monad.Reader (Reader(..))
import qualified Control.Monad.Reader as Reader

import Data.Maybe
import Data.Monoid
import Data.Generics
import Data.List as List
import qualified Data.Set as Set

runSimplify :: Simplify a => Options -> a -> a
runSimplify opts x = Reader.runReader (simplifyId x) opts

type SimplifyM = Reader Options

class Simplify a where
    simplify :: a -> SimplifyM (Maybe a)
    
    simplifyId :: a -> SimplifyM a
    simplifyId x = liftM (maybe x id) (simplify x)
    
    simplifyMonoid :: Monoid a => a -> SimplifyM a
    simplifyMonoid x = liftM (maybe mempty id) (simplify x)
    
    simplifyList :: [a] -> SimplifyM (Maybe [a])
    simplifyList xs = do
        xs' <- liftM catMaybes $ mapM simplify xs
        if null xs' then return Nothing else return (Just xs')

instance Simplify Id where
    simplify = return . Just

instance Simplify IdTypeWhere where
    simplify (IdTypeWhere i t e) = do
        t' <- simplifyId t
        e' <- simplifyId e
        return $ Just $ IdTypeWhere i t' e'

instance Simplify (GenType id) where
    simplify = return . Just

instance Simplify a => Simplify (Maybe a) where
    simplify Nothing = return Nothing
    simplify (Just x) = do
        mb <- simplify x
        case mb of
            Nothing -> return Nothing
            Just x' -> return $ Just $ Just x'

instance Simplify a => Simplify (Pos a) where
    simplify (Pos p x) = liftM (fmap (Pos p)) (simplify x)

instance Simplify Program where
    simplify (Program decls) = do
        decls' <- simplifyDecls decls
        return $ Just $ Program decls'
      where
        simplifyDecls [] = return []
        simplifyDecls (Left c:ys@(Right (Pos _ d):xs)) = case (bareDeclName d) of
            Nothing -> do
                ys' <- simplifyDecls ys
                return (Left c : ys')
            Just n -> if List.elem c (dafnyAxioms n)
                then simplifyDecls xs
                else do
                    ys' <- simplifyDecls ys
                    return (Left c : ys')
        simplifyDecls (Left c:xs) = do
            xs' <- simplifyDecls xs
            return $ Left c : xs'
        simplifyDecls (Right d:xs) = do
            d' <- simplifyId d
            xs' <- simplifyDecls xs
            return (Right d':xs')   

instance Simplify BareExpression where
    simplify e = liftM Just $ simplifyBareExpr e

simplifyBareExpr :: BareExpression -> SimplifyM BareExpression
simplifyBareExpr (Logical t r) = do
    t' <- simplifyId t
    return $ Logical t' r
simplifyBareExpr (MapSelection e es) = do
    e' <- simplifyId e
    es' <- simplifyId es
    return $ MapSelection e' es'
simplifyBareExpr (MapUpdate e1 es e2) = do
    e1' <- simplifyId e1
    es' <- simplifyId es
    e2' <- simplifyId e2
    return $ MapUpdate e1' es' e2'
simplifyBareExpr (Old e) = do
    e' <- simplifyId e
    return $ Old e'
simplifyBareExpr (IfExpr c e1 e2) = do
    c' <- simplifyId c
    case unPos c of
        Literal (BoolValue True) -> simplifyId $ unPos e1
        Literal (BoolValue False) -> simplifyId $ unPos e2
        otherwise -> do
            e1' <- simplifyId e1
            e2' <- simplifyId e2
            return $ IfExpr c' e1' e2'
simplifyBareExpr (Coercion e t) = do
    e' <- simplifyId e
    t' <- simplifyId t
    return $ Coercion e' t'
simplifyBareExpr (Quantified q ids idts trgs e) = do
    e' <- simplifyId e
    case unPos e' of
        Literal (BoolValue b) -> return $ unPos e'
        otherwise -> do
            let vs = fvs e'
            let ids' = filter (`Set.member` vs) ids
            let idts' = filter (\(i,t) -> Set.member i vs) idts
            let trgs' = cleanQTriggerAttributes (Just $ Set.toList vs) trgs
            return $ Quantified q ids' idts' trgs' e'
simplifyBareExpr (BinaryExpression o e1 e2) = do
    e1' <- simplifyId e1
    e2' <- simplifyId e2
    return $ evalBinOp o e1' e2'
simplifyBareExpr (UnaryExpression o e) = do
    e' <- simplifyId e
    return $ evalUnOp o e'
simplifyBareExpr app@(Application n es) = do
    opts <- Reader.ask
    case replaceCanCallMb opts app of
        Just e' -> return e'
        Nothing -> do
            es' <- mapM simplifyId es
            return $ Application n es'
simplifyBareExpr e = return e

evalUnOp :: UnOp -> Expression -> BareExpression
evalUnOp o e = UnaryExpression o e

evalBinOp :: BinOp -> Expression -> Expression -> BareExpression
evalBinOp Implies e1 e2@(unPos -> Literal (BoolValue True)) = unPos e2
evalBinOp b e1 e2 = BinaryExpression b e1 e2

instance Simplify (Id, [[Expression]]) where
    simplify (a,b) = do
        mba' <- simplify a
        mbb' <- simplifyList b
        case (mba',mbb') of
            (Nothing,Nothing) -> return Nothing
            otherwise -> return $ Just (maybe a id mba',maybe b id mbb')

instance Simplify [Id] where
    simplify = simplifyList

instance Simplify [Decl] where
    simplify = simplifyList
    
instance Simplify [Expression] where
    simplify = simplifyList

instance Simplify [Body] where
    simplify = simplifyList

instance Simplify [IdType] where
    simplify = simplifyList

instance Simplify [[IdTypeWhere]] where
    simplify = simplifyList

instance Simplify [IdTypeWhere] where
    simplify = simplifyList

instance Simplify [Statement] where
    simplify = simplifyList

instance Simplify [Either Comment Statement] where
    simplify = simplifyList

instance Simplify (Either Comment Statement) where
    simplify (Left c) = return $ Just $ Left c
    simplify (Right s) = do
        s' <- simplify s
        return $ fmap Right s'

instance Simplify BasicBlock where
    simplify (x,y) = do
        mbx <- simplify x
        mby <- simplify y
        case (mbx,mby) of
            (Nothing,Nothing) -> return Nothing
            (Just x',Nothing) -> return $ Just (x',[])
            (Nothing,Just y') -> return $ Just (x,y')
            (Just x',Just y') -> return $ Just (x',y')

instance Simplify Block where
    simplify bs = do
        let bbs = toBasicBlocks bs
        bbs' <- simplifyList bbs
        return $ fmap fromBasicBlocks bbs'

instance Simplify [Contract] where
    simplify = simplifyList

instance Simplify [SpecClause] where
    simplify = simplifyList

instance Simplify WildcardExpression where
    simplify Wildcard = return $ Just Wildcard
    simplify (Expr e) = liftM (fmap Expr) $ simplify e
    
instance Simplify [Attribute] where
    simplify = simplifyList
    
instance Simplify [([Attribute], [IdTypeWhere])] where
    simplify = simplifyList
    
instance Simplify ([Attribute], [IdTypeWhere]) where
    simplify (x,y) = do
        x' <- simplifyMonoid x
        y' <- simplifyMonoid y
        if null x' && null y' then return Nothing else return $ Just (x',y')
    
instance Simplify Attribute where
    simplify (Attribute tag vals) = liftM (fmap (Attribute tag)) $ simplifyList vals
instance Simplify AttrValue where
    simplify (EAttr e) = liftM (fmap EAttr) $ simplify e
    simplify (SAttr s) = return $ Just $ SAttr s
    
instance Simplify ([([Attribute],[IdTypeWhere])], Block) where
    simplify (x,y) = do
        mbx <- simplify x
        mby <- simplify y
        case (mbx,mby) of
            (Nothing,Nothing) -> return Nothing
            (Just x',Just y') -> return $ Just (x',y')
            (Just x',Nothing) -> return $ Just (x',[])
            (Nothing,Just y') -> return $ Just ([],y')
    
instance Simplify ([Id],Statement) where
    simplify (x,y) = do
        mbx <- simplify x
        mby <- simplify y
        case (mbx,mby) of
            (Nothing,Nothing) -> return Nothing
            (Just x',Just y') -> return $ Just (x',y')
            (Just x',Nothing) -> return $ Just (x',Pos noPos Skip)
            (Nothing,Just y') -> return $ Just ([],y')

instance Simplify IdType where
    simplify (x,y) = do
        x' <- simplifyId x
        y' <- simplifyId y
        return $ Just (x',y')

simplifyAs :: (Eq a,Simplify a) => a -> a -> SimplifyM (Maybe a)
simplifyAs empty x = do
    mb <- simplify x
    case mb of
        Just ((==empty)->True) -> return Nothing
        otherwise -> return mb

instance Simplify Contract where
    simplify c = Reader.ask >>= \opts -> simplify' opts c
      where
        simplify' opts (Requires _ (Pos p (isFreeExpr opts -> Just e))) = do
            liftM (fmap (Requires True)) $ simplifyAs posTT (Pos p e)
        simplify' opts (Ensures _ (Pos p (isFreeExpr opts -> Just e))) = do
            liftM (fmap (Ensures True)) $ simplifyAs posTT (Pos p e)
        simplify' opts (Requires free e) = liftM (fmap (Requires free)) $ simplifyAs posTT e
        simplify' opts (Modifies free []) = return Nothing
        simplify' opts c@(Modifies _ _) = return $ Just c
        simplify' opts (Ensures free e) = liftM (fmap (Ensures free)) $ simplifyAs posTT e

instance Simplify BareDecl where
    simplify d = do
        opts <- Reader.ask
        case (bareDeclName d,vcgen opts) of
            (Just n,Dafny) -> if List.elem n dafnyAnns
                then return Nothing
                else simplify' d
            otherwise -> simplify' d
      where
        simplify' (AxiomDecl atts e) = do
            atts' <- simplifyMonoid atts
            liftM (fmap (AxiomDecl atts')) $ simplifyAs posTT e
        simplify' (ProcedureDecl atts n targs args rets cstrs b) = do
            atts' <- simplifyMonoid atts
            targs' <- simplifyMonoid targs
            args' <- simplifyMonoid args
            rets' <- simplifyMonoid rets
            cstrs' <- simplifyMonoid cstrs
            b' <- simplifyMonoid b
            return $ Just $ ProcedureDecl atts' n targs' args' rets' cstrs' b'
        simplify' (ImplementationDecl atts name targs args rets b) = do
            atts' <- simplifyMonoid atts
            targs' <- simplifyMonoid targs
            args' <- simplifyMonoid args
            rets' <- simplifyMonoid rets
            b' <- simplifyMonoid b
            return $ Just $ ImplementationDecl atts' name targs' args' rets' b'
        simplify' d = return $ Just d

instance Simplify SpecClause where
    simplify e = do
        opts <- Reader.ask
        simplify' opts e
      where
        simplify' opts (SpecClause t isAssume (Pos p (isFreeExpr opts -> Just e))) = do
            simplify' opts (SpecClause t True (Pos p e))
        simplify' opts (SpecClause t isAssume e) = liftM (fmap (SpecClause t isAssume)) $ simplifyAs posTT e

instance Simplify BareStatement where
    simplify (Predicate atts spec) = do
        opts <- Reader.ask
        atts' <- simplifyId atts
        spec'@(SpecClause st' isAssume' (Pos l' e')) <- simplifyId spec
        case isLeakageExpr opts e' of
            Just e'' -> return $ Just $ Predicate (atts'++[leakageAtt]) (SpecClause st' isAssume' $ Pos l' e'')
            Nothing -> return $ Just $ Predicate atts' spec'
    simplify (Assign lhs rhs) = do
        lhs' <- mapM simplifyId lhs
        rhs' <- mapM simplifyId rhs
        return $ Just $ Assign lhs' rhs'
    simplify (Call atts lhs n es) = do
        atts' <- simplifyId atts
        lhs' <- simplifyId lhs
        es' <- mapM simplifyId es
        return $ Just $ Call atts' lhs' n es'
    simplify (CallForall  n es) = do
        es' <- mapM simplifyId es
        return $ Just $ CallForall n es'
    simplify (If e th el) = do
        e' <- simplifyId e
        th' <- simplifyId th
        el' <- mapM simplifyId el
        return $ Just $ If e' th' el'
    simplify (While e c b) = do
        e' <- simplifyId e
        c' <- simplifyId c
        b' <- simplifyId b
        return $ Just $ While e' c' b'
    simplify s = return $ Just s

cleanQTriggerAttributes :: Maybe [Id] -> [QTriggerAttribute] -> [QTriggerAttribute]
cleanQTriggerAttributes vars xs = map (cleanQTriggerAttribute vars) xs

cleanQTriggerAttribute :: Maybe [Id] -> QTriggerAttribute -> QTriggerAttribute
cleanQTriggerAttribute vars (Left t) = case cleanTrigger vars t of
    Nothing -> Left []
    Just xs -> Left xs
cleanQTriggerAttribute vars (Right a) = Right $ cleanAttribute vars a

cleanAttrVals :: Maybe [Id] -> [AttrValue] -> [AttrValue]
cleanAttrVals vars = concatMap (cleanAttrVal vars)

cleanTriggers :: Maybe [Id] -> [Trigger] -> [Trigger]
cleanTriggers vars = catMaybes . map (cleanTrigger vars)

cleanAttrVal :: Maybe [Id] -> AttrValue -> [AttrValue]
cleanAttrVal vars (SAttr x) = [SAttr x]
cleanAttrVal vars (EAttr x) = map EAttr $ cleanExpression x

cleanAttribute :: Maybe [Id] -> Attribute -> Attribute
cleanAttribute vars (Attribute i vs) = Attribute i $ cleanAttrVals vars vs

cleanTrigger :: Maybe [Id] -> Trigger -> Maybe Trigger
cleanTrigger vars t = let t' = concatMap cleanExpression t in case vars of
    Nothing -> Just t'
    Just ids -> if Set.isSubsetOf (Set.fromList ids) (fvs t') then Just t' else Nothing

cleanExpression :: Expression -> [Expression]
cleanExpression (Pos p e) = cleanBareExpression p e

cleanBareExpression :: SourcePos -> BareExpression -> [Expression]
cleanBareExpression p (BinaryExpression _ e1 e2) = cleanExpression e1 ++ cleanExpression e2
cleanBareExpression p e = [Pos p e]



    
