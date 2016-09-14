{-# LANGUAGE ViewPatterns, FlexibleInstances #-}

module Language.Boogie.Transformation.Simplify where

import Language.Boogie.Util
import Language.Boogie.Exts
import Language.Boogie.AST
import Language.Boogie.Position
import Language.Boogie.PrettyAST
import Language.Boogie.Pretty
import Language.Boogie.BasicBlocks
import Language.Boogie.Analysis.Leakage

import Control.Monad.Identity

import Data.Maybe
import Data.Monoid
import Data.Generics
import qualified Data.Set as Set

runSimplify :: Simplify a => a -> a
runSimplify x = runIdentity (simplifyId x)

type SimplifyM = Identity

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
    simplify (Program decls) = liftM (fmap Program) (simplify decls)

instance Simplify BareExpression where
    simplify = return . Just

instance Simplify [Id] where
    simplify = simplifyList

instance Simplify [Decl] where
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
    simplify (Requires free e) = liftM (fmap (Requires free)) $ simplifyAs posTT e
    simplify (Modifies free []) = return Nothing
    simplify c@(Modifies _ _) = return $ Just c
    simplify (Ensures free e) = liftM (fmap (Ensures free)) $ simplifyAs posTT e

instance Simplify BareDecl where
    simplify (AxiomDecl atts e) = do
        atts' <- simplifyMonoid atts
        liftM (fmap (AxiomDecl atts')) $ simplifyAs posTT e
    simplify (ProcedureDecl atts n targs args rets cstrs b) = do
        atts' <- simplifyMonoid atts
        targs' <- simplifyMonoid targs
        args' <- simplifyMonoid args
        rets' <- simplifyMonoid rets
        cstrs' <- simplifyMonoid cstrs
        b' <- simplifyMonoid b
        return $ Just $ ProcedureDecl atts' n targs' args' rets' cstrs' b'
    simplify (ImplementationDecl atts name targs args rets b) = do
        atts' <- simplifyMonoid atts
        targs' <- simplifyMonoid targs
        args' <- simplifyMonoid args
        rets' <- simplifyMonoid rets
        b' <- simplifyMonoid b
        return $ Just $ ImplementationDecl atts' name targs' args' rets' b'
    simplify d = return $ Just d

instance Simplify SpecClause where
    simplify (SpecClause t isAssume e) = liftM (fmap (SpecClause t isAssume)) $ simplifyAs posTT e

instance Simplify BareStatement where
    simplify (Predicate atts spec) = liftM (fmap (Predicate atts)) $ simplify spec
    simplify s = return $ Just s

cleanAttributes :: Maybe [Id] -> [AttrValue] -> [AttrValue]
cleanAttributes vars = concatMap (cleanAttribute vars)

cleanTriggers :: Maybe [Id] -> [Trigger] -> [Trigger]
cleanTriggers vars = catMaybes . map (cleanTrigger vars)

cleanAttribute :: Maybe [Id] -> AttrValue -> [AttrValue]
cleanAttribute vars (SAttr x) = [SAttr x]
cleanAttribute vars (EAttr x) = map EAttr $ cleanExpression x

cleanTrigger :: Maybe [Id] -> Trigger -> Maybe Trigger
cleanTrigger vars t = let t' = concatMap cleanExpression t in case vars of
    Nothing -> Just t'
    Just ids -> if Set.isSubsetOf (Set.fromList ids) (fvs t') then Just t' else Nothing

cleanExpression :: Expression -> [Expression]
cleanExpression (Pos p e) = cleanBareExpression p e

cleanBareExpression :: SourcePos -> BareExpression -> [Expression]
cleanBareExpression p (BinaryExpression _ e1 e2) = cleanExpression e1 ++ cleanExpression e2
cleanBareExpression p e = [Pos p e]



    
