{-# LANGUAGE GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.TypeChecker.Semantics

import Control.Monad
import Control.Monad.Except
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer
import Control.Monad.RWS as RWS

import Data.Bifunctor
import Data.Monoid
import Data.Maybe
import Data.Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data hiding (cast)
import qualified Data.Map as Map
import Data.Generics hiding (LT,GT,cast)

import Text.PrettyPrint as PP hiding (equals)

resolveTCstr :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTCstr l c = newErrorM $ resolveTCstr' l c

resolveTCstr' :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTCstr' l k@(TApp n args) =
    liftM fst $ matchTemplate l (Left n) args Nothing (checkTemplateType $ fmap (const l) n)
resolveTCstr' l k@(TDec n args) =
    liftM snd $ matchTemplate l (Left n) args Nothing (checkTemplateType $ fmap (const l) n)
resolveTCstr' l k@(PDec (Left n) args r) =
    liftM snd $ matchTemplate l (Right $ Left n) args (Just r) (checkProcedure $ fmap (const l) n)
resolveTCstr' l k@(PDec (Right o) args r) =
    liftM snd $ matchTemplate l (Right $ Right o) args (Just r) (checkOperator $ fmap (const l) o)
resolveTCstr' l k@(Coerces t1 t2) = do
    coerces l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr' l k@(Coerces2 t1 t2) = do
    t3 <- coerces2 l t1 t2
    addTemplateConstraint l k (Just t3)
    return t3
resolveTCstr' l k@(CoercesSec t1 t2 b) = do
    coercesSec l t1 t2 b
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr' l k@(Unifies t1 t2) = do
    unifies l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr' l k@(UnifiesExpr t1 t2) = do
    unifiesExpr l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr' l k@(SupportedPrint t) = do
    isSupportedPrint l t
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr' l k@(ProjectStruct t a) = do
    ret <- projectStructField l t a
    addTemplateConstraint l k (Just ret)
    return ret
resolveTCstr' l k@(ProjectMatrix t rs) = do
    ret <- projectMatrixType l t rs
    addTemplateConstraint l k (Just ret)
    return ret
resolveTCstr' l k@(IsReturnStmt cs ret dec) = do
    isReturnStmt l cs ret dec
    addTemplateConstraint l k (Just NoType)
    return NoType
--resolveTCstr l k@(Cast from to) = do
--    cast l from to
--    addTemplateConstraint l k (Just NoType)
--    return NoType
--resolveTCstr l err (InheritedCstr p k) = mapError err $ do
--    resolveTCstr (updpos l p) k `catchError` (\e -> tcError (locpos l) $ TemplateSolvingError e)
resolveTCstr' l (DelayedCstr k err) = do
    addErrorM err $ resolveTCstr' l k
--resolveTCstr l k@(GetCBase t) = do
--    ret <- getCBase l t
--    addTemplateConstraint l k (Just ret)
--    return ret
--resolveTCstr l k@(SetCBase t p) = do
--    ret <- setCBase l t p
--    addTemplateConstraint l k (Just ret)
--    return ret

tcProve :: (Vars loc,Location loc) => TcM loc a -> TcM loc (a,TDict loc)
tcProve m = do
    r <- Reader.ask
    s <- State.get
    (x,env',w') <- TcM $ lift $ runRWST (unTcM $ m >>= \x -> solve >> return x) r (s { tDict = (tDict s) { tCstrs = Map.filter isJust (tCstrs $ tDict s) } })
    State.modify $ \env -> env' { tDict = tDict env }
    Writer.tell w'
    return (x,tDict env')

prove :: (Vars loc,Location loc) => TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))
prove proof = try `catchError` (return . Left)
    where
    try = liftM Right $ tcProve proof

---- checks if two types are equal, without using coercions, not performing substitutions
--equals :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
--equals l (ProcType i1 _ _ _ _) (ProcType i2 _ _ _ _) | i1 == i2 = return ()
--equals l (StructType i1 _ _) (StructType i2 _ _) | i1 == i2 = return ()
----equals l (TK c1) (TK c2) = provesCstr mempty (\x y -> return $ mappend x y) equals (const ()) equals l c1 c2
--equals l (TK cstr) t2 = do
--    t1' <- resolveTK l cstr
--    tcCstrM l $ Equals t1' t2
--equals l t1 (TK cstr) = do
--    t2' <- resolveTK l cstr 
--    tcCstrM l $ Equals t1 t2'
--equals l (TpltType i1 _ _ _ _) (TpltType i2 _ _ _ _) | i1 == i2 = return ()
--equals l (TVar (VarName t1 n1)) (TVar (VarName t2 n2)) | n1 == n2 = do
--    tcCstrM l $ Equals t1 t2
--equals l t1@(TVar v1) t2 = do
--    t1' <- resolveTVar l v1 `mplus` constraintError EqualityException l (pp t1) (pp t2)
--    tcCstrM l $ Equals t1' t2
--equals l t1 t2@(TVar v2) = do
--    t2' <- resolveTVar l v2 `mplus` constraintError EqualityException l (pp t1) (pp t2)
--    tcCstrM l $ Equals t1 t2'
--equals l TType TType = return ()
--equals l KType KType = return ()
--equals l (DType i1) (DType i2) | i1 == i2 = return ()
--equals l Void Void = return ()
--equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
--equals l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
--    tcCstrM l $ Equals s1 s2
--    tcCstrM l $ Equals t1 t2
--    tcCstrM l $ EqualsExpr dim1 dim2
--    mapM_ (uncurry (tcCstrM l $ EqualsExpr)) =<< zipSizes l szs1 szs2
--equals l t1 t2@(CType {}) = do
--    let t1' = defCType t1
--    tcCstrM l $ Equals t1' t2
--equals l t1@(CType {}) t2 = do
--    let t2' = defCType t2
--    tcCstrM l $ Equals t1 t2'
--equals l (PrimType p1) (PrimType p2) = equalsPrim l p1 p2
--equals l Public Public = return ()
--equals l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
--equals l (SysPush t1) (SysPush t2) = tcCstrM l $ Equals t1 t2
--equals l (SysRet t1) (SysRet t2) = tcCstrM l $ Equals t1 t2
--equals l (SysRef t1) (SysRef t2) = tcCstrM l $ Equals t1 t2
--equals l (SysCRef t1) (SysCRef t2) = tcCstrM l $ Equals t1 t2
--equals l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
--equals l t1 t2 = constraintError EqualityException l (pp t1) (pp t2)
--
--equalsFoldable :: (Vars loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc ()
--equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)
--
--equalsList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
--equalsList l [] [] = return ()
--equalsList l (x:xs) (y:ys) = do
--    tcCstrM l $ Equals l x y
--    equalsList l xs ys
--equalsList l xs ys = constraintError EqualityException l (vcat $ map pp xs) (vcat $ map pp ys)

zipSizes :: (Vars loc,Location loc) => loc -> [Expression VarIdentifier Type] -> [Expression VarIdentifier Type] -> TcM loc [(Expression VarIdentifier Type,Expression VarIdentifier Type)]
zipSizes l [] [] = return []
zipSizes l [] (y:ys) = do
    x <- newSizeVar
    zs <- zipSizes l [] ys
    return ((x,y):zs)
zipSizes l (x:xs) [] = do
    y <- newSizeVar
    zs <- zipSizes l xs []
    return ((x,y):zs)
zipSizes l (x:xs) (y:ys) = do
    rs <- zipSizes l xs ys
    return ((x,y):rs)

equalsPrim :: Location loc => loc -> PrimitiveDatatype () -> PrimitiveDatatype () -> TcM loc ()
equalsPrim l p1 p2 | p1 == p2 = return ()
equalsPrim l (DatatypeInt _) (DatatypeInt64 _) = return ()
equalsPrim l (DatatypeInt64 _) (DatatypeInt _) = return ()
equalsPrim l (DatatypeUint _) (DatatypeUint64 _) = return ()
equalsPrim l (DatatypeUint64 _) (DatatypeUint _) = return ()
equalsPrim l (DatatypeXorUint _) (DatatypeXorUint64 _) = return ()
equalsPrim l (DatatypeXorUint64 _) (DatatypeXorUint _) = return ()
equalsPrim l (DatatypeFloat _) (DatatypeFloat32 _) = return ()
equalsPrim l (DatatypeFloat32 _) (DatatypeFloat _) = return ()
equalsPrim l t1 t2 = constraintError EqualityException l (pp t1) (pp t2) Nothing

equalsExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()
equalsExpr l e1 e2 = do
    v1 <- evalExpr $ fmap (Typed l) e1
    v2 <- evalExpr $ fmap (Typed l) e2
    let ce1' = fmap (const ()) e1
    let ce2' = fmap (const ()) e2
    unless (v1 == v2 || ce1' == ce2') $ constraintError EqualityException l (pp ce1') (pp ce2') Nothing

--provesFoldable :: (Location loc,Foldable t) => b -> (b -> b -> TcM loc b) -> (loc -> Type -> Type -> TcM loc b) -> loc -> t Type -> t Type -> TcM loc b
--provesFoldable z plus prove l t1 t2 = provesList z plus prove l (toList t1) (toList t2)
--
--provesList :: (Location loc) => b -> (b -> b -> TcM loc b) -> (loc -> Type -> Type -> TcM loc b) -> loc -> [Type] -> [Type] -> TcM loc b
--provesList z plus prove l [] [] = return z
--provesList z plus prove l (x:xs) (y:ys) = do
--    m1 <- prove l x y
--    m2 <- provesList z plus prove l xs ys
--    m1 `plus` m2
--provesList z plus prove l xs ys = constraintError EqualityException l (vcat $ map pp xs) (vcat $ map pp ys)

expandCTypeVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier Type -> TcM loc Type
expandCTypeVar l v = case loc v of
    BType -> return $ defCType (TVar v)
    TType -> do
        d <- newDomainTyVar Nothing
        t <- newBaseTyVar
        dim <- newDimVar
        let ct = CType d t dim []
        addSubstM l v ct
        return ct

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
coerces l (TyLit lit) t2 = coercesLit l lit t2 -- literals are never variables
coerces l (ProcType i1 _ _ _ _) (ProcType i2 _ _ _ _) | i1 == i2 = return ()
coerces l (StructType i1 _ _) (StructType i2 _ _) | i1 == i2 = return ()
coerces l (TK c1) t2 = do
    t1' <- resolveTK l c1
    tcCstrM_ l $ Coerces t1' t2
coerces l t1 (TK c2) = do
    t2' <- resolveTK l c2
    tcCstrM_ l $ Coerces t1 t2'
coerces l (TpltType i1 _ _ _ _) (TpltType i2 _ _ _ _) | i1 == i2 = return ()
coerces l TType TType = return ()
coerces l KType KType = return ()
coerces l (DType k1) (DType k2) | k1 == k2 = return ()
coerces l Void Void = return ()
coerces l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
coerces l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
    tcCstrM l $ Unifies t1 t2 -- we unify base types, no coercions here since it can't be a literal nor a security type
    tcCstrM l $ UnifiesExpr dim1 dim2
    unifiesSizes l dim1 szs1 dim2 szs2
    tcCstrM_ l $ CoercesSec s1 s2 ct2
coerces l t1@(TVar v1) t2@(CType {}) do
    mb <- tryResolveTVar l v1
    case mb of
        Just t1' -> tcCstrM_ l $ Coerces t1' t2
        Nothing -> do
                t1' <- expandCTypeVar l v1
                tcCstrM_ l $ Coerces t1' t2 
coerces l t1@(CType {}) t2@(TVar v2) = do
    mb <- tryResolveTVar l v2
    case mb of
        Just t2' -> tcCstrM_ l $ Coerces t1 t2'
        Nothing -> do
            t2' <- expandCTypeVar l v2
            tcCstrM_ l $ Coerces t1 t2'
coerces l t1@(CType {}) t2 = do
    let t2' = defCType t2
    tcCstrM_ l $ Coerces t1 t2'
coerces l t1 t2@(CType {}) = do
    let t1' = defCType t1
    tcCstrM_ l $ Coerces t1' t2
coerces l (PrimType p1) (PrimType p2) = equalsPrim l p1 p2
coerces l (SysPush t1) (SysPush t2) = tcCstrM_ l $ Coerces t1 t2
coerces l (SysRet t1) (SysRet t2) = tcCstrM_ l $ Coerces t1 t2
coerces l (SysRef t1) (SysRef t2) = tcCstrM_ l $ Coerces t1 t2
coerces l (SysCRef t1) (SysCRef t2) = tcCstrM_ l $ Coerces t1 t2
coerces l t1@(TVar v1) t2 = do
    mb <- tryResolveTVar l v1
    case mb of
        Just t1' -> tcCstrM_ l $ Coerces t1' t2
        Nothing -> do
            t1' <- expandCTypeVar l v1
            tcCstrM_ l $ Coerces t1' t2
coerces l t1 t2@(TVar v2) = do
    mb <- tryResolveTVar l v2
    case mb of
        Just t2' -> tcCstrM_ l $ Coerces t1 t2'
        Nothing -> case loc v2 of
            BType -> tcCstrM_ l $ Unifies t1 t2
            otherwise -> do
                t2' <- expandCTypeVar l v2
                tcCstrM_ l $ Coerces t1 t2'
coerces l Public Public = return ()
coerces l (Private k1 d1) (Private k2 d2) | d1 == d2 && k1 == k2 = return ()
coerces l t1 t2 = constraintError CoercionException l (pp t1) (pp t2) Nothing

coercesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
coercesList l [] [] = return ()
coercesList l (x:xs) (y:ys) = do
    tcCstrM l $ Coerces x y
    coercesList l xs ys
coercesList l xs ys = constraintError CoercionException l (vcat $ map pp xs) (vcat $ map pp ys) Nothing

-- | Non-directed coercion, with implicit security coercions.
-- Returns the unified type.
-- applies substitutions
coerces2 :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Type
coerces2 l t1 t2 = (coerces2 l t1 t2 >> return t2)
           `mplus` (coerces2 l t2 t1 >> return t1)

coercesSec :: (Vars loc,Location loc) => loc -> Type -> Type -> Type -> TcM loc ()
coercesSec l (TK c) s2 ct = do
    s1 <- resolveTK l c
    tcCstrM_ l $ CoercesSec s1 s2 ct
coercesSec l s1 (TK c) ct = do
    s2 <- resolveTK l c
    tcCstrM_ l $ CoercesSec s1 s2 ct 
coercesSec l Public Public ct = return ()
coercesSec l s1@Public (TVar v) ct = do
    s2 <- resolveTVar l v
    tcCstrM_ l $ CoercesSec s1 s2 ct
coercesSec l s1@(TVar v) s2@(Public) ct = tcCstrM_ l $ Unifies s1 s2
coercesSec l (Private d1 k1) (Private d2 k2) ct | d1 == d2 && k1 == k2 = return ()
coercesSec l s1@(Private d1 k1) s2@(TVar v) ct = tcCstrM_ l $ Unifies s1 s2
coercesSec l (TVar v) s2@(Private d2 k2) ct = do
    s1 <- resolveTVar l v
    tcCstrM_ l $ CoercesSec s1 s2 ct
coercesSec l s1@Public s2@(Private d2 k2) ct = do
    tcCstrM_ l $ PDec (Left $ ProcedureName () $ mkVarId "classify") [setCSec ct s1] (setCSec ct s2)
coercesSec l (TVar v) s2 ct = do
    s1 <- resolveTVar l v
    tcCstrM_ l $ CoercesSec s1 s2 ct
coercesSec l s1 (TVar v) ct = do
    s2 <- resolveTVar l v
    tcCstrM_ l $ CoercesSec s1 s2 ct
coercesSec l t1 t2 b = constraintError CoercionException l (pp t1) (pp t2) Nothing

-- | coerces a literal into a primitive type
coercesLit :: (Vars loc,Location loc) => loc -> Literal () -> Type -> TcM loc ()
coercesLit l lit t2@(TVar v) = do
    mb <- tryResolveTVar l v
    case mb of
        Just t -> tcCstrM_ l $ Coerces (TyLit lit) t
        Nothing -> do
            s <- newDomainTyVar Nothing
            d <- newDimVar
            t <- case lit of
                StringLit _ s -> return $ PrimType $ DatatypeString ()
                BoolLit _ b -> return $ PrimType $ DatatypeBool ()
                otherwise -> constraintError CoercionException l (pp lit) (pp t2) Nothing
            let ct = CType s t d []
            addSubstM l v ct         
coercesLit l lit (TK c) = do
    t <- resolveTK l c
    tcCstrM_ l $ Coerces (TyLit lit) t
coercesLit l lit ct@(CType s t d sz) = do -- to support the construction of constant arrays
    tcCstrM l $ Coerces (TyLit lit) t 
    tcCstrM_ l $ CoercesSec Public s ct -- since literals are always public values
coercesLit l (IntLit _ i1) (TyLit (IntLit _ i2)) | i1 <= i2 = return ()
coercesLit l (IntLit _ i) (PrimType t) | isPrimInt t || isPrimUint t = do
    let (min,max) = primIntBounds t
    unless (min <= i && i <= max) $ tcWarnM (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLit l (FloatLit _ f1) (TyLit (FloatLit _ f2)) | f1 <= f2 = return ()
coercesLit l (FloatLit _ f) (PrimType t) | isPrimFloat t = do
    let (min,max) = primFloatBounds t
    unless (min <= f && f <= max) $ tcWarnM (locpos l) $ LiteralOutOfRange (show f) (pp t) (show min) (show max)
coercesLit l (BoolLit _ b) (PrimType (DatatypeBool _)) = return ()
coercesLit l (StringLit _ s) (PrimType (DatatypeString _)) = return ()
coercesLit l l1 (TyLit l2) | l1 == l2 = return ()
coercesLit l l1 t2 = constraintError CoercionException l (pp l1) (pp t2) Nothing

-- | Checks if a type is more specific than another, performing substitutions
compares :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering
compares l t1@(TVar v1) t2@(TVar v2) = do
    mb1 <- tryResolveTVar l v1
    mb2 <- tryResolveTVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> addSubstM l v1 t2 >> return EQ
        (Just t1',Nothing) -> compares l t1' t2
        (Nothing,Just t2') -> compares l t1 t2'
        (Just t1',Just t2') -> compares l t1' t2'
compares l (TVar v1) t2 = provesTVar (return GT) compares l v1 t2
compares l t1 (TVar v2) = provesTVar (return LT) (\l x y -> compares l y x) l v2 t1
compares l (ProcType i1 _ _ _ _) (ProcType i2 _ _ _ _) | i1 == i2 = return EQ
compares l (StructType i1 _ _) (StructType i2 _ _) | i1 == i2 = return EQ
compares l (TpltType i1 _ _ _ _) (TpltType i2 _ _ _ _) | i1 == i2 = return EQ
compares l (TK c1) t2 = do
    t1' <- resolveTK l c1
    compares l t1' t2
compares l t1 (TK c2) = do
    t2' <- resolveTK l c2
    compares l t1 t2'
compares l TType TType = return EQ
compares l KType KType = return EQ
compares l (DType k1) (DType k2) | k1 == k2 = return EQ
compares l Void Void = return EQ
compares l (StmtType s1) (StmtType s2) | s1 == s2 = return EQ
compares l (TyLit lit1) (TyLit lit2) | lit1 == lit2 = return EQ
compares l (TyLit lit) t2 = do
    tcCstrM l $ Coerces (TyLit lit) t2
    return GT
compares l t1 (TyLit lit) = do
    tcCstrM l $ Coerces (TyLit lit) t1
    return LT
compares l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
    o1 <- compares l s1 s2
    o2 <- compares l t1 t2
    o3 <- comparesExpr l dim1 dim2
    os <- mapM (\(x,y) -> comparesExpr l x y) =<< zipSizes l szs1 szs2
    foldM (appendOrdering l (pp ct1) (pp ct2)) EQ (o1:o2:o3:os)
compares l t1@(CType {}) t2 = do
    let t2' = defCType t2
    compares l t1 t2'
compares l t1 t2@(CType {}) = do
    let t1' = defCType t1
    compares l t1' t2
compares l Public Public = return EQ
compares l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return EQ
compares l Public (Private {}) = return LT -- public computations are preferrable
compares l (SysPush t1) (SysPush t2) = do
    compares l t1 t2
compares l (SysRet t1) (SysRet t2) = do
    compares l t1 t2
compares l (SysRef t1) (SysRef t2) = do
    compares l t1 t2
compares l (SysCRef t1) (SysCRef t2) = do
    compares l t1 t2
compares l (PrimType p1) (PrimType p2) = equalsPrim l p1 p2 >> return EQ
compares l t1 t2 = constraintError ComparisonException l (pp t1) (pp t2) Nothing
    
comparesFoldable :: (Vars loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc Ordering
comparesFoldable l xs ys = comparesList l (toList xs) (toList ys)

comparesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering
comparesList l [] [] = return EQ
comparesList l a@(x:xs) b@(y:ys) = do
    f <- compares l x y
    g <- comparesList l xs ys
    appendOrdering l (vcat $ map pp a) (vcat $ map pp b) f g
comparesList l xs ys = constraintError ComparisonException l (vcat $ map pp xs) (vcat $ map pp ys) Nothing
    
appendOrdering :: Location loc => loc -> Doc -> Doc -> Ordering -> Ordering -> TcM loc Ordering
appendOrdering l a b EQ y = return y
appendOrdering l a b x EQ = return x
appendOrdering l a b LT LT = return LT
appendOrdering l a b GT GT = return GT
appendOrdering l a b x y = constraintError ComparisonException l a b Nothing

-- | Non-directed unification, without implicit security coercions.
-- applies substitutions
unifies :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
unifies l t1@(ProcType i1 _ _ _ _) (ProcType i2 _ _ _ _) | i1 == i2 = return ()
unifies l t1@(StructType i1 _ _) (StructType i2 _ _) | i1 == i2 = return ()
unifies l (TK c1) t2 = do
    t1' <- resolveTK l c1
    tcCstrM_ l $ Unifies t1' t2
unifies l t1 (TK c2) = do
    t2' <- resolveTK l c2
    tcCstrM_ l $ Unifies t1 t2'
unifies l t1@(TpltType i1 _ _ _ _) (TpltType i2 _ _ _ _) | i1 == i2 = return ()
unifies l t1@TType TType = return ()
unifies l t2@KType KType = return ()
unifies l t1@(DType k1) (DType k2) | k1 == k2 = return ()
unifies l t1@Void Void = return ()
unifies l t1@(StmtType s1) (StmtType s2) | s1 == s2 = return ()
unifies l (TyLit lit) t2 = tcCstrM_ l $ Coerces (TyLit lit) t2 -- literals are never variables
unifies l t1 (TyLit lit) = tcCstrM_ l $ Unifies (TyLit lit) t1 -- literals are never variables
unifies l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
    tcCstrM_ l $ Unifies s1 s2
    tcCstrM_ l $ Unifies t1 t2
    tcCstrM_ l $ UnifiesExpr dim1 dim2
    unifiesSizes l dim1 szs1 dim2 szs2
unifies l t1@(CType {}) t2 = do
    let t2' = defCType t2
    tcCstrM_ l $ Unifies t1 t2'
unifies l t1 t2@(CType {}) = do
    let t1' = defCType t1
    tcCstrM_ l $ Unifies t1' t2
unifies l t1@(TVar v1) t2 = provesTVar (return ()) unifies l v1 t2
unifies l t1 t2@(TVar v2) = provesTVar (return ()) unifies l v2 t1
unifies l t1@(PrimType p1) (PrimType p2) = equalsPrim l p1 p2
unifies l (SysPush t1) (SysPush t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifies l (SysRet t1) (SysRet t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifies l (SysRef t1) (SysRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifies l (SysCRef t1) (SysCRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifies l t1@Public Public = return ()
unifies l t1@(Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
unifies l t1 t2 = constraintError UnificationException l (pp t1) (pp t2) Nothing

unifiesSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()
unifiesSizes l dim1 szs1 dim2 szs2 = do
    mapM_ (\(x,y) -> tcCstrM l $ UnifiesExpr x y) =<< zipSizes l szs1 szs2

unifiesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError UnificationException l (vcat $ map pp xs) (vcat $ map pp ys) Nothing

-- | Tries to resolve a constraint inside a proof
resolveTK :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTK l cstr = resolveTCstr l cstr

resolveTVar :: Location loc => loc -> VarName VarIdentifier Type -> TcM loc Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> do
            ss <- liftM ppSubstsGeneric getSubstsGeneric
            tcError (locpos l) $ UnresolvedVariable (pp v) ss
        Just t -> return t

provesTVar :: Location loc => TcM loc b -> (loc -> Type -> Type -> TcM loc b) -> loc -> VarName VarIdentifier Type -> Type -> TcM loc b
provesTVar z go l v1 t2 = do
    mb <- tryResolveTVar l v1
    case mb of
        Nothing -> addSubstM l v1 t2 >> z
        Just t1' -> go l t1' t2

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: Location loc => loc -> VarName VarIdentifier Type -> TcM loc (Maybe Type)
tryResolveTVar l v = do
    -- lookup in the substitution environment
    s <- liftM (tSubsts . tDict) State.get
    let mb = substsFromMap s $ fmap (const ()) v
    return $ mb

-- throws a constraint
tcCstrM :: Location loc => loc -> TCstr -> TcM loc Type
tcCstrM l k = do
    err <- askErrorM
    addTemplateConstraint l k Nothing
    return $ TK $ DelayedCstr k err

tcTopCstrM :: Location loc => loc -> TCstr -> TcM loc Type
tcTopCstrM l k = do
    addErrorM (topCstrErr (locpos l) k) $ tcCstrM l k

-- | error-handling for a top-level delayed constraint
topCstrErr :: Position -> TCstr -> SecrecError -> SecrecError
topCstrErr p (Unifies t1 t2) err = TypecheckerError p $ UnificationException (pp t1) (pp t2) $ Right err
topCstrErr p (Coerces t1 t2) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (Coerces2 t1 t2) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (PDec {}) err = err
topCstrErr p (TApp {}) err = err
topCstrErr p (TDec {}) err = err
topCstrErr p t err = error $ "topCstrErr does not support" ++ ppr t

tcCstrM_ :: Location loc => loc -> TCstr -> TcM loc ()
tcCstrM_ l c = tcCstrM l c >> return ()

--cast :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Type
--cast l from to = do
--    case from of
--        TyLit lit -> resolveTCstr l $ Coerces (TyLit lit) to
--        otherwise -> resolveTCstr l $ PDec (Right $ OpCast ()) [from] to

-- base of a compound type
--getCBase :: (Vars loc,Location loc) => loc -> Type -> TcM loc Type
--getCBase l (CType _ t _ _) = return t
--getCBase l (TVar v) = do
--    mb <- tryResolveTVar l v
--    case mb of
--        Just t -> getCBase l t
--        Nothing -> do
--            ct <- expandCTypeVar l v
--            getCBase l ct
--getCBase l (TK c) = do
--    t <- resolveTK l c
--    getCBase l t
--getCBase l ct = genericError (locpos l) $ "Not a complex type " ++ ppr ct
--
--setCBase :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Type
--setCBase l (CType s t d sz) b = return $ CType s b d sz
--setCBase l ct@(TVar v) b = do
--    mb <- tryResolveTVar l v
--    case mb of
--        Just t -> setCBase l t b
--        Nothing -> do
--            s <- newDomainTyVar Nothing
--            d <- newDimVar
--            let ct = CType s b d []
--            addSubstM l v ct
--            return ct
--setCBase l (TK c) b = do
--    t <- resolveTK l c
--    setCBase l t b
--setCBase l ct b = genericError (locpos l) $ "Not a complex type " ++ ppr ct

setCSec (CType _ t d sz) s = CType s t d sz

--mapTypeBase :: (Vars loc,Location loc) => loc -> Type -> (Type -> TcM loc (Type,b)) -> TcM loc (Type,b)
--mapTypeBase l (CType s b d sz) f = do
--    (b',r) <- f b
--    return (CType s b' d sz,r)
--mapTypeBase l (TK c) f = do
--    t <- resolveTCstr l c
--    mapTypeBase l t f
--mapTypeBase l t@(TVar v) f = do
--    mb <- tryResolveTVar l v
--    case mb of
--        Nothing -> genericError (locpos l) $ "Unknown base type for " ++ ppr t
--        Just x -> mapTypeBase l x f
--mapTypeBase l t f = f t

isSupportedPrint :: (Vars loc,Location loc) => loc -> [Type] -> TcM loc ()
isSupportedPrint l ts = do
    forM_ ts $ \t -> resolveTCstr l (PDec (Left $ ProcedureName () (mkVarId "tostring")) [t] string)

-- | solves all constraints in the environment
solve :: (Vars loc,Location loc) => TcM loc ()
solve = do
--    ss <- liftM (tUnsolved . tDict) State.get
--    liftIO $ putStrLn $ "solve [" ++ show (vcat $ map pp ss) ++ "\n]"
    solveCstrs

solveCstrs :: (Vars loc,Location loc) => TcM loc ()
solveCstrs = do
    cstrs <- liftM (tUnsolved . tDict) State.get
    case cstrs of
        [] -> return ()
        otherwise -> do
            (go,_) <- trySolveSomeCstrs cstrs
            if go
                then solveCstrs -- new substitions have been found, try again
                else do
                    solveAllCstrs -- nothing has progressed, solve once and for all

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (Vars loc,Location loc) => [Loc loc TCstr] -> TcM loc (Bool,[Loc loc TCstr])
trySolveSomeCstrs = foldrM solveBound (False,[])
    where
    solveBound x@(Loc l c) (b,xs) = do
        ok <- trySolveCstr x
        if ok
            then do
                return (ok,xs)
            else return (b,x:xs)

-- | solves all constraints
solveAllCstrs :: (Vars loc,Location loc) => TcM loc ()
solveAllCstrs = do
    cstrs <- liftM (tUnsolved . tDict) State.get
--    ss <- liftM ppSubstsGeneric getSubstsGeneric
--    liftIO $ putStrLn $ "solveAll {" ++ show (vcat $ map pp cstrs) ++ "\n}\n" ++ show ss
    mapM_ solveCstr cstrs

trySolveCstr :: (Vars loc,Location loc) => Loc loc TCstr -> TcM loc Bool
trySolveCstr c = (solveCstr c {- >>= \ret -> liftIO (putStrLn $ "solved " ++ ppr c ++ " --> " ++ ppr ret) -} >> return True) `mplus` return False

solveCstr :: (Vars loc,Location loc) => Loc loc TCstr -> TcM loc ()
solveCstr (Loc l c) = do
    t <- resolveTCstr l c
    addTemplateConstraint l c (Just t)

isReturnStmt :: (Vars loc,Location loc) => loc -> Set StmtClass -> Type -> ProcedureDeclaration VarIdentifier Position -> TcM loc ()
isReturnStmt l cs ret dec = aux $ Set.toList cs
    where
    aux [StmtReturn] = return ()
    aux c = mapError (\err -> TypecheckerError (locpos l) $ NoReturnStatement $ pp dec) (resolveTCstr l (Unifies Void ret) >> return ())

unifiesExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()
unifiesExpr l (RVariablePExpr _ v1) e2 = provesEVar (return ()) unifiesExpr l v1 e2
unifiesExpr l e1 (RVariablePExpr _ v2) = provesEVar (return ()) unifiesExpr l v2 e1
unifiesExpr l e1 e2 = equalsExpr l e1 e2
    
comparesExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc Ordering
comparesExpr l e1@(RVariablePExpr _ v1@(VarName _ n)) e2@(RVariablePExpr _ v2) = do
    mb1 <- tryResolveEVar l (fmap (Typed l) v1)
    mb2 <- tryResolveEVar l (fmap (Typed l) v2)
    case (mb1,mb2) of
        (Nothing,Nothing) -> addValueM l (fmap (Typed l) v1) (fmap (Typed l) e2) >> return EQ
        (Just e1',Nothing) -> comparesExpr l (fmap typed e1') e2
        (Nothing,Just e2') -> comparesExpr l e1 (fmap typed e2')
        (Just e1',Just e2') -> comparesExpr l (fmap typed e1') (fmap typed e2')
comparesExpr l (RVariablePExpr _ v1) e2 = provesEVar (return GT) comparesExpr l v1 e2
comparesExpr l e1 (RVariablePExpr _ v2) = provesEVar (return LT) (\l x y -> comparesExpr l y x) l v2 e1
comparesExpr l e1 e2 = equalsExpr l e1 e2 >> return EQ
    
constraintError :: Location loc => (Doc -> Doc -> Either Doc SecrecError -> TypecheckerErr) -> loc -> Doc -> Doc -> Maybe SecrecError -> TcM loc a
constraintError k l e1 e2 (Just suberr) = do
    tcError (locpos l) $ k e1 e2 $ Right suberr
constraintError k l e1 e2 Nothing = do
    ss <- liftM ppSubstsGeneric getSubstsGeneric
    tcError (locpos l) $ k e1 e2 $ Left ss
    
provesEVar :: (Vars loc,Location loc) => TcM loc b -> (loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc b) -> loc -> VarName VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc b
provesEVar z go l v1@(VarName t n) e2 = do
    mb <- tryResolveEVar l (fmap (Typed l) v1)
    case mb of
        Nothing -> addValueM l (fmap (Typed l) v1) (fmap (Typed l) e2) >> z
        Just e1' -> go l (fmap typed e1') e2


