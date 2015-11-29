{-# LANGUAGE GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.TypeChecker.Semantics

import Control.Monad
import Control.Monad.Except
import qualified Control.Monad.State as State

import Data.Monoid
import Data.Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data hiding (cast)
import qualified Data.Map as Map
import Data.Generics hiding (LT,GT,cast)

import Text.PrettyPrint hiding (equals)

prove :: TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))
prove proof = try `catchError` (return . Left)
    where
    try = liftM Right $ tcBlockWith proof

-- checks if two types are equal, without using coercions, not performing substitutions
equals :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
equals l (ProcType i1 _ _ _ _) (ProcType i2 _ _ _ _) | i1 == i2 = return ()
equals l (StructType i1 _ _) (StructType i2 _ _) | i1 == i2 = return ()
--equals l (TK c1) (TK c2) = provesCstr mempty (\x y -> return $ mappend x y) equals (const ()) equals l c1 c2
equals l (TK cstr) t2 = do
    t1' <- resolveTK l cstr
    equals l t1' t2
equals l t1 (TK cstr) = do
    t2' <- resolveTK l cstr 
    equals l t1 t2'
equals l (TpltType i1 _ _ _ _) (TpltType i2 _ _ _ _) | i1 == i2 = return ()
equals l (TVar (VarName t1 n1)) (TVar (VarName t2 n2)) | n1 == n2 = do
    equals l t1 t2
equals l t1@(TVar v1) t2 = do
    t1' <- resolveTVar l v1 `mplus` constraintError EqualityException l (pp t1) (pp t2)
    equals l t1' t2
equals l t1 t2@(TVar v2) = do
    t2' <- resolveTVar l v2 `mplus` constraintError EqualityException l (pp t1) (pp t2)
    equals l t1 t2'
equals l TType TType = return ()
equals l KType KType = return ()
equals l (DType i1) (DType i2) | i1 == i2 = return ()
equals l Void Void = return ()
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
equals l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
    equals l s1 s2
    equals l t1 t2
    equalsExpr l dim1 dim2
    mapM_ (uncurry (equalsExpr l)) =<< zipSizes l szs1 szs2
equals l t1 t2@(CType {}) = do
    let t1' = defCType t1
    equals l t1' t2
equals l t1@(CType {}) t2 = do
    let t2' = defCType t2
    equals l t1 t2'
equals l (PrimType p1) (PrimType p2) = equalsPrim l p1 p2
equals l Public Public = return ()
equals l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
equals l (SysPush t1) (SysPush t2) = equals l t1 t2
equals l (SysRet t1) (SysRet t2) = equals l t1 t2
equals l (SysRef t1) (SysRef t2) = equals l t1 t2
equals l (SysCRef t1) (SysCRef t2) = equals l t1 t2
equals l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
equals l t1 t2 = constraintError EqualityException l (pp t1) (pp t2)

equalsFoldable :: (Vars loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc ()
equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)

equalsList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
equalsList l [] [] = return ()
equalsList l (x:xs) (y:ys) = do
    equals l x y
    equalsList l xs ys
equalsList l xs ys = constraintError EqualityException l (vcat $ map pp xs) (vcat $ map pp ys)

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
equalsPrim l t1 t2 = constraintError EqualityException l (pp t1) (pp t2)

equalsExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()
equalsExpr l e1 e2 = do
    v1 <- evalExpr $ fmap (Typed l) e1
    v2 <- evalExpr $ fmap (Typed l) e2
    let ce1' = fmap (const ()) e1
    let ce2' = fmap (const ()) e2
    unless (v1 == v2 || ce1' == ce2') $ constraintError EqualityException l (pp ce1') (pp ce2')

provesFoldable :: (Location loc,Foldable t) => b -> (b -> b -> TcM loc b) -> (loc -> Type -> Type -> TcM loc b) -> loc -> t Type -> t Type -> TcM loc b
provesFoldable z plus prove l t1 t2 = provesList z plus prove l (toList t1) (toList t2)

provesList :: (Location loc) => b -> (b -> b -> TcM loc b) -> (loc -> Type -> Type -> TcM loc b) -> loc -> [Type] -> [Type] -> TcM loc b
provesList z plus prove l [] [] = return z
provesList z plus prove l (x:xs) (y:ys) = do
    m1 <- prove l x y
    m2 <- provesList z plus prove l xs ys
    m1 `plus` m2
provesList z plus prove l xs ys = constraintError EqualityException l (vcat $ map pp xs) (vcat $ map pp ys)

-- | tests if two constraint are equal, possibly without resolving them
--provesCstr :: (Vars loc,Location loc) => a -> (a -> a -> TcM loc a) -> (loc -> Type -> Type -> TcM loc a) -> (a -> b) -> (loc -> Type -> Type -> TcM loc b) -> loc -> TCstr -> TCstr -> TcM loc b
--provesCstr z p eq def fallback l c1 c2 = (liftM def (provesCstrEq l c1 c2))
--                                 `mplus` (provesCstrNeq l c1 c2)
--    where
--    provesCstrEq l (TApp n1 args1) (TApp n2 args2) | n1 == n2 = provesFoldable z p eq l args1 args2
--    provesCstrEq l (TDec n1 args1) (TDec n2 args2) | n1 == n2 = provesFoldable z p eq l args1 args2
--    provesCstrEq l (PDec n1 args1 r1) (PDec n2 args2 r2) | n1 == n2 = provesFoldable z p eq l args1 args2 >> eq l r1 r2
--    provesCstrEq l (CoercesLit a1 b1) (CoercesLit a2 b2) = eq l (TyLit a1) (TyLit a2) >> eq l b1 b2
--    provesCstrEq l (Unifies a1 b1) (Unifies a2 b2) = eq l a1 a2 >> eq l b1 b2
--    provesCstrEq l (SupportedPrint x) (SupportedPrint y) = provesFoldable z p eq l x y
--    provesCstrEq l (ProjectStruct t1 a1) (ProjectStruct t2 a2) | a1 == a2 = eq l t1 t2
--    provesCstrEq l (ProjectMatrix t1 a1) (ProjectMatrix t2 a2) | a1 == a2 = eq l t1 t2
--    provesCstrEq l (BaseCastDec t1 from1 to1) (BaseCastDec t2 from2 to2) = eq l t1 t2 >> eq l from1 from2 >> eq l to1 to2
--    provesCstrEq l (InheritedCstr _ c1) (InheritedCstr _ c2) = provesCstrEq l c1 c2
--    provesCstrEq l (CBase t1) (CBase t2) = eq l t1 t2
--    provesCstrEq l (CoercesCType a1 b1) (CoercesCType a2 b2) = eq l a1 a2 >> eq l b1 b2
--    provesCstrEq l c1 c2 = constraintError EqualityException l (pp c1) (pp c2)
--
--    provesCstrNeq l c1 c2 = do
--        t1 <- resolveTCstr l c1
--        t2 <- resolveTCstr l c2
--        fallback l t1 t1

coerces :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
coerces l (TyLit lit) t2 = coercesLit l lit t2
coerces l (TK k) t2 = do
    t1 <- resolveTK l k
    coerces l t1 t2
coerces l t1 (TK k) = do
    t2 <- resolveTK l k
    coerces l t1 t2
coerces l t1@(TVar v) t2 = do
    t1 <- resolveTVar l v `mplus` coercesError l t1 t2
    coerces l t1 t2
coerces l t1 t2@(TVar v) = do
    t2 <- resolveTVar l v `mplus` coercesError l t1 t2
    coerces l t1 t2
--coerces l t1@(CType {}) t2@(CType {}) = coercesCType l t1 t2
coerces l t1 t2 = coercesError l t1 t2

-- | coerces a literal into a primitive type
coercesLit :: (Vars loc,Location loc) => loc -> Literal () -> Type -> TcM loc ()
coercesLit l lit t2@(TVar v) = do
    mb <- tryResolveTVar l v
    case mb of
        Just t -> coercesLit l lit t
        Nothing -> do
            s <- newDomainTyVar Nothing
            d <- newDimVar
            t <- case lit of
                StringLit _ s -> return $ PrimType $ DatatypeString ()
                BoolLit _ b -> return $ PrimType $ DatatypeBool ()
                otherwise -> coercesError l (TyLit lit) t2
            let ct = CType s t d []
            addSubstM l v ct         
coercesLit l lit (TK c) = resolveTK l c >>= coercesLit l lit
coercesLit l lit (CType s t d sz) = coercesLit l lit t -- to support the construction of constant arrays
coercesLit l (IntLit _ i1) (TyLit (IntLit _ i2)) | i1 <= i2 = return ()
coercesLit l (IntLit _ i) (PrimType t) | isPrimInt t || isPrimUint t = do
    let (min,max) = primIntBounds t
    unless (min <= i && i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLit l (FloatLit _ f1) (TyLit (FloatLit _ f2)) | f1 <= f2 = return ()
coercesLit l (FloatLit _ f) (PrimType t) | isPrimFloat t = do
    let (min,max) = primFloatBounds t
    unless (min <= f && f <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show f) (pp t) (show min) (show max)
coercesLit l (BoolLit _ b) (PrimType (DatatypeBool _)) = return ()
coercesLit l (StringLit _ s) (PrimType (DatatypeString _)) = return ()
coercesLit l l1 (TyLit l2) | l1 == l2 = return ()
coercesLit l l1 t2 = coercesError l (TyLit l1) t2

coercesError :: Location loc => loc -> Type -> Type -> TcM loc a
coercesError l t1 t2 = constraintError CoercionException l (pp t1) (pp t2)

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
--compares l t1@(TK c1) t2@(TK c2) = provesCstr EQ (appendOrdering l (pp t1) (pp t2)) compares id compares l c1 c2
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
compares l (TyLit lit) t2 = coercesLit l lit t2 >> return GT
compares l t1 (TyLit lit) = coercesLit l lit t1 >> return LT
compares l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
    o1 <- compares l s1 s2
    o2 <- compares l t1 t2
    o3 <- comparesExpr l dim1 dim2
    os <- mapM (uncurry (comparesExpr l)) =<< zipSizes l szs1 szs2
    foldM (appendOrdering l (pp ct1) (pp ct2)) EQ (o1:o2:o3:os)
compares l t1@(CType {}) t2 = do
    let t2' = defCType t2
    compares l t1 t2'
compares l t1 t2@(CType {}) = do
    let t1' = defCType t1
    compares l t1' t2
compares l Public Public = return EQ
compares l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return EQ
compares l (SysPush t1) (SysPush t2) = compares l t1 t2
compares l (SysRet t1) (SysRet t2) = compares l t1 t2
compares l (SysRef t1) (SysRef t2) = compares l t1 t2
compares l (SysCRef t1) (SysCRef t2) = compares l t1 t2
compares l (PrimType p1) (PrimType p2) = (equalsPrim l p1 p2 >> return EQ)
                                 `mplus` (constraintError ComparisonException l (pp p1) (pp p2))
compares l t1 t2 = constraintError ComparisonException l (pp t1) (pp t2)
    
comparesFoldable :: (Vars loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc Ordering
comparesFoldable l xs ys = comparesList l (toList xs) (toList ys)

comparesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering
comparesList l [] [] = return EQ
comparesList l a@(x:xs) b@(y:ys) = do
    f <- compares l x y
    g <- comparesList l xs ys
    appendOrdering l (vcat $ map pp a) (vcat $ map pp b) f g
comparesList l xs ys = constraintError ComparisonException l (vcat $ map pp xs) (vcat $ map pp ys)
    
appendOrdering :: Location loc => loc -> Doc -> Doc -> Ordering -> Ordering -> TcM loc Ordering
appendOrdering l a b EQ y = return y
appendOrdering l a b x EQ = return x
appendOrdering l a b LT LT = return LT
appendOrdering l a b GT GT = return GT
appendOrdering l a b x y = constraintError ComparisonException l a b
    
-- | Non-directed unification, without coercions
-- takes a type variable for the result of the unification
-- applies substitutions
unifies :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
unifies l t1@(TVar v1) t2 = provesTVar (return ()) unifies l v1 t2
unifies l t1 t2@(TVar v2) = provesTVar (return ()) unifies l v2 t1
unifies l (ProcType i1 _ _ _ _) (ProcType i2 _ _ _ _) | i1 == i2 = return ()
unifies l (StructType i1 _ _) (StructType i2 _ _) | i1 == i2 = return ()
--unifies l (TK c1) (TK c2) = provesCstr mempty (\x y -> return $ mappend x y) unifies (const ()) unifies l c1 c2
unifies l (TK c1) t2 = do
    t1' <- resolveTK l c1
    unifies l t1' t2
unifies l t1 (TK c2) = do
    t2' <- resolveTK l c2
    unifies l t1 t2'
unifies l (TpltType i1 _ _ _ _) (TpltType i2 _ _ _ _) | i1 == i2 = return ()
unifies l TType TType = return ()
unifies l KType KType = return ()
unifies l (DType k1) (DType k2) | k1 == k2 = return ()
unifies l Void Void = return ()
unifies l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
unifies l (TyLit lit) t2 = coercesLit l lit t2
unifies l t1 (TyLit lit) = coercesLit l lit t1
unifies l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
    s3 <- unifies l s1 s2
    t3 <- unifies l t1 t2
    unifiesExpr l dim1 dim2
    unifiesSizes l dim1 szs1 dim2 szs2
unifies l t1@(CType {}) t2 = do
    let t2' = defCType t2
    unifies l t1 t2'
unifies l t1 t2@(CType {}) = do
    let t1' = defCType t1
    unifies l t1' t2
unifies l (PrimType p1) (PrimType p2) = (equalsPrim l p1 p2)
                                `mplus` (constraintError UnificationException l (pp p1) (pp p2))
unifies l Public Public = return ()
unifies l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
unifies l (SysPush t1) (SysPush t2) = unifies l t1 t2
unifies l (SysRet t1) (SysRet t2) = unifies l t1 t2
unifies l (SysRef t1) (SysRef t2) = unifies l t1 t2
unifies l (SysCRef t1) (SysCRef t2) = unifies l t1 t2
unifies l t1 t2 = constraintError UnificationException l (pp t1) (pp t2) 

unifiesSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()
unifiesSizes l dim1 szs1 dim2 szs2 = do
    mapM_ (uncurry (unifiesExpr l)) =<< zipSizes l szs1 szs2

unifiesFoldable :: (Vars loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc ()
unifiesFoldable l xs ys = unifiesList l (toList xs) (toList ys)

unifiesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    unifies l x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError UnificationException l (vcat $ map pp xs) (vcat $ map pp ys) 

-- | Tries to resolve a constraint inside a proof
resolveTK :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTK l cstr = resolveTCstr l cstr

resolveTVar :: Location loc => loc -> VarName VarIdentifier Type -> TcM loc Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> tcError (locpos l) $ UnresolvedVariable (pp v)
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
tcCstrM l cstr = do
    addTemplateConstraint l cstr Nothing
    return $ TK cstr

resolveTCstr :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTCstr l k@(TApp n args) =
    liftM fst $ matchTemplate l (Left n) args Nothing (checkTemplateType $ fmap (const l) n)
resolveTCstr l k@(TDec n args) =
    liftM snd $ matchTemplate l (Left n) args Nothing (checkTemplateType $ fmap (const l) n)
resolveTCstr l k@(PDec (Left n) args r) =
    liftM snd $ matchTemplate l (Right $ Left n) args (Just r) (checkProcedure $ fmap (const l) n)
resolveTCstr l k@(PDec (Right o) args r) =
    liftM snd $ matchTemplate l (Right $ Right o) args (Just r) (checkOperator $ fmap (const l) o)
resolveTCstr l k@(Coerces t1 t2) = do
    coerces l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l k@(Unifies t1 t2) = do
    unifies l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l k@(SupportedPrint t) = do
    isSupportedPrint l t
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l k@(ProjectStruct t a) = do
    ret <- projectStructField l t a
    addTemplateConstraint l k (Just ret)
    return ret
resolveTCstr l k@(ProjectMatrix t rs) = do
    ret <- projectMatrixType l t rs
    addTemplateConstraint l k (Just ret)
    return ret
resolveTCstr l k@(IsReturnStmt cs ret dec) = do
    isReturnStmt l cs ret dec
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l k@(Cast from to) = do
    cast l from to
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l (InheritedCstr p k) = do
    resolveTCstr (updpos l p) k `catchError` (\e -> tcError (locpos l) $ TemplateSolvingError e)
resolveTCstr l k@(GetCBase t) = do
    ret <- getCBase l t
    addTemplateConstraint l k (Just ret)
    return ret
resolveTCstr l k@(SetCBase t p) = do
    ret <- setCBase l t p
    addTemplateConstraint l k (Just ret)
    return ret

cast :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Type
cast l from to = do
    case from of
        TyLit lit -> resolveTCstr l $ Coerces (TyLit lit) to
        otherwise -> resolveTCstr l $ PDec (Right $ OpCast ()) [from] to

-- base of a compound type
getCBase :: (Vars loc,Location loc) => loc -> Type -> TcM loc Type
getCBase l (CType _ t _ _) = return t
getCBase l (TVar v) = do
    mb <- tryResolveTVar l v
    case mb of
        Just t -> getCBase l t
        Nothing -> do
            s <- newDomainTyVar Nothing
            t <- newTyVar
            d <- newDimVar
            let ct = CType s t d []
            addSubstM l v ct
            return t
getCBase l (TK c) = do
    t <- resolveTK l c
    getCBase l t
getCBase l ct = genericError (locpos l) $ "Not a complex type " ++ ppr ct

setCBase :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Type
setCBase l (CType s t d sz) b = return $ CType s b d sz
setCBase l ct@(TVar v) b = do
    mb <- tryResolveTVar l v
    case mb of
        Just t -> setCBase l t b
        Nothing -> do
            s <- newDomainTyVar Nothing
            d <- newDimVar
            let ct = CType s b d []
            addSubstM l v ct
            return ct
setCBase l (TK c) b = do
    t <- resolveTK l c
    setCBase l t b
setCBase l ct b = genericError (locpos l) $ "Not a complex type " ++ ppr ct

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
    dict <- liftM tDict State.get
    liftIO $ putStrLn $ "solve [" ++ show (vcat $ map pp $ tUnsolved dict) ++ "\n]"
    solveWith dict

-- | solves all given constraints
solveWith :: (Vars loc,Location loc) => TDict loc -> TcM loc ()
solveWith dict = do
    addDict (TDict (Map.map Just $ tSolved dict) (tSubsts dict) (tValues dict))
    solveCstrs (tUnsolved dict)

solveCstrs :: (Vars loc,Location loc) => [Loc loc TCstr] -> TcM loc ()
solveCstrs [] = return ()
solveCstrs cstrs = do
    (go,rest) <- trySolveSomeCstrs cstrs
    if go
        then solveCstrs rest -- new substitions have been found, try again
        else do
            solveAllCstrs rest -- nothing has progressed, solve once and for all

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
solveAllCstrs :: (Vars loc,Location loc) => [Loc loc TCstr] -> TcM loc ()
solveAllCstrs cs = mapM_ solveCstr cs

trySolveCstr :: (Vars loc,Location loc) => Loc loc TCstr -> TcM loc Bool
trySolveCstr c = (solveCstr c >>= \ret -> liftIO (putStrLn $ "solved " ++ ppr c ++ " --> " ++ ppr ret) >> return True) `mplus` return False

solveCstr :: (Vars loc,Location loc) => Loc loc TCstr -> TcM loc ()
solveCstr (Loc l c) = do
    t <- resolveTCstr l c
    addTemplateConstraint l c (Just t)

isReturnStmt :: (Vars loc,Location loc) => loc -> Set StmtClass -> Type -> ProcedureDeclaration VarIdentifier Position -> TcM loc ()
isReturnStmt l cs ret dec = aux $ Set.toList cs
    where
    aux [StmtReturn] = return ()
    aux c =    (resolveTCstr l (Unifies Void ret) >> return ())
       `mplus` (tcError (locpos l) $ NoReturnStatement $ pp dec)

unifiesExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()
unifiesExpr l (RVariablePExpr _ v1) e2 = provesEVar (return ()) unifiesExpr l v1 e2
unifiesExpr l e1 (RVariablePExpr _ v2) = provesEVar (return ()) unifiesExpr l v2 e1
unifiesExpr l e1 e2 = equalsExpr l e1 e2
             `mplus` (constraintError UnificationException l (pp e1) (pp e2))
    
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
comparesExpr l e1 e2 = (equalsExpr l e1 e2 >> return EQ)
               `mplus` (constraintError ComparisonException l (pp e1) (pp e2))
    
constraintError :: Location loc => (Doc -> Doc -> Doc -> TypecheckerErr) -> loc -> Doc -> Doc -> TcM loc a
constraintError k l e1 e2 = do
    ss <- liftM ppSubstsGeneric getSubstsGeneric
    tcError (locpos l) $ k e1 e2 ss
    
provesEVar :: (Vars loc,Location loc) => TcM loc b -> (loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc b) -> loc -> VarName VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc b
provesEVar z go l v1@(VarName t n) e2 = do
    mb <- tryResolveEVar l (fmap (Typed l) v1)
    case mb of
        Nothing -> addValueM l (fmap (Typed l) v1) (fmap (Typed l) e2) >> z
        Just e1' -> go l (fmap typed e1') e2


