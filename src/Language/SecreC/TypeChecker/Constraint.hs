{-# LANGUAGE GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
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

-- throws a constraint
tcCstrM :: Location loc => loc -> TCstr -> TcM loc Type
tcCstrM l k = do
    err <- askErrorM
    let k' = DelayedCstr k err
    addTemplateConstraint l k' Nothing
    return $ TK k'

tcTopCstrM :: Location loc => loc -> TCstr -> TcM loc Type
tcTopCstrM l k = newErrorM $ addErrorM (topCstrErr (locpos l) k) $ tcCstrM l k

-- | error-handling for a top-level delayed constraint
topCstrErr :: Position -> TCstr -> SecrecError -> SecrecError
topCstrErr p (Unifies t1 t2) err = TypecheckerError p $ UnificationException (pp t1) (pp t2) $ Right err
topCstrErr p (Coerces t1 t2) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (Coerces2 t1 t2) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (Equals t1 t2) err = TypecheckerError p $ EqualityException (pp t1) (pp t2) $ Right err
topCstrErr p (CoercesSec t1 t2 ct) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (PDec {}) err = err
topCstrErr p (TApp {}) err = err
topCstrErr p (TDec {}) err = err
topCstrErr p t err = err

tcCstrM_ :: Location loc => loc -> TCstr -> TcM loc ()
tcCstrM_ l c = tcCstrM l c >> return ()

resolveTCstr :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTCstr l k@(TApp n args) =
    liftM fst $ matchTemplate l (Left n) args Nothing (checkTemplateType $ fmap (const l) n)
resolveTCstr l k@(TDec n args) =
    liftM snd $ matchTemplate l (Left n) args Nothing (checkTemplateType $ fmap (const l) n)
resolveTCstr l k@(PDec (Left n) args r) =
    liftM snd $ matchTemplate l (Right $ Left n) args (Just r) (checkProcedure $ fmap (const l) n)
resolveTCstr l k@(PDec (Right o) args r) =
    liftM snd $ matchTemplate l (Right $ Right o) args (Just r) (checkOperator $ fmap (const l) o)
resolveTCstr l k@(Equals t1 t2) = do
    equals l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l k@(Coerces t1 t2) = do
    coerces l t1 t2
    addTemplateConstraint l k (Just NoType)
    return NoType
resolveTCstr l k@(Coerces2 t1 t2) = do
    t3 <- coerces2 l t1 t2
    addTemplateConstraint l k (Just t3)
    return t3
resolveTCstr l k@(CoercesSec t1 t2 b) = do
    coercesSec l t1 t2 b
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
    addTemplateConstraint l k (Just $ ComplexT ret)
    return $ ComplexT ret
resolveTCstr l k@(IsReturnStmt cs ret dec) = do
    isReturnStmt l cs ret dec
    addTemplateConstraint l k (Just NoType)
    return NoType
--resolveTCstr l k@(Cast from to) = do
--    cast l from to
--    addTemplateConstraint l k (Just NoType)
--    return NoType
--resolveTCstr l err (InheritedCstr p k) = mapError err $ do
--    resolveTCstr (updpos l p) k `catchError` (\e -> tcError (locpos l) $ TemplateSolvingError e)
resolveTCstr l (DelayedCstr k err) = do
    addErrorM err $ resolveTCstr l k
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

proveWith :: (Vars loc,Location loc) => TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))
proveWith proof = try `catchError` (return . Left)
    where
    try = liftM Right $ tcProve proof

prove :: (Vars loc,Location loc) => TcM loc a -> TcM loc a
prove m = do
    (a,dict) <- tcProve m
    addDict dict
    return a

-- checks if two types are equal, without using coercions, not performing substitutions
equals :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
equals l NoType NoType = return ()
equals l (TK c) t2 = do
    t1 <- resolveTK l c
    tcCstrM_ l $ Equals t1 t2
equals l t1 (TK c) = do
    t2 <- resolveTK l c
    tcCstrM_ l $ Equals t1 t2
equals l (IdxT e1) (IdxT e2) = do
    equalsExpr l e1 e2
equals l (SysT t1) (SysT t2) = do
    equalsSys l t1 t2
equals l (DecT d1) (DecT d2) = do
    equalsDec l d1 d2
equals l (SecT s1) (SecT s2) = do
    equalsSec l s1 s2
equals l (BaseT b1) (BaseT b2) = do
    equalsBase l b1 b2
equals l (ComplexT c1) (ComplexT c2) = do
    equalsComplex l c1 c2
equals l (ComplexT c1) (BaseT b2) = do
    equalsComplex l c1 (defCType b2)
equals l (BaseT b1) (ComplexT c2) = do
    equalsComplex l (defCType b1) c2
equals l TType TType = return ()
equals l DType DType = return ()
equals l BType BType = return ()
equals l KType KType = return ()
equals l (SType k1) (SType k2) | k1 == k2 = return ()
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
equals l t1 t2 = constraintError EqualityException l (pp t1) (pp t2) Nothing

equalsSys :: (Vars loc,Location loc) => loc -> SysType -> SysType -> TcM loc ()
equalsSys l (SysPush t1) (SysPush t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysRet t1) (SysRet t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysRef t1) (SysRef t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysCRef t1) (SysCRef t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l t1 t2 = constraintError EqualityException l (pp t1) (pp t2) Nothing

equalsSec :: (Vars loc,Location loc) => loc -> SecType -> SecType -> TcM loc ()
equalsSec l Public Public = return ()
equalsSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
equalsSec l (SVar v _) s2 = do
    s1 <- resolveSVar l v
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 (SVar v _) = do
    s2 <- resolveSVar l v
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)

equalsDec :: (Vars loc,Location loc) => loc -> DecType -> DecType -> TcM loc ()
equalsDec l d1 d2 | typeTyVarId d1 == typeTyVarId d2 = return ()
equalsDec l d1 d2 = constraintError EqualityException l (pp d1) (pp d2) Nothing

equalsComplex :: (Vars loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc ()
equalsComplex l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
equalsComplex l (CType s1 t1 d1 sz1) (CType s2 t2 d2 sz2) = do
    tcCstrM l $ Equals (SecT s1) (SecT s2)
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
    tcCstrM l $ Equals (IdxT d1) (IdxT d2)
    mapM_ (\(x,y) -> tcCstrM l $ Equals (IdxT x) (IdxT y)) =<< zipSizes l sz1 sz2
equalsComplex l (CVar v) c2 = do
    c1 <- resolveCVar l v
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l c1 (CVar v) = do
    c2 <- resolveCVar l v
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l Void Void = return ()
equalsComplex l c1 c2 = constraintError EqualityException l (pp c1) (pp c2) Nothing

equalsBase :: (Vars loc,Location loc) => loc -> BaseType -> BaseType -> TcM loc ()
equalsBase l (BVar v) t2 = do
    t1 <- resolveBVar l v
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l t1 (BVar v) = do
    t2 <- resolveBVar l v
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2
equalsBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
equalsBase l b1 b2 = constraintError EqualityException l (pp b1) (pp b2) Nothing

equalsFoldable :: (Vars loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc ()
equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)

equalsList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
equalsList l [] [] = return ()
equalsList l (x:xs) (y:ys) = do
    tcCstrM l $ Equals x y
    equalsList l xs ys
equalsList l xs ys = constraintError EqualityException l (vcat $ map pp xs) (vcat $ map pp ys) Nothing

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

expandCTypeVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType
expandCTypeVar l v = do
    d <- newDomainTyVar AnyKind
    t <- newBaseTyVar
    dim <- newDimVar
    let ct = CType d t dim []
    addSubstM l (fmap (const TType) v) $ ComplexT ct
    return ct

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
coerces l (TK c1) t2 = do
    t1' <- resolveTK l c1
    tcCstrM_ l $ Coerces t1' t2
coerces l t1 (TK c2) = do
    t2' <- resolveTK l c2
    tcCstrM_ l $ Coerces t1 t2'
coerces l (BaseT t1) (BaseT t2) = unifiesBase l t1 t2
coerces l (ComplexT t1) (ComplexT t2) = coercesComplex l t1 t2
coerces l (ComplexT c1) (BaseT b2) = coercesComplex l c1 (defCType b2)
coerces l (BaseT b1) (ComplexT c2) = coercesComplex l (defCType b1) c2
coerces l (IdxT e1) (IdxT e2) = unifiesExpr l e1 e2
coerces l (SecT s1) (SecT s2) = coercesSec l s1 s2 (defCType index)
coerces l (SysT s1) (SysT s2) = coercesSys l s1 s2
coerces l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp t1) (pp t2) . Right)
    (equals l t1 t2)

coercesSys :: (Vars loc,Location loc) => loc -> SysType -> SysType -> TcM loc ()
coercesSys l (SysPush t1) (SysPush t2) = tcCstrM_ l $ Coerces t1 t2
coercesSys l (SysRet t1) (SysRet t2) = tcCstrM_ l $ Coerces t1 t2
coercesSys l (SysRef t1) (SysRef t2) = tcCstrM_ l $ Coerces t1 t2
coercesSys l (SysCRef t1) (SysCRef t2) = tcCstrM_ l $ Coerces t1 t2
coercesSys l t1 t2 = constraintError CoercionException l (pp t1) (pp t2) Nothing

coercesComplex :: (Vars loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc ()
coercesComplex l Void Void = return ()
coercesComplex l (TyLit lit) t2 = coercesLitComplex l lit t2 -- literals are never variables
coercesComplex l (CType s1 t1 d1 sz1) ct2@(CType s2 t2 d2 sz2) = do
    tcCstrM l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
    tcCstrM l $ Unifies (IdxT d1) (IdxT d2)
    unifiesSizes l d1 sz1 d2 sz2
    tcCstrM_ l $ CoercesSec s1 s2 ct2
coercesComplex l (CVar v) ct2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct1 -> coercesComplex l ct1 ct2
        Nothing -> do
            ct1 <- expandCTypeVar l v
            tcCstrM_ l $ Coerces (ComplexT ct1) (ComplexT ct2)
coercesComplex l ct1 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct2 -> coercesComplex l ct1 ct2
        Nothing -> do
            ct2 <- expandCTypeVar l v
            tcCstrM_ l $ Coerces (ComplexT ct1) (ComplexT ct2)
coercesComplex l c1 c2 = constraintError CoercionException l (pp c1) (pp c2) Nothing

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
coerces2 l t1 t2 = (prove (coerces2 l t1 t2 >> return t2))
           `mplus` (prove (coerces2 l t2 t1 >> return t1))

coercesSec :: (Vars loc,Location loc) => loc -> SecType -> SecType -> ComplexType -> TcM loc ()
coercesSec l Public Public ct = return ()
coercesSec l s1@Public (SVar v AnyKind) ct = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM_ l $ CoercesSec s1 s2 ct
        Nothing -> do
            let sub1 = Map.fromList [(v,SecT Public)]
            v' <- newDomainTyVar $ PrivateKind Nothing
            let sub2 = Map.fromList [(v,SecT v')]
            tcError (locpos l) $ MultipleTypeSubstitutions [toPPDyn sub1,toPPDyn sub2]
coercesSec l s1@Public s2@(SVar v k) ct = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp s1) (pp s2) . Right)
    (resolveSVar l v >>= \s2' -> tcCstrM_ l $ CoercesSec s1 s2' ct)
coercesSec l s1@(SVar v _) s2@(Public) ct = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp s1) (pp s2) . Right)
    (tcCstrM_ l $ Unifies (SecT s1) (SecT s2))
coercesSec l (Private d1 k1) (Private d2 k2) ct | d1 == d2 && k1 == k2 = return ()
coercesSec l s1@(Private d1 k1) s2@(SVar v _) ct = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp s1) (pp s2) . Right)
    (tcCstrM_ l $ Unifies (SecT s1) (SecT s2))
coercesSec l (SVar v AnyKind) s2@(Private d2 k2) ct = do
    mb <- tryResolveSVar l v
    case mb of
        Just s1 -> tcCstrM_ l $ CoercesSec s1 s2 ct
        Nothing -> do
            let sub1 = Map.fromList [(v,SecT Public)]
            let sub2 = Map.fromList [(v,SecT s2)]
            tcError (locpos l) $ MultipleTypeSubstitutions [toPPDyn sub1,toPPDyn sub2]
coercesSec l s1@(SVar v _) s2@(Private d2 k2) ct = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp s1) (pp s2) . Right)
    (tcCstrM_ l $ Unifies (SecT s1) (SecT s2))
coercesSec l s1@Public s2@(Private d2 k2) ct = do
    tcCstrM_ l $ PDec (Left $ ProcedureName () $ mkVarId "classify") [ComplexT $ setCSec ct s1] (ComplexT $ setCSec ct s2)
coercesSec l s1@(SVar v1 _) s2@(SVar v2 _) ct = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just t1',Just t2') -> tcCstrM_ l $ CoercesSec t1' t2' ct
        (Just t1',Nothing) -> tcCstrM_ l $ CoercesSec t1' s2 ct
        (Nothing,Just t2') -> tcCstrM_ l $ CoercesSec s1 t2' ct
        (Nothing,Nothing) -> constraintError CoercionException l (pp s1) (pp s2) Nothing
coercesSec l t1 t2 b = constraintError CoercionException l (pp t1) (pp t2) Nothing

-- | coerces a literal into a primitive type
coercesLitComplex :: (Vars loc,Location loc) => loc -> Literal () -> ComplexType -> TcM loc ()
coercesLitComplex l lit ct@(CType s t d sz) = do
    coercesLitBase l lit t
    tcCstrM_ l $ CoercesSec Public s (defCType t) -- coerce the security type
coercesLitComplex l lit (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> tcCstrM_ l $ Coerces (ComplexT $ TyLit lit) (ComplexT c2)
        Nothing -> do
            c2 <- expandCTypeVar l v
            tcCstrM_ l $ Coerces (ComplexT $ TyLit lit) (ComplexT c2)
coercesLitComplex l (IntLit _ i1) (TyLit (IntLit _ i2)) | i1 <= i2 = return ()
coercesLitComplex l (FloatLit _ f1) (TyLit (FloatLit _ f2)) | f1 <= f2 = return ()
coercesLitComplex l l1 (TyLit l2) | l1 == l2 = return ()
coercesLitComplex l l1 t2 = constraintError CoercionException l (pp l1) (pp t2) Nothing  
    
coercesLitBase :: (Vars loc,Location loc) => loc -> Literal () -> BaseType -> TcM loc ()
coercesLitBase l lit t2@(BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
       Just t2' -> tcCstrM_ l $ Coerces (ComplexT $ TyLit lit) (BaseT t2')
       Nothing -> do
           b <- case lit of
                StringLit _ s -> return $ TyPrim $ DatatypeString ()
                BoolLit _ b -> return $ TyPrim $ DatatypeBool ()
                otherwise -> constraintError CoercionException l (pp lit) (pp t2) Nothing
           addSubstM l (fmap (const BType) v) (BaseT b)
coercesLitBase l (IntLit _ i) (TyPrim t) | isPrimInt t || isPrimUint t = do
    let (min,max) = primIntBounds t
    unless (min <= i && i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (FloatLit _ f) (TyPrim t) | isPrimFloat t = do
    let (min,max) = primFloatBounds t
    unless (min <= f && f <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show f) (pp t) (show min) (show max)
coercesLitBase l (BoolLit _ b) (TyPrim (DatatypeBool _)) = return ()
coercesLitBase l (StringLit _ s) (TyPrim (DatatypeString _)) = return ()
coercesLitBase l l1 t2 = constraintError CoercionException l (pp l1) (pp t2) Nothing  

-- | Checks if a type is more specific than another, performing substitutions
compares :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering
compares l (IdxT e1) (IdxT e2) = comparesExpr l e1 e2
compares l (TK c) t2 = do
    t1 <- resolveTK l c
    compares l t1 t2
compares l t1 (TK c) = do
    t2 <- resolveTK l c
    compares l t1 t2
compares l (BaseT b1) (BaseT b2) = do
    comparesBase l b1 b2
compares l (ComplexT c1) (ComplexT c2) = do
    comparesComplex l c1 c2
compares l (BaseT b1) (ComplexT c2) = do
    comparesComplex l (defCType b1) c2
compares l (ComplexT c1) (BaseT b2) = do
    comparesComplex l c1 (defCType b2)
compares l (SecT s1) (SecT s2) = do
    comparesSec l s1 s2
compares l (SysT t1) (SysT t2) = do
    comparesSys l t1 t2
compares l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . ComparisonException (pp t1) (pp t2) . Right)
    (equals l t1 t2 >> return EQ)

comparesSec :: (Vars loc,Location loc) => loc -> SecType -> SecType -> TcM loc Ordering
comparesSec l Public Public = return EQ
comparesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return EQ
comparesSec l Public (Private {}) = return LT -- public computations are preferrable
comparesSec l t1@(SVar v1 _) t2@(SVar v2 _) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> return EQ
        (Just t1',Nothing) -> comparesSec l t1' t2
        (Nothing,Just t2') -> comparesSec l t1 t2'
        (Just t1',Just t2') -> comparesSec l t1' t2'        
comparesSec l t1 (SVar v _) = do
    mb <- tryResolveSVar l v
    case mb of
        Just t2 -> comparesSec l t1 t2
        Nothing -> return LT
comparesSec l (SVar v _) t2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just t1 -> comparesSec l t1 t2
        Nothing -> return GT
comparesSec l t1 t2 = constraintError ComparisonException l (pp t1) (pp t2) Nothing

comparesSys :: (Vars loc,Location loc) => loc -> SysType -> SysType -> TcM loc Ordering
comparesSys l (SysPush t1) (SysPush t2) = do
    compares l t1 t2
comparesSys l (SysRet t1) (SysRet t2) = do
    compares l t1 t2
comparesSys l (SysRef t1) (SysRef t2) = do
    compares l t1 t2
comparesSys l (SysCRef t1) (SysCRef t2) = do
    compares l t1 t2
comparesSys l t1 t2 = constraintError ComparisonException l (pp t1) (pp t2) Nothing

comparesBase :: (Vars loc,Location loc) => loc -> BaseType -> BaseType -> TcM loc Ordering
comparesBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2 >> return EQ
comparesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2 >> return EQ
comparesBase l t1@(BVar v1) t2@(BVar v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> return EQ
        (Just t1',Nothing) -> comparesBase l t1' t2
        (Nothing,Just t2') -> comparesBase l t1 t2'
        (Just t1',Just t2') -> comparesBase l t1' t2'        
comparesBase l t1 (BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> comparesBase l t1 t2
        Nothing -> return LT
comparesBase l (BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> comparesBase l t1 t2
        Nothing -> return GT
comparesBase l t1 t2 = constraintError ComparisonException l (pp t1) (pp t2) Nothing

comparesComplex :: (Vars loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc Ordering
comparesComplex l Void Void = return EQ
comparesComplex l (TyLit lit1) (TyLit lit2) | lit1 == lit2 = return EQ
comparesComplex l (TyLit lit) t2 = coercesLitComplex l lit t2 >> return GT
comparesComplex l t1 (TyLit lit) = coercesLitComplex l lit t1 >> return LT
comparesComplex l ct1@(CType s1 t1 d1 sz1) ct2@(CType s2 t2 d2 sz2) = do
    o1 <- comparesSec l s1 s2
    o2 <- comparesBase l t1 t2
    o3 <- comparesExpr l d1 d2
    os <- mapM (\(x,y) -> comparesExpr l x y) =<< zipSizes l sz1 sz2
    foldM (appendOrdering l (pp ct1) (pp ct2)) EQ (o1:o2:o3:os)
comparesComplex l t1@(CVar v1) t2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> return EQ
        (Just t1',Nothing) -> comparesComplex l t1' t2
        (Nothing,Just t2') -> comparesComplex l t1 t2'
        (Just t1',Just t2') -> comparesComplex l t1' t2'        
comparesComplex l t1 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2 -> comparesComplex l t1 t2
        Nothing -> return LT
comparesComplex l (CVar v) t2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1 -> comparesComplex l t1 t2
        Nothing -> return GT
comparesComplex l t1 t2 = constraintError ComparisonException l (pp t1) (pp t2) Nothing
    
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
unifies l (IdxT e1) (IdxT e2) = unifiesExpr l e1 e2
unifies l (SecT s1) (SecT s2) = unifiesSec l s1 s2
unifies l (SysT s1) (SysT s2) = unifiesSys l s1 s2
unifies l (BaseT b1) (BaseT b2) = unifiesBase l b1 b2
unifies l (BaseT b1) (ComplexT c2) = unifiesComplex l (defCType b1) c2
unifies l (ComplexT c1) (BaseT b2) = unifiesComplex l c1 (defCType b2)
unifies l (ComplexT c1) (ComplexT c2) = unifiesComplex l c1 c2
unifies l (TK c) t2 = do
    t1 <- resolveTK l c
    unifies l t1 t2
unifies l t1 (TK c) = do
    t2 <- resolveTK l c
    unifies l t1 t2
unifies l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . UnificationException (pp t1) (pp t2) . Right)
    (equals l t1 t2)

unifiesComplex :: (Vars loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc ()
unifiesComplex l Void Void = return ()
unifiesComplex l (TyLit lit) t2 = coercesLitComplex l lit t2
unifiesComplex l t1 (TyLit lit) = coercesLitComplex l lit t1
unifiesComplex l (CType s1 t1 d1 sz1) (CType s2 t2 d2 sz2) = do
    tcCstrM l $ Unifies (SecT s1) (SecT s2)
    tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
    tcCstrM l $ Unifies (IdxT d1) (IdxT d2)
    mapM_ (\(x,y) -> tcCstrM l $ Unifies (IdxT x) (IdxT y)) =<< zipSizes l sz2 sz2
unifiesComplex l (CVar v) c2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just c1 -> tcCstrM_ l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (fmap (const TType) v) (ComplexT c2)
unifiesComplex l c1 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> tcCstrM_ l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (fmap (const TType) v) (ComplexT c1)
unifiesComplex l t1 t2 = constraintError UnificationException l (pp t1) (pp t2) Nothing

unifiesSVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> SVarKind -> SecType -> TcM loc ()
unifiesSVar l v k@AnyKind s1 = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind Nothing) s1@(Private _ _) = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind (Just n)) s1@(Private d ((==n) -> True)) = addSVarSubstM l v s1
unifiesSVar l v k s1@(SVar v1 k1) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> tcCstrM_ l $ Unifies (SecT $ SVar v k) (SecT s1')
        Nothing -> if k <= k1
            then addSVarSubstM l v s1
            else addSVarSubstM l v1 (SVar v k)
unifiesSVar l v k s = constraintError UnificationException l (pp $ SVar v k) (pp s) Nothing

addSVarSubstM l v s = addSubstM l (fmap (const $ SType $ secTypeKind s) v) (SecT s)

unifiesSec :: (Vars loc,Location loc) => loc -> SecType -> SecType -> TcM loc ()
unifiesSec l Public Public = return ()
unifiesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
unifiesSec l (SVar v k) s2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just s1 -> tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s2
unifiesSec l s1 (SVar v k) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s1
unifiesSec l t1 t2 = constraintError UnificationException l (pp t1) (pp t2) Nothing

unifiesSys :: (Vars loc,Location loc) => loc -> SysType -> SysType -> TcM loc ()
unifiesSys l (SysPush t1) (SysPush t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRet t1) (SysRet t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRef t1) (SysRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysCRef t1) (SysCRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l t1 t2 = constraintError UnificationException l (pp t1) (pp t2) Nothing

unifiesBase :: (Vars loc,Location loc) => loc -> BaseType -> BaseType -> TcM loc ()
unifiesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
unifiesBase l (BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (fmap (const BType) v) (BaseT t2)
unifiesBase l t1 (BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (fmap (const BType) v) (BaseT t1)
unifiesBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2
unifiesBase l t1 t2 = constraintError UnificationException l (pp t1) (pp t2) Nothing

unifiesSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()
unifiesSizes l dim1 szs1 dim2 szs2 = do
    mapM_ (\(x,y) -> tcCstrM l $ Unifies (IdxT x) (IdxT y)) =<< zipSizes l szs1 szs2

unifiesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError UnificationException l (vcat $ map pp xs) (vcat $ map pp ys) Nothing

-- | Tries to resolve a constraint inside a proof
resolveTK :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type
resolveTK l cstr = resolveTCstr l cstr

resolveCVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType
resolveCVar l v = resolveTVar l v >>= typeToComplexType l

resolveSVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc SecType
resolveSVar l v = resolveTVar l v >>= typeToSecType l

resolveBVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc BaseType
resolveBVar l v = resolveTVar l v >>= typeToBaseType l

resolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> do
            ss <- liftM ppSubstsGeneric getSubstsGeneric
            tcError (locpos l) $ UnresolvedVariable (pp v) ss
        Just t -> return t

tryResolveSVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe SecType)
tryResolveSVar l v = tryResolveTVar l v >>= mapM (typeToSecType l)

tryResolveBVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe BaseType)
tryResolveBVar l v = tryResolveTVar l v >>= mapM (typeToBaseType l)

tryResolveCVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe ComplexType)
tryResolveCVar l v = tryResolveTVar l v >>= mapM (typeToComplexType l)

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc (Maybe Type)
tryResolveTVar l v = do
    -- lookup in the substitution environment
    s <- liftM (tSubsts . tDict) State.get
    let mb = substsFromMap s $ v
    return $ mb

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
    forM_ ts $ \t -> resolveTCstr l (PDec (Left $ ProcedureName () (mkVarId "tostring")) [t] $ BaseT string)

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
            case go of
                Left () -> solveCstrs -- new substitions have been found, try again
                Right opts -> guessCstrs opts -- nothing has progressed, try guessing

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (Vars loc,Location loc) => [Loc loc TCstr] -> TcM loc (Either () (Maybe [SubstsType]),[Loc loc TCstr])
trySolveSomeCstrs = foldrM solveBound (Right Nothing,[])
    where
    solveBound x@(Loc l c) (b,xs) = do
        ok <- trySolveCstr x
        case ok of
            Left () -> return (ok,xs)
            Right opts -> do
                let b' = bimap id (append opts) b
                return (b',x:xs)
    append Nothing y = y
    append x y = x

guessCstrs :: (Vars loc,Location loc) => Maybe [SubstsType] -> TcM loc ()
guessCstrs opts = steps $ maybe [] id opts
    where
    steps [] = solveAllCstrs
    steps [o] = step o
    steps (o:os) = step o `mplus` steps os
    step o = do
        addSubsts o
        liftIO $ putStrLn $ "step subst " ++ ppr o
        ss <- liftM (tUnsolved . tDict) State.get
        liftIO $ putStrLn $ "step {" ++ show (vcat $ map pp ss) ++ "\n}\n"
        solveCstrs

-- | solves all constraints
solveAllCstrs :: (Vars loc,Location loc) => TcM loc ()
solveAllCstrs = do
    cstrs <- liftM (tUnsolved . tDict) State.get
    liftIO $ putStrLn $ "solveAll [" ++ show (vcat $ map pp cstrs) ++ "\n]"
--    ss <- liftM ppSubstsGeneric getSubstsGeneric
--    liftIO $ putStrLn $ "solveAll {" ++ show (vcat $ map pp cstrs) ++ "\n}\n" ++ show ss
    mapM_ solveCstr cstrs

trySolveCstr :: (Vars loc,Location loc) => Loc loc TCstr -> TcM loc (Either () (Maybe [SubstsType]))
trySolveCstr c = (solveCstr c >> return (Left ())) `catchError` (\e -> case e of
    TypecheckerError _ (MultipleTypeSubstitutions opts) -> return $ Right $ Just $ concatMap (maybeToList . fromPPDyn) opts
    otherwise -> return $ Right Nothing)

solveCstr :: (Vars loc,Location loc) => Loc loc TCstr -> TcM loc ()
solveCstr (Loc l c) = do
    t <- resolveTCstr l c
    addTemplateConstraint l c (Just t)

isReturnStmt :: (Vars loc,Location loc) => loc -> Set StmtClass -> Type -> ProcedureDeclaration VarIdentifier Position -> TcM loc ()
isReturnStmt l cs ret dec = aux $ Set.toList cs
    where
    aux [StmtReturn] = return ()
    aux c = mapError (\err -> TypecheckerError (locpos l) $ NoReturnStatement $ pp dec) (resolveTCstr l (Unifies (ComplexT Void) ret) >> return ())

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


