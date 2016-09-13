{-# LANGUAGE ScopedTypeVariables, TupleSections, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Base hiding (int)
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.Prover.Semantics
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Conversion

import Data.Bifunctor
import Data.Traversable
import Data.Foldable
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.List as List
import Data.Int
import Data.Word
import qualified Data.Foldable as Foldable

import Control.Monad hiding (mapM)
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (Reader(..),ReaderT(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Except

import Text.PrettyPrint as PP hiding (equals)

import Prelude hiding (mapM)

--isBoolTypeM :: (ProverK loc m) => loc -> Type -> TcM m Bool
--isBoolTypeM l t | isBoolType t = return True
--isBoolTypeM l t = liftM isBoolBaseType (typeToBaseType l t) `mplus` return False
--
--isIntTypeM :: (ProverK loc m) => loc -> Type -> TcM m Bool
--isIntTypeM l t | isIntType t = return True
--isIntTypeM l t = liftM isIntBaseType (typeToBaseType l t) `mplus` return False

castTypeToType :: CastType VarIdentifier Type -> Type
castTypeToType (CastPrim p) = BaseT $ TyPrim $ funit p
castTypeToType (CastTy (TypeName t n)) = t

typeToSecType :: (ProverK loc m) => loc -> Type -> TcM m SecType
typeToSecType l (SecT s) = return s
typeToSecType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp $ KindT $ KVar (mkVarId "*") False)

typeToKindType :: (ProverK loc m) => loc -> Type -> TcM m KindType
typeToKindType l (KindT s) = return s
typeToKindType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp $ KType False)

typeToDecType :: (ProverK loc m) => loc -> Type -> TcM m DecType
typeToDecType l (DecT s) = return s
typeToDecType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp DType)

typeToVArrayType :: (ProverK loc m) => loc -> Type -> Expr -> TcM m VArrayType
typeToVArrayType l (VArrayT a) sz = do
    prove l "typeToVArrayType" $ unifiesExprTy l True sz (vArraySize a)
    return a
typeToVArrayType l t sz = ppM l t >>= tcError (locpos l) . TypeConversionError (pp (NoType $ "array of size " ++ ppr sz))

typeToPrimType :: (ProverK loc m) => loc -> Type -> TcM m Prim
typeToPrimType l t = do
    b <- typeToBaseType l t
    case b of
        TyPrim p -> return p
        otherwise -> genTcError (locpos l) $ text "not a primitive type" <+> pp t

typeToBaseType :: (ProverK loc m) => loc -> Type -> TcM m BaseType
typeToBaseType l (BaseT s) = return s
typeToBaseType l t@(ComplexT ct) = case ct of
    (CType s b d) -> do
        tcCstrM_ l $ Equals (SecT s) (SecT Public)
        tcCstrM_ l $ Equals (IdxT d) (IdxT $ indexExpr 0)
        return b
    CVar v@(nonTok -> True) isNotVoid -> do
        mb <- tryResolveCVar l v
        ct' <- case mb of
            Just ct' -> return ct'
            Nothing -> if isNotVoid
                then expandCTypeVar l v
                else throwTcError $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "to convert to base type" <+> pp t) Nothing
        typeToBaseType l (ComplexT ct')     
    otherwise -> ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)
typeToBaseType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)

typeToComplexType :: (ProverK loc m) => loc -> Type -> TcM m ComplexType
typeToComplexType l (ComplexT s) = return s
typeToComplexType l (BaseT s) = return $ defCType s
typeToComplexType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp (TType False))

isComplex :: Type -> Bool
isComplex (ComplexT s) = True
isComplex (BaseT b) = True
isComplex _ = False

tcCastType :: (ProverK loc m) => CastType Identifier loc -> TcM m (CastType VarIdentifier (Typed loc))
tcCastType (CastPrim p) = do
    liftM CastPrim $ tcPrimitiveDatatype p
tcCastType (CastTy v) = do
    liftM CastTy $ tcTypeName v

tcTypeName :: (ProverK loc m) => TypeName Identifier loc -> TcM m (TypeName VarIdentifier (Typed loc))
tcTypeName tn@(TypeName l n) = do
    let n' = mkVarId n
    isAnn <- getAnn
    checkTypeName isAnn (TypeName l n')

tcTypeSpec :: (ProverK loc m) => TypeSpecifier Identifier loc -> IsVariadic -> TcM m (TypeSpecifier VarIdentifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) isVariadic = do
    (sec',tsec) <- tcMbSecType sec 
    (dta') <- tcDatatypeSpec dta
    let tdta = typed $ loc dta'
    -- enforce structs to be public
    case tdta of
        BaseT (TApp {}) -> tcCstrM_ l $ IsPublic True tsec
        otherwise -> return ()
    (dim',tdim) <- tcMbDimtypeSpec l (pp tsec <+> pp tdta) dim
    t <- buildTypeSpec l tsec tdta (fmap typed tdim) isVariadic
    return (TypeSpecifier (Typed l t) sec' dta' dim')
    
buildTypeSpec :: (ProverK loc m) => loc -> Type -> Type -> Expr -> IsVariadic -> TcM m Type
buildTypeSpec l tsec tdta tdim True = do
    tsecs <- if isVATy (tyOf tsec) then expandVariadicType l (tsec,True) else return [tsec]
    tdtas <- if isVATy (tyOf tdta) then expandVariadicType l (tdta,True) else return [tdta]
    tdims <- if isVATy (loc tdim) then expandVariadicExpr l (tdim,True) else return [tdim]
    tzips <- zipCTypeArgs l tsecs tdtas tdims
    ts <- forM tzips $ \(s,b,dim) -> buildTypeSpec l s b dim False
    case ts of
        [t] -> do
            sz@(RVariablePExpr _ n) <- newSizeVar Nothing
            --removeFree $ varNameId n
            return $ VAType t sz
        otherwise -> return $ VArrayT $ VAVal ts (TType True)
buildTypeSpec l tsec tdta dim False = do
    ts <- typeToSecType l tsec
    td <- typeToBaseType l tdta
    dim' <- tcExprTy' (BaseT index) $ fmap (Typed l) dim
    let ct = CType ts td (fmap typed dim')
    return $ ComplexT ct
    
zipCTypeArgs l [s] [b] [d] = return [(s,b,d)]
zipCTypeArgs l [s] bs ds = zipCTypeArgs l (repeat s) bs ds
zipCTypeArgs l ss [b] ds = zipCTypeArgs l ss (repeat b) ds
zipCTypeArgs l ss bs [d] = zipCTypeArgs l ss bs (repeat d)
zipCTypeArgs l ss bs ds = zipCTypeArgs' l ss bs ds
    where
    zipCTypeArgs l [] [] [] = return []
    zipCTypeArgs' l (s:ss) (b:bs) (d:ds) = liftM ((s,b,d) :) (zipCTypeArgs' l ss bs ds)
    zipCTypeArgs' l _ _ _ = genTcError (locpos l) $ text "variadic arrays with mismatching sizes"
    
tcMbSecType :: (ProverK loc m) => Maybe (SecTypeSpecifier Identifier loc) -> TcM m (Maybe (SecTypeSpecifier VarIdentifier (Typed loc)),Type)
tcMbSecType Nothing = return (Nothing,SecT Public) -- public by default
tcMbSecType (Just sec) = do
    sec' <- tcSecType sec
    let t = typed $ loc sec'
    return (Just sec',t)

tcSecType :: (ProverK loc m) => SecTypeSpecifier Identifier loc -> TcM m (SecTypeSpecifier VarIdentifier (Typed loc))
tcSecType (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l $ SecT Public)
tcSecType (PrivateSpecifier l d) = do
    let vd = bimap mkVarId id d
    isAnn <- getAnn
    vd' <- checkDomain isAnn vd
    return $ PrivateSpecifier (Typed l $ typed $ loc vd') vd'

tcDatatypeSpec :: (ProverK loc m) => DatatypeSpecifier Identifier loc -> TcM m (DatatypeSpecifier VarIdentifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM (tcVariadicArg tcTemplateTypeArgument) args
    let ts = map (mapFst (typed . loc)) args'
    let vn = bimap mkVarId id n
    dec <- newDecVar Nothing
    topTcCstrM_ l $ TDec True (funit vn) ts dec
    let ret = TApp (funit vn) ts dec
    let n' = fmap (flip Typed (DecT dec)) vn
    return $ TemplateSpecifier (Typed l $ BaseT ret) n' args'
tcDatatypeSpec (VariableSpecifier l tn) = do
    tn' <- tcTypeName tn
    return $ VariableSpecifier (Typed l $ typed $ loc tn') tn'
tcDatatypeSpec (MultisetSpecifier l b) = do
    b' <- tcDatatypeSpec b
    let t = typed $ loc b'
    tb <- typeToBaseType l t
    return $ MultisetSpecifier (Typed l $ BaseT $ MSet tb) b'

tcPrimitiveDatatype :: (MonadIO m,Location loc) => PrimitiveDatatype loc -> TcM m (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = BaseT $ TyPrim $ funit p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: (ProverK loc m) => TemplateTypeArgument Identifier loc -> TcM m (TemplateTypeArgument VarIdentifier (Typed loc))
tcTemplateTypeArgument (GenericTemplateTypeArgument l n) = do
    isAnn <- getAnn
    isLeak <- getLeak
    n' <- checkTemplateArg isAnn isLeak (bimap mkVarId id n)
    let t = typed $ loc n'
    return $ GenericTemplateTypeArgument (Typed l t) n'
tcTemplateTypeArgument (TemplateTemplateTypeArgument l n args) = do
    TemplateSpecifier l' n' args' <- tcDatatypeSpec (TemplateSpecifier l n args)
    return $ TemplateTemplateTypeArgument l' n' args'
tcTemplateTypeArgument (PrimitiveTemplateTypeArgument l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveTemplateTypeArgument (Typed l t) p'
tcTemplateTypeArgument (ExprTemplateTypeArgument l e) = do
    e' <- tcPureExpr e
    let t = IdxT (fmap typed e')
    return $ ExprTemplateTypeArgument (Typed l t) e'
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = SecT $ Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: (ProverK loc m) => loc -> Doc -> Maybe (DimtypeSpecifier Identifier loc) -> TcM m (Maybe (DimtypeSpecifier VarIdentifier (Typed loc)),Expression VarIdentifier (Typed loc))
tcMbDimtypeSpec l doc Nothing = return (Nothing,(indexExprLoc l 0)) -- 0 by default
tcMbDimtypeSpec l doc (Just dim) = do
    (dim',t) <- tcDimtypeSpec doc dim
    return (Just dim',t)

tcDimtypeSpec :: (ProverK loc m) => Doc -> DimtypeSpecifier Identifier loc -> TcM m (DimtypeSpecifier VarIdentifier (Typed loc),Expression VarIdentifier (Typed loc))
tcDimtypeSpec doc (DimSpecifier l e) = do
    e' <- tcPureExpr e -- we don't commit to a type yet
    return (DimSpecifier (notTyped "tcDimtypeSpec" l) e',e') 

tcRetTypeSpec :: (ProverK loc m) => ReturnTypeSpecifier Identifier loc -> TcM m (ReturnTypeSpecifier VarIdentifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing) = do
    let t = Void
    return $ ReturnType (Typed l $ ComplexT Void) Nothing
tcRetTypeSpec (ReturnType l (Just t)) = do
    t' <- tcTypeSpec t False
    let ty = typed $ loc t'
    return (ReturnType (Typed l ty) (Just t'))

-- | Retrieves a constant dimension from a type
typeDim :: (ProverK loc m) => loc -> Type -> TcM m Expr
typeDim l (BaseT _) = return $ indexExpr 0
typeDim l (ComplexT (CType _ _ e)) = return e
typeDim l (VAType _ _) = return $ indexExpr 1
typeDim l t = genTcError (locpos l) $ text "No dimension for type" <+> pp t

projectMatrixType :: (ProverK loc m) => loc -> Type -> [ArrayProj] -> TcM m Type
projectMatrixType l (ComplexT ct) rngs = liftM ComplexT $ projectMatrixCType l ct rngs
    where
    projectMatrixCType l ct@(CType sec t dim) rngs = do
        (dim'') <- projectSizes l ct 1 dim rngs  
        return $ CType sec t dim''
    projectMatrixCType l (CVar v@(nonTok -> True) isNotVoid) rngs = do
        t <- resolveCVar l v
        projectMatrixCType l t rngs
projectMatrixType l (VAType t sz) [rng] = projectSizeTyArray l t sz rng
    where
    projectSizeTyArray l t sz (ArrayIdx i) = do
        projectSize l (VAType t sz) 1 (Just sz) i i
        return t
    projectSizeTyArray l t sz (ArraySlice i j) = do
        Just sz' <- projectSize l (VAType t sz) 1 (Just sz) i j
        return $ VAType t sz'
projectMatrixType l t rngs = genTcError (locpos l) $ text "Cannot project type " <+> quotes (pp t <> brackets (sepBy comma $ map pp rngs))

projectSizes :: (ProverK loc m) => loc -> ComplexType -> Word64 -> Expr -> [ArrayProj] -> TcM m Expr
projectSizes p ct i dim ys = do
    n <- evaluateIndexExpr p =<< typeDim p (ComplexT ct)
    (r) <- projectSizes' p ct i n ys
    return (indexExpr r)
  where
    projectSizes' p ct i dim [] = return (dim)
    projectSizes' p ct i 0 ys = do
        tcError (locpos p) $ MismatchingArrayDimension (pp ct) (pp $ pred i + toEnum (length ys)) Nothing
    projectSizes' p ct i dim (ArrayIdx y:ys) = do -- project the dimension
        projectSize p (ComplexT ct) i Nothing y y
        projectSizes' p ct (succ i) (pred dim) ys
    projectSizes' p ct i dim (ArraySlice y1 y2:ys) = do -- narrow the dimension
        projectSize p (ComplexT ct) i Nothing y1 y2
        (dim') <- projectSizes' p ct (succ i) dim ys
        return (dim')

projectSize :: (ProverK loc m) => loc -> Type -> Word64 -> Maybe Expr -> ArrayIndex -> ArrayIndex -> TcM m (Maybe Expr)
projectSize p t i Nothing y1 y2 = return Nothing
projectSize p t i (Just x) y1 y2 = do
    let low = case y1 of
                NoArrayIndex -> DynArrayIndex $ indexExpr 0
                i -> i
    let upp = case y2 of
                NoArrayIndex -> DynArrayIndex x
                i -> i
    let arrerr = GenericError (locpos p) (text "Unknown") Nothing
    let elow = arrayIndexExpr low
    let eupp = arrayIndexExpr upp
    case (low,upp) of
        (DynArrayIndex el,DynArrayIndex eu) -> do
            liftM Just $ subtractIndexExprs p False eupp elow
        otherwise -> do
            errWarn $ TypecheckerError (locpos p) $ UncheckedRangeSelection (pp t) i (pp elow <> char ':' <> pp eupp) arrerr
            liftM Just $ subtractIndexExprs p False eupp elow          

structBody :: (ProverK loc m) => loc -> DecType -> TcM m InnerDecType
structBody l d@(DecType _ Nothing _ _ _ _ _ _ b) = return b
structBody l d@(DecType j (Just i) _ _ _ _ _ _ (StructType sl sid _ cl)) = do
    (DecType _ isRec _ _ _ _ _ _ s@(StructType {})) <- checkStruct l True (isAnnDecClass cl) (isLeakDec d) sid j
    return s        
structBody l (DVar v@(nonTok -> True)) = resolveDVar l v >>= structBody l
--structBody l d = genTcError (locpos l) $ text "structBody" <+> pp d

-- | checks that a given type is a struct type, resolving struct templates if necessary, and projects a particular field.
projectStructField :: (ProverK loc m) => loc -> BaseType -> AttributeName VarIdentifier () -> TcM m ComplexType
projectStructField l t@(TyPrim {}) a = tcError (locpos l) $ FieldNotFound (pp t) (pp a)
projectStructField l t@(BVar v@(nonTok -> True)) a = do
    b <- resolveBVar l v
    projectStructField l b a
projectStructField l (TApp _ _ d) a = do
    r <- structBody l d
    projectStructFieldDec l r a
    
projectStructFieldDec :: (ProverK loc m) => loc -> InnerDecType -> AttributeName VarIdentifier () -> TcM m ComplexType
projectStructFieldDec l t@(StructType _ _ (Just atts) cl) (AttributeName _ a) = do -- project the field
    case List.find (\(Attribute _ t f _) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound (pp t) (pp a)
        Just (Attribute t _ f szs) -> do
            typeToComplexType l t
projectStructFieldDec l t a = genTcError (locpos l) $ text "cannot project field" <+> pp a <+> text "on type" <+> pp t

-- | Typechecks the sizes of a matrix and appends them to a given complex type.
tcTypeSizes :: (ProverK loc m) => loc -> Type -> Maybe (Sizes Identifier loc) -> TcM m (Type,Maybe (Sizes VarIdentifier (Typed loc)))
tcTypeSizes l ty szs = do
    (szs') <- mapM (tcSizes l) szs
    let tszs' = fmap (fmap typed) szs'
    ty' <- refineTypeSizes l ty tszs'
    return (ty',szs')

variadicExprsLength :: (ProverK loc m) => loc -> Bool -> [(Expr,IsVariadic)] -> TcM m Expr
variadicExprsLength l isTop [] = return $ indexExpr 0
variadicExprsLength l isTop es = mapM (variadicExprLength l) es >>= foldr0M (indexExpr 0) (sumIndexExprs l isTop)
    where
    variadicExprLength :: (ProverK loc m) => loc -> (Expr,IsVariadic) -> TcM m Expr
    variadicExprLength l (e,False) = return $ indexExpr 1
    variadicExprLength l (e,True) = do
        let t = loc e
        case t of
            VAType _ sz -> return sz
            VArrayT (VAVal ts _) -> return $ indexExpr $ toEnum $ length ts
            VArrayT (VAVar v _ sz) -> return sz
            otherwise -> genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)

--evalVarExprs :: (ProverK loc m) => loc -> [(Expr,IsVariadic)] -> TcM m ()
--evalVarExprs l = mapM_ (evalVarExpr l)
--    where
--    evalVarExpr :: (ProverK loc m) => loc -> (Expr,IsVariadic) -> TcM m ()
--    evalVarExpr l x = do
--        es <- expandVariadicExpr l x
--        mapM_ (evaluateIndexExpr . fmap (Typed l)) es

matchTypeDimension :: (ProverK loc m) => loc -> Expr -> [(Expr,IsVariadic)] -> TcM m ()
matchTypeDimension l td szs = addErrorM l (TypecheckerError (locpos l) . Halt . MismatchingArrayDimension (pp td) (pp szs) . Just) $ do
    d <- variadicExprsLength l False szs 
--    liftIO $ putStrLn $ "matchTypeDim " ++ ppr td ++ " " ++ ppr szs ++ " " ++ ppr d
    unifiesExpr l True td d

-- | Update the size of a compound type
-- for variadic arrays, we set the size of each base type and not of the array itself
refineTypeSizes :: (ProverK loc m) => loc -> Type -> Maybe (Sizes VarIdentifier Type) -> TcM m Type
refineTypeSizes l ct@(ComplexT (CType s t d)) Nothing = do -- check the generated size
    return ct
refineTypeSizes l ct@(ComplexT (CType s t d)) (Just (Sizes szs)) = do -- discard the generated size in detriment of the declared size
    let sz' = Foldable.toList szs
    tcCstrM_ l $ MatchTypeDimension d sz'
    return $ ComplexT $ CType s t d
refineTypeSizes l (VArrayT (VAVal ts b)) szs = do
    liftM (VArrayT . flip VAVal b) $ mapM (\t -> refineTypeSizes l t szs) ts
refineTypeSizes l (VArrayT (VAVar v b sz)) szs = do
    b' <- refineTypeSizes l b szs
    return $ VArrayT $ VAVar v b' sz
refineTypeSizes l (VAType b sz) szs = do
    b' <- refineTypeSizes l b szs
    return $ VAType b' sz
refineTypeSizes l ct _ = genTcError (locpos l) $ text "Failed to add type size" <+> pp ct

variadicBase :: Type -> Type
variadicBase (VAType b sz) = b
variadicBase t = error $ "variadicBase: " ++ ppr t

typeBase :: (ProverK loc m) => loc -> Type -> TcM m Type
typeBase l (BaseT b) = return $ BaseT b
typeBase l (ComplexT (CType Public b _)) = return $ BaseT b
typeBase l (ComplexT (CType s b _)) = return $ ComplexT $ CType s b (indexExpr 0)
typeBase l (ComplexT (CVar v@(nonTok -> True) _)) = do
    ct <- resolveCVar l v
    typeBase l (ComplexT ct)
typeBase l (VAType b sz) = return b
typeBase l t = genTcError (locpos l) $ text "No static base type for type" <+> quotes (pp t)
    
isPublic :: ProverK loc m => loc -> Bool -> Type -> TcM m ()
isPublic l doUnify (BaseT b) = return ()
isPublic l doUnify (ComplexT (CVar v@(nonTok -> True) _)) = do
    ct <- resolveCVar l v
    isPublic l doUnify (ComplexT ct)
isPublic l doUnify (ComplexT (CType s _ _)) = isPublicSec l doUnify s
isPublic l doUnify (SecT s) = isPublicSec l doUnify s
isPublic l doUnify t = genTcError (locpos l) $ text "type" <+> pp t <+> text "is not private"
    
isPublicSec :: ProverK loc m => loc -> Bool -> SecType -> TcM m ()
isPublicSec l True s = unifiesSec l s Public
isPublicSec l False s = equalsSec l s Public
    
isPrivate :: ProverK loc m => loc -> Bool -> Type -> TcM m ()
isPrivate l doUnify (ComplexT (CVar v@(nonTok -> True) isNotVoid)) = do
    ct <- resolveCVar l v
    isPrivate l doUnify (ComplexT ct)
isPrivate l doUnify (ComplexT (CType s _ _)) = isPrivateSec l doUnify s
isPrivate l doUnify (SecT s) = isPrivateSec l doUnify s
isPrivate l doUnify t = genTcError (locpos l) $ text "type" <+> pp t <+> text "is not private"
    
isPrivateSec :: ProverK loc m => loc -> Bool -> SecType -> TcM m ()
isPrivateSec l True s = do
    k' <- newKindVar "pk" True Nothing
    s' <- newDomainTyVar "ps" k' Nothing
    unifiesSec l s s'
isPrivateSec l False (Private {}) = return ()
isPrivateSec l False s = genTcError (locpos l) $ text "security type" <+> pp s <+> text "is not private"

typeSize :: (ProverK loc m) => loc -> Type -> TcM m Expr
typeSize l (BaseT _) = return $ indexExpr 1
--typeSize l (ComplexT (CType _ _ _ (Just []))) = return $ indexExpr 1
--typeSize l (ComplexT (CType _ _ _ (Just szs))) | length szs > 0 = do
--    is <- concatMapM (expandVariadicExpr l) szs
--    foldr0M (indexExpr 1) (multiplyIndexExprs l) is
--typeSize l (ComplexT (CVar v@(nonTok -> True))) = do
--    t <- resolveCVar l v
--    typeSize l (ComplexT t)
typeSize l (VAType t sz) = return sz
typeSize l t = genTcError (locpos l) $ text "No static size for type" <+> quotes (pp t)

toMultisetType :: ProverK loc m => loc -> Type -> TcM m ComplexType
toMultisetType l (ComplexT (CVar v@(nonTok -> False) isNotVoid)) = return $ CVar v isNotVoid
toMultisetType l t@(ComplexT (CVar v@(nonTok -> True) isNotVoid)) = do
    mb <- tryResolveCVar l v
    ct' <- case mb of
        Just ct' -> return ct'
        Nothing -> if isNotVoid
            then expandCTypeVar l v
            else throwTcError $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "to convert to multiset" <+> pp t) Nothing
    toMultisetType l $ ComplexT ct'
toMultisetType l (ComplexT (CType s b d)) = do
    tcCstrM_ l $ Unifies (IdxT d) (IdxT $ indexExpr 1)
    return $ CType s (MSet b) (indexExpr 0)
toMultisetType l t = genTcError (locpos l) $ text "cannot convert type" <+> pp t <+> text "to multiset"

defaultExpr :: ProverK loc m => loc -> Type -> Maybe [(Expr,IsVariadic)] -> TcM m Expr
defaultExpr l t@(BaseT b) szs = defaultBaseExpr l Public b
defaultExpr l t@(ComplexT (CVar v _)) szs = do
    c <- resolveCVar l v
    defaultExpr l (ComplexT c) szs
defaultExpr l t@(ComplexT ct@(CType s b d)) szs = do
    mbd <- tryError $ evaluateIndexExpr l d
    case mbd of
        Right 0 -> defaultBaseExpr l s b
        Right n -> do
            let ct1 = CType s b $ indexExpr 1
            case szs of
                Nothing -> do
                    let arr = ArrayConstructorPExpr (ComplexT ct) []
                    case n of
                        1 -> return arr
                        otherwise -> do
                            let ns = replicate (fromInteger $ toInteger n) (indexExpr 0,False)
                            reshapeExpr l False arr ns (ComplexT ct)
                Just ns -> do 
                    bdef <- defaultBaseExpr l s b
                    sz1 <- multiplyIndexVariadicExprs l False ns
                    rep <- repeatExpr l False bdef (Just sz1) ct1
                    case n of
                        1 -> return rep
                        otherwise -> reshapeExpr l False rep ns (ComplexT ct)
        Left err -> throwTcError $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "failed to generate default value for type" <+> pp t) (Just err)
defaultExpr l t szs = throwTcError $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "unsupported default value for type" <+> pp t) Nothing

defaultBaseExpr :: ProverK loc m => loc -> SecType -> BaseType -> TcM m Expr
defaultBaseExpr l s b@(BVar v) = do
    b' <- resolveBVar l v
    defaultBaseExpr l s b'
defaultBaseExpr l s b@(TyPrim p) | isIntPrimType p = defaultBaseClassify l s $ intExpr (BaseT b) 0
defaultBaseExpr l s b@(TyPrim p) | isFloatPrimType p = defaultBaseClassify l s $ floatExpr (BaseT b) 0
defaultBaseExpr l s b@(TyPrim (DatatypeBool _)) = defaultBaseClassify l s $ falseExpr
defaultBaseExpr l s b@(TyPrim (DatatypeString _)) = defaultBaseClassify l s $ stringExpr "\"\""
defaultBaseExpr l s b@(MSet _) = return $ MultisetConstructorPExpr (ComplexT $ CType s b $ indexExpr 0) []
--defaultBaseExpr l s b@(TApp tn@(TypeName _ sn) targs (DVar v)) = do
--    dec <- resolveDVar l v
--    defaultBaseExpr l s $ TApp tn targs dec
defaultBaseExpr l Public b@(TApp (TypeName _ sn) targs sdec) = do
--    StructType _ _ (Just atts) cl <- structBody l dec
    let ct = BaseT b
    (pdec,[]) <- pDecCstrM l False False (Left sn) (Just targs) [] ct
    targs' <- mapM (\(x,y) -> liftM ((,y) . fmap typed) $ type2TemplateTypeArgument l x) targs
    let targs'' = if null targs' then Nothing else Just targs'
    return $ ProcCallExpr ct (fmap (const $ DecT pdec) $ ProcedureName () sn) targs'' []
defaultBaseExpr l s b = genError (locpos l) $ text "defaultBaseExpr:" <+> pp s <+> pp b

defaultBaseClassify :: ProverK loc m => loc -> SecType -> Expr -> TcM m Expr
defaultBaseClassify l Public e = return e
defaultBaseClassify l s@(Private {}) e@(loc -> BaseT b) = classifyExpr l False e (CType s b $ indexExpr 0)
defaultBaseClassify l s@(SVar v k) e@(loc -> BaseT b) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s' -> defaultBaseClassify l s' e
        Nothing -> if isPrivateKind k
            then classifyExpr l False e (CType s b $ indexExpr 0)
            else throwTcError $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "failed to generate default value for base" <+> pp s <+> ppExprTy e) Nothing
defaultBaseClassify l s e = throwTcError $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "failed to generate default value for base" <+> pp s <+> ppExprTy e) Nothing
