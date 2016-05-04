{-# LANGUAGE TupleSections, FlexibleContexts, ViewPatterns #-}

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

isBoolTypeM :: (ProverK loc m) => loc -> Type -> TcM m Bool
isBoolTypeM l t | isBoolType t = return True
isBoolTypeM l t = liftM isBoolBaseType (typeToBaseType l t) `mplus` return False

isIntTypeM :: (ProverK loc m) => loc -> Type -> TcM m Bool
isIntTypeM l t | isIntType t = return True
isIntTypeM l t = liftM isIntBaseType (typeToBaseType l t) `mplus` return False

castTypeToType :: CastType VarIdentifier Type -> Type
castTypeToType (CastPrim p) = BaseT $ TyPrim $ funit p
castTypeToType (CastTy (TypeName t n)) = t

typeToSecType :: (ProverK loc m) => loc -> Type -> TcM m SecType
typeToSecType l (SecT s) = return s
typeToSecType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp $ SType AnyKind)

typeToDecType :: (ProverK loc m) => loc -> Type -> TcM m DecType
typeToDecType l (DecT s) = return s
typeToDecType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp DType)

typeToVArrayType :: (ProverK loc m) => loc -> Type -> SExpr VarIdentifier Type -> TcM m VArrayType
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
    (CType s b d _) -> catchError
        (newErrorM $ prove l "typeToBaseType" $ tcCstrM l (Equals t (ComplexT $ CType Public b (indexSExpr 0) Nothing)) >> return b)
        (\err -> ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType))
    CVar v -> resolveBVar l v
    otherwise -> ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)
typeToBaseType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)

typeToComplexType :: (ProverK loc m) => loc -> Type -> TcM m ComplexType
typeToComplexType l (ComplexT s) = return s
typeToComplexType l (BaseT s) = return $ defCType s
typeToComplexType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp TType)

tcCastType :: (MonadIO m,Location loc) => CastType Identifier loc -> TcM m (CastType VarIdentifier (Typed loc))
tcCastType (CastPrim p) = do
    liftM CastPrim $ tcPrimitiveDatatype p
tcCastType (CastTy v) = do
    liftM CastTy $ tcTypeName v

tcTypeName :: (MonadIO m,Location loc) => TypeName Identifier loc -> TcM m (TypeName VarIdentifier (Typed loc))
tcTypeName v@(TypeName l n) = do
    let n' = mkVarId n
    t <- checkNonTemplateType (TypeName l n')
    return $ TypeName (Typed l t) n'

tcTypeSpec :: (ProverK loc m) => TypeSpecifier Identifier loc -> IsVariadic -> TcM m (TypeSpecifier VarIdentifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) isVariadic = do
    (sec',tsec) <- tcMbSecType sec 
    (dta') <- tcDatatypeSpec dta
    let tdta = typed $ loc dta'
    (dim',tdim) <- tcMbDimtypeSpec (pp tsec <+> pp tdta) dim
    t <- buildTypeSpec l tsec tdta (fmap typed tdim) isVariadic
    return (TypeSpecifier (Typed l t) sec' dta' dim')
    
buildTypeSpec :: (ProverK loc m) => loc -> Type -> Type -> SExpr VarIdentifier Type -> IsVariadic -> TcM m Type
buildTypeSpec l tsec tdta tdim True = do
    tsecs <- if isVATy (tyOf tsec) then expandVariadicType l (tsec,True) else return [tsec]
    tdtas <- if isVATy (tyOf tdta) then expandVariadicType l (tdta,True) else return [tdta]
    tdims <- if isVATy (loc tdim) then expandVariadicExpr l (tdim,True) else return [tdim]
    tzips <- zipCTypeArgs l tsecs tdtas tdims
    ts <- forM tzips $ \(s,b,dim) -> buildTypeSpec l s b dim False
    case ts of
        [t] -> do
            sz <- newSizeVar Nothing
            return $ VAType t sz
        otherwise -> return $ VArrayT $ VAVal ts TType
buildTypeSpec l tsec tdta dim False = do
    ts <- typeToSecType l tsec
    td <- typeToBaseType l tdta
    dim' <- tcExprTy' (BaseT index) $ fmap (Typed l) dim
    let ct = CType ts td (fmap typed dim') Nothing
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
    t <- checkDomain vd
    let d' = fmap (flip Typed t) vd
    return $ PrivateSpecifier (Typed l t) d'

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
    tcTopCstrM l $ TDec (funit vn) ts dec
    let ret = TApp (funit vn) ts dec
    let n' = fmap (flip Typed (DecT dec)) vn
    return $ TemplateSpecifier (Typed l $ BaseT ret) n' args'
tcDatatypeSpec (VariableSpecifier l (TypeName nl n)) = do
    let n' = mkVarId n
    t <- checkNonTemplateType (TypeName nl n')  
    let v' = TypeName (Typed nl t) n'
    return $ VariableSpecifier (Typed l t) v'

tcPrimitiveDatatype :: (MonadIO m,Location loc) => PrimitiveDatatype loc -> TcM m (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = BaseT $ TyPrim $ funit p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: (ProverK loc m) => TemplateTypeArgument Identifier loc -> TcM m (TemplateTypeArgument VarIdentifier (Typed loc))
tcTemplateTypeArgument (GenericTemplateTypeArgument l n) = do
    n' <- checkTemplateArg (bimap mkVarId id n)
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
    e' <- tcExpr e
    let t = IdxT (fmap typed e')
    return $ ExprTemplateTypeArgument (Typed l t) e'
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = SecT $ Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: (ProverK loc m) => Doc -> Maybe (DimtypeSpecifier Identifier loc) -> TcM m (Maybe (DimtypeSpecifier VarIdentifier (Typed loc)),SExpr VarIdentifier (Typed loc))
tcMbDimtypeSpec doc Nothing = return (Nothing,(indexSExprLoc 0)) -- 0 by default
tcMbDimtypeSpec doc (Just dim) = do
    (dim',t) <- tcDimtypeSpec doc dim
    return (Just dim',t)

tcDimtypeSpec :: (ProverK loc m) => Doc -> DimtypeSpecifier Identifier loc -> TcM m (DimtypeSpecifier VarIdentifier (Typed loc),SExpr VarIdentifier (Typed loc))
tcDimtypeSpec doc (DimSpecifier l e) = do
    e' <- tcExpr e -- we don't commit to a type yet
    return (DimSpecifier (notTyped "tcDimtypeSpec" l) e',e') 

tcRetTypeSpec :: (ProverK loc m) => ReturnTypeSpecifier Identifier loc -> TcM m (ReturnTypeSpecifier VarIdentifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing Nothing) = do
    let t = Void
    return $ ReturnType (Typed l $ ComplexT Void) Nothing Nothing
tcRetTypeSpec (ReturnType l (Just t) sz) = do
    t' <- tcTypeSpec t False
    let ty = typed $ loc t'
    (ty',sz') <- tcTypeSizes l ty sz
    return (ReturnType (Typed l ty') (Just t') sz')

-- | Retrieves a constant dimension from a type
typeDim :: (ProverK loc m) => loc -> Type -> TcM m (SExpr VarIdentifier Type)
typeDim l (BaseT _) = return $ indexSExpr 0
typeDim l (ComplexT (CType _ _ e _)) = return e
typeDim l (VAType _ _) = return $ indexSExpr 1
typeDim l t = genTcError (locpos l) $ text "No dimension for type" <+> pp t

projectMatrixType :: (ProverK loc m) => loc -> Type -> [ArrayProj] -> TcM m Type
projectMatrixType l (ComplexT ct) rngs = liftM ComplexT $ projectMatrixCType l ct rngs
    where
    projectMatrixCType l ct@(CType sec t dim sz) rngs = do
        (dim'') <- projectSizes l ct 1 dim rngs  
        return $ CType sec t dim'' Nothing
    projectMatrixCType l (CVar v) rngs = do
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

projectSizes :: (ProverK loc m) => loc -> ComplexType -> Word64 -> SExpr VarIdentifier Type -> [ArrayProj] -> TcM m (SExpr VarIdentifier Type)
projectSizes p ct i dim ys = do
    n <- evaluateIndexExpr p =<< typeDim p (ComplexT ct)
    (r) <- projectSizes' p ct i n ys
    return (indexSExpr r)
  where
    projectSizes' p ct i dim [] = return (dim)
    projectSizes' p ct i 0 ys = tcError (locpos p) $ MismatchingArrayDimension (pp ct) (pp $ pred i + toEnum (length ys)) Nothing
    projectSizes' p ct i dim (ArrayIdx y:ys) = do -- project the dimension
        projectSize p (ComplexT ct) i Nothing y y
        projectSizes' p ct (succ i) (pred dim) ys
    projectSizes' p ct i dim (ArraySlice y1 y2:ys) = do -- narrow the dimension
        projectSize p (ComplexT ct) i Nothing y1 y2
        (dim') <- projectSizes' p ct (succ i) dim ys
        return (dim')

projectSize :: (ProverK loc m) => loc -> Type -> Word64 -> Maybe (SExpr VarIdentifier Type) -> ArrayIndex -> ArrayIndex -> TcM m (Maybe (SExpr VarIdentifier Type))
projectSize p t i Nothing y1 y2 = return Nothing
projectSize p t i (Just x) y1 y2 = do
    let low = case y1 of
                NoArrayIndex -> DynArrayIndex $ indexSExpr 0
                i -> i
    let upp = case y2 of
                NoArrayIndex -> DynArrayIndex x
                i -> i
    let arrerr = GenericError (locpos p) $ text "Unknown"
    let elow = arrayIndexSExpr low
    let eupp = arrayIndexSExpr upp
    case (low,upp) of
        (DynArrayIndex el,DynArrayIndex eu) -> do
            liftM Just $ subtractIndexExprs p eupp elow
        otherwise -> do
            errWarn $ TypecheckerError (locpos p) $ UncheckedRangeSelection (pp t) i (pp elow <> char ':' <> pp eupp) arrerr
            liftM Just $ subtractIndexExprs p eupp elow          

structBody :: (ProverK loc m) => loc -> DecType -> TcM m Type
structBody l d@(DecType _ _ _ _ _ _ _ _ b) | not (isTemplateDecType d) = structBody l b
structBody l s@(StructType {}) = return $ DecT s
structBody l (DVar v) = resolveDVar l v >>= structBody l
structBody l d = genTcError (locpos l) $ text "structBody" <+> pp d

-- | checks that a given type is a struct type, resolving struct templates if necessary, and projects a particular field.
projectStructField :: (ProverK loc m) => loc -> BaseType -> AttributeName VarIdentifier () -> TcM m Type
projectStructField l t@(TyPrim {}) a = tcError (locpos l) $ FieldNotFound (pp t) (pp a)
projectStructField l t@(BVar _) a = tcError (locpos l) $ Halt $ FieldNotFound (pp t) (pp a)
projectStructField l (TApp _ _ d) a = do
    DecT r <- structBody l d
    projectStructFieldDec l r a
    
projectStructFieldDec :: (ProverK loc m) => loc -> DecType -> AttributeName VarIdentifier () -> TcM m Type
projectStructFieldDec l t@(StructType _ _ atts) (AttributeName _ a) = do -- project the field
    case List.find (\(Cond (Attribute _ t f _) c) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound (pp t) (pp a)
        Just (Cond (Attribute _ t f _) c) -> do
            case c of
                Nothing -> return ()
                Just k -> tcCstrM l $ IsValid True k
            return $ typeSpecifierLoc t 

-- | Typechecks the sizes of a matrix and appends them to a given complex type.
tcTypeSizes :: (ProverK loc m) => loc -> Type -> Maybe (Sizes Identifier loc) -> TcM m (Type,Maybe (Sizes VarIdentifier (Typed loc)))
tcTypeSizes l ty szs = do
    (szs') <- mapM (tcSizes l) szs
    let tszs' = fmap (fmap typed) szs'
    ty' <- refineTypeSizes l ty tszs'
    return (ty',szs')

variadicExprsLength :: (ProverK loc m) => loc -> [(SExpr VarIdentifier Type,IsVariadic)] -> TcM m (SExpr VarIdentifier Type)
variadicExprsLength l [] = return $ indexSExpr 0
variadicExprsLength l es = mapM (variadicExprLength l) es >>= foldr0M (indexSExpr 0) (sumIndexExprs l)
    where
    variadicExprLength :: (ProverK loc m) => loc -> (SExpr VarIdentifier Type,IsVariadic) -> TcM m (SExpr VarIdentifier Type)
    variadicExprLength l (e,False) = return $ indexSExpr 1
    variadicExprLength l (e,True) = do
        let t = loc e
        case t of
            VAType _ sz -> return sz
            VArrayT (VAVal ts _) -> return $ indexSExpr $ toEnum $ length ts
            VArrayT (VAVar v _ sz) -> return sz
            otherwise -> genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)

--evalVarExprs :: (ProverK loc m) => loc -> [(SExpr VarIdentifier Type,IsVariadic)] -> TcM m ()
--evalVarExprs l = mapM_ (evalVarExpr l)
--    where
--    evalVarExpr :: (ProverK loc m) => loc -> (SExpr VarIdentifier Type,IsVariadic) -> TcM m ()
--    evalVarExpr l x = do
--        es <- expandVariadicExpr l x
--        mapM_ (evaluateIndexExpr . fmap (Typed l)) es

matchTypeDimension :: (ProverK loc m) => loc -> SExpr VarIdentifier Type -> [(SExpr VarIdentifier Type,IsVariadic)] -> TcM m ()
matchTypeDimension l td szs = addErrorM l (TypecheckerError (locpos l) . Halt . MismatchingArrayDimension (pp td) (pp szs) . Just) $ do
    d <- variadicExprsLength l szs 
    liftIO $ putStrLn $ "matchTypeDim " ++ ppr td ++ " " ++ ppr d
    unifiesExpr l True td d

-- | Update the size of a compound type
-- for variadic arrays, we set the size of each base type and not of the array itself
refineTypeSizes :: (ProverK loc m) => loc -> Type -> Maybe (Sizes VarIdentifier Type) -> TcM m Type
refineTypeSizes l ct@(ComplexT (CType s t d sz)) Nothing = do -- check the generated size
    return ct
refineTypeSizes l ct@(ComplexT (CType s t d sz)) (Just (Sizes szs)) = do -- discard the generated size in detriment of the declared size
    let sz' = Foldable.toList szs
    tcCstrM l $ MatchTypeDimension d sz'
    return $ ComplexT $ CType s t d $ Just sz'
refineTypeSizes l (VArrayT (VAVal ts b)) szs = do
    liftM (VArrayT . flip VAVal b) $ mapM (\t -> refineTypeSizes l t szs) ts
refineTypeSizes l (VArrayT (VAVar v b sz)) szs = do
    b' <- refineTypeSizes l b szs
    return $ VArrayT $ VAVar v b' sz
refineTypeSizes l (VAType b sz) szs = do
    b' <- refineTypeSizes l b szs
    return $ VAType b' sz
refineTypeSizes l ct _ = genTcError (locpos l) $ text "Failed to add type size" <+> pp ct
    
typeBase :: (ProverK loc m) => loc -> Type -> TcM m Type
typeBase l (BaseT b) = return $ BaseT b
typeBase l (ComplexT (CType Public b _ _)) = return $ BaseT b
typeBase l (ComplexT (CType s b _ _)) = return $ ComplexT $ CType s b (indexSExpr 0) Nothing
typeBase l (ComplexT (CVar v)) = do
    ct <- resolveCVar l v
    typeBase l (ComplexT ct)
typeBase l (VAType b sz) = return b
typeBase l t = genTcError (locpos l) $ text "No static base type for type" <+> quotes (pp t)
    
typeSize :: (ProverK loc m) => loc -> Type -> TcM m (SExpr VarIdentifier Type)
typeSize l (BaseT _) = return $ indexSExpr 1
typeSize l (ComplexT (CType _ _ _ (Just []))) = return $ indexSExpr 1
typeSize l (ComplexT (CType _ _ _ (Just szs))) | length szs > 0 = do
    is <- concatMapM (expandVariadicExpr l) szs
    foldr0M (indexSExpr 1) (multiplyIndexExprs l) is
typeSize l (ComplexT (CVar v)) = do
    t <- resolveCVar l v
    typeSize l (ComplexT t)
typeSize l (VAType t sz) = return sz
typeSize l t = genTcError (locpos l) $ text "No static size for type" <+> quotes (pp t)



