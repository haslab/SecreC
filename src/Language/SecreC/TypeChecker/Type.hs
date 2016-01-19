{-# LANGUAGE FlexibleContexts #-}

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
import Language.SecreC.TypeChecker.Semantics
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.SMT
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Index

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

isBoolTypeM :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Bool
isBoolTypeM l t | isBoolType t = return True
isBoolTypeM l t = liftM isBoolBaseType (typeToBaseType l t) `mplus` return False

isIntTypeM :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Bool
isIntTypeM l t | isIntType t = return True
isIntTypeM l t = liftM isIntBaseType (typeToBaseType l t) `mplus` return False

castTypeToType :: CastType VarIdentifier Type -> Type
castTypeToType (CastPrim p) = BaseT $ TyPrim $ funit p
castTypeToType (CastTy (TypeName t n)) = t

typeToSecType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m SecType
typeToSecType l (SecT s) = return s
typeToSecType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp $ SType AnyKind)

typeToDecType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m DecType
typeToDecType l (DecT s) = return s
--typeToDecType l (BaseT (TyDec d)) = return d
typeToDecType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp DType)

typeToPrimType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Prim
typeToPrimType l t = do
    b <- typeToBaseType l t
    case b of
        TyPrim p -> return p
        otherwise -> genTcError (locpos l) $ text "not a primitive type" <+> pp t

typeToBaseType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m BaseType
typeToBaseType l (BaseT s) = return s
--typeToBaseType l (DecT d) | isStruct d = return $ TyDec d
typeToBaseType l t@(ComplexT ct) = case ct of
    (CType s b d sz) -> catchError
        (newErrorM $ prove l True $ equals l t (ComplexT $ CType Public b (indexSExpr 0) []) >> return b)
        (\err -> ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType))
    CVar _ -> ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)
    otherwise -> ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)
typeToBaseType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp BType)

typeToComplexType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m ComplexType
typeToComplexType l (ComplexT s) = return s
typeToComplexType l (BaseT s) = return $ defCType s
typeToComplexType l t = ppM l t >>= tcError (locpos l) . TypeConversionError (pp TType)

tcCastType :: (MonadIO m,Location loc) => CastType Identifier loc -> TcM loc m (CastType VarIdentifier (Typed loc))
tcCastType (CastPrim p) = do
    liftM CastPrim $ tcPrimitiveDatatype p
tcCastType (CastTy v) = do
    liftM CastTy $ tcTypeName v

tcTypeName :: (MonadIO m,Location loc) => TypeName Identifier loc -> TcM loc m (TypeName VarIdentifier (Typed loc))
tcTypeName v@(TypeName l n) = do
    let n' = mkVarId n
    t <- checkNonTemplateType (TypeName l n')
    return $ TypeName (Typed l t) n'

tcTypeSpec :: (VarsIdTcM loc m,Location loc) => TypeSpecifier Identifier loc -> TcM loc m (TypeSpecifier VarIdentifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) = do
    (sec',tsec) <- tcMbSecTypeSpec sec 
    (dta',tdta) <- tcDatatypeSpecBase dta
    (dim',tdim) <- tcMbDimtypeSpec (pp tsec <+> pp tdta) dim
    let t = ComplexT $ CType tsec tdta (fmap typed tdim) [] -- return type without array sizes
    return $ TypeSpecifier (Typed l t) sec' dta' dim'
    
tcMbSecTypeSpec :: (VarsIdTcM loc m,Location loc) => Maybe (SecTypeSpecifier Identifier loc) -> TcM loc m (Maybe (SecTypeSpecifier VarIdentifier (Typed loc)),SecType)
tcMbSecTypeSpec Nothing = return (Nothing,Public) -- public by default
tcMbSecTypeSpec (Just sec) = do
    sec' <- tcSecTypeSpec sec
    let t = typed $ loc sec'
    s <- typeToSecType (unTyped $ loc sec') t
    return (Just sec',s)

tcSecTypeSpec :: (VarsIdTcM loc m,Location loc) => SecTypeSpecifier Identifier loc -> TcM loc m (SecTypeSpecifier VarIdentifier (Typed loc))
tcSecTypeSpec (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l $ SecT Public)
tcSecTypeSpec (PrivateSpecifier l d) = do
    let vd = bimap mkVarId id d
    t <- checkDomain vd
    let d' = fmap (flip Typed t) vd
    return $ PrivateSpecifier (Typed l t) d'

tcDatatypeSpecBase :: (VarsIdTcM loc m,Location loc) => DatatypeSpecifier Identifier loc -> TcM loc m (DatatypeSpecifier VarIdentifier (Typed loc),BaseType)
tcDatatypeSpecBase d = do
    d' <- tcDatatypeSpec d
    let tdta = typed $ loc d'
    t <- typeToBaseType (unTyped $ loc d') tdta
    return (d',t)

tcDatatypeSpec :: (VarsIdTcM loc m,Location loc) => DatatypeSpecifier Identifier loc -> TcM loc m (DatatypeSpecifier VarIdentifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let ts = map (typed . loc) args'
    let vn = bimap mkVarId id n
    dec <- newDecVar
    tcTopCstrM l $ TDec (funit vn) ts dec
    ret <- newBaseTyVar
    tcTopCstrM l $ TRet dec (BaseT ret)
    let n' = fmap (flip Typed (DecT dec)) vn
    return $ TemplateSpecifier (Typed l $ BaseT ret) n' args'
tcDatatypeSpec (VariableSpecifier l (TypeName nl n)) = do
    let n' = mkVarId n
    t <- checkNonTemplateType (TypeName nl n')  
    let v' = TypeName (Typed nl t) n'
    return $ VariableSpecifier (Typed l t) v'

tcPrimitiveDatatype :: (MonadIO m,Location loc) => PrimitiveDatatype loc -> TcM loc m (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = BaseT $ TyPrim $ funit p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: (VarsIdTcM loc m,Location loc) => TemplateTypeArgument Identifier loc -> TcM loc m (TemplateTypeArgument VarIdentifier (Typed loc))
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
    ie <- tryExpr2IExpr e'
    let t = IdxT (fmap (typed) e')
    return $ ExprTemplateTypeArgument (Typed l t) e'
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = SecT $ Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: (VarsIdTcM loc m,Location loc) => Doc -> Maybe (DimtypeSpecifier Identifier loc) -> TcM loc m (Maybe (DimtypeSpecifier VarIdentifier (Typed loc)),SExpr VarIdentifier (Typed loc))
tcMbDimtypeSpec doc Nothing = return (Nothing,(indexSExprLoc 0)) -- 0 by default
tcMbDimtypeSpec doc (Just dim) = do
    (dim',t) <- tcDimtypeSpec doc dim
    return (Just dim',t)

tcDimtypeSpec :: (VarsIdTcM loc m,Location loc) => Doc -> DimtypeSpecifier Identifier loc -> TcM loc m (DimtypeSpecifier VarIdentifier (Typed loc),SExpr VarIdentifier (Typed loc))
tcDimtypeSpec doc (DimSpecifier l e) = do
    e' <- tcDimExpr doc Nothing e
    return (DimSpecifier (notTyped "tcDimtypeSpec" l) e',e') 

tcRetTypeSpec :: (VarsIdTcM loc m,Location loc) => ReturnTypeSpecifier Identifier loc -> TcM loc m (ReturnTypeSpecifier VarIdentifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing) = do
    let t = Void
    return $ ReturnType (Typed l $ ComplexT Void) Nothing
tcRetTypeSpec (ReturnType l (Just (s,szs))) = do
    s' <- tcTypeSpec s
    ty <- typeToComplexType l $ typed $ loc s'
    (ty',szs') <- tcTypeSizes l ty Nothing szs
    return $ ReturnType (Typed l $ ComplexT ty') (Just (s',szs'))

-- | Retrieves a constant dimension from a type
typeDim :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> TcM loc m (SExpr VarIdentifier Type)
typeDim l ct@(CType _ _ e _) = return e
typeDim l t = genTcError (locpos l) $ text "No dimension for type" <+> pp t

projectMatrixType :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc m ComplexType
projectMatrixType l ct rngs = projectMatrixCType l ct rngs
  where
    projectMatrixCType :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc m ComplexType
    projectMatrixCType l ct@(CType sec t dim szs) rngs = do
        szs' <- resolveSizes l dim szs
        szs'' <- projectSizes l ct 1 szs' rngs  
        return $ CType sec t (indexSExpr $ toEnum $ length szs'') szs''
    projectMatrixCType l (CVar v) rngs = do
        t <- resolveCVar l v
        projectMatrixCType l t rngs

projectSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Word64 -> [SExpr VarIdentifier Type] -> [ArrayProj] -> TcM loc m [SExpr VarIdentifier Type]
projectSizes p ct i xs [] = return xs
projectSizes p ct i [] ys = tcError (locpos p) $ MismatchingArrayDimension (pp ct) (i + toEnum (length ys)) Nothing
projectSizes p ct i (x:xs) (ArrayIdx y:ys) = do
    projectSize p ct i x y y
    projectSizes p ct (succ i) xs ys
projectSizes p ct i (x:xs) (ArraySlice y1 y2:ys) = do
    z <- projectSize p ct i x y1 y2
    zs <- projectSizes p ct (succ i) xs ys
    return (z:zs)

projectSize :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Word64 -> SExpr VarIdentifier Type -> ArrayIndex -> ArrayIndex -> TcM loc m (SExpr VarIdentifier Type)
projectSize p ct i x y1 y2 = do
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
        --(StaticArrayIndex l,StaticArrayIndex u,Right sz) ->
        --    if (l >= 0 && u >= 0 && sz >= l && u <= sz)
        --        then return (indexExpr (u - l))
        --        else tcError (locpos p) $ ArrayAccessOutOfBounds (pp ct) i (pp l <> char ':' <> pp u)
        (DynArrayIndex el,DynArrayIndex eu) -> do
            checkCstrM p $ CheckArrayAccess ct i el eu x
            subtractIndexExprs p eupp elow
        otherwise -> do
            errWarn $ TypecheckerError (locpos p) $ UncheckedRangeSelection (pp ct) i (pp elow <> char ':' <> pp eupp) arrerr
            subtractIndexExprs p eupp elow          

-- | checks that a given type is a struct type, resolving struct templates if necessary, and projects a particular field.
projectStructField :: (VarsIdTcM loc m,Location loc) => loc -> BaseType -> AttributeName VarIdentifier () -> TcM loc m Type
projectStructField l t@(TyPrim {}) a = tcError (locpos l) $ FieldNotFound (pp t) (pp a)
projectStructField l t@(BVar _) a = tcError (locpos l) $ Halt $ FieldNotFound (pp t) (pp a)
projectStructField l (TyDec d) a = projectStructFieldDec l d a
    
projectStructFieldDec :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> AttributeName VarIdentifier () -> TcM loc m Type
projectStructFieldDec l t@(StructType _ _ _ atts) (AttributeName _ a) = do -- project the field
    case List.find (\(Cond (Attribute _ t f) c) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound (pp t) (pp a)
        Just (Cond (Attribute _ t f) c) -> do
            case c of
                Nothing -> return ()
                Just k -> tcCstrM l $ IsValid k
            return $ typeSpecifierLoc t

resolveSizes :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> [SExpr VarIdentifier Type] -> TcM loc m [SExpr VarIdentifier Type]
resolveSizes l d [] = do
    i <- evaluateIndexExpr $ fmap (Typed l) d
    replicateM (fromEnum i) newSizeVar
resolveSizes l d xs = return xs

isZeroTypeExpr :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> TcM loc m Bool
isZeroTypeExpr l e = do
    let e' = fmap (Typed l) e
    mb <- tryEvaluateIndexExpr e'
    case mb of
        Right 0 -> return True
        otherwise -> return False     

tcTypeSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Maybe (VarName Identifier loc) -> Maybe (Sizes Identifier loc) -> TcM loc m (ComplexType,Maybe (Sizes VarIdentifier (Typed loc)))
tcTypeSizes l ty v szs = do
    szs' <- mapM (tcSizes l ty v) szs
    let tszs' = fmap (fmap typed) szs'
    ty' <- refineTypeSizes l ty tszs'
    return (ty',szs')
    
matchTypeDimension :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Word64 -> TcM loc m ()
matchTypeDimension l t d = addErrorM l (TypecheckerError (locpos l) . MismatchingArrayDimension (pp t) d . Just) $ do
    td <- typeDim l t
    i <- expr2IExpr $ fmap (Typed l) td
    isValid l $ i .==. IInt (toInteger d)

-- | Update the size of a compound type
refineTypeSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Maybe (Sizes VarIdentifier Type) -> TcM loc m ComplexType
refineTypeSizes l ct@(CType s t d sz) Nothing = do
    return ct
refineTypeSizes l ct@(CType s t d []) (Just (Sizes szs)) = do
--    unifiesSizes l d sz d tsz
    return $ CType s t d $ Foldable.toList szs
refineTypeSizes l ct _ = genTcError (locpos l) $ text "Expected a complex type but found" <+> pp ct
    
checkIndex :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> TcM loc m ()
checkIndex l e = addErrorM l (TypecheckerError (locpos l) . NonPositiveIndexExpr (pp e)) $ orWarn_ $ do
    ie <- expr2IExpr $ fmap (Typed l) e
    isValid l $ ie .>=. IInt 0

checkArrayAccess :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Word64 -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
checkArrayAccess l t d low up sz = addErrorM l (TypecheckerError (locpos l) . UncheckedRangeSelection (pp t) d (pp low <> char ':' <> pp up)) $ orWarn_ $ do
    il <- expr2IExpr $ fmap (Typed l) low
    iu <- expr2IExpr $ fmap (Typed l) up
    isz <- expr2IExpr $ fmap (Typed l) sz
    isValid l $ IAnd [il .>=. IInt 0,iu .>=. IInt 0,isz .>=. il,iu .<=. isz]
    




