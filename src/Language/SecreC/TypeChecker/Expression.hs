{-# LANGUAGE ViewPatterns, FlexibleContexts, DataKinds, TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Semantics
import Language.SecreC.TypeChecker.Index
import Language.SecreC.Vars
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)
import Control.Monad.IO.Class

import Data.Bifunctor
import Data.Monoid
import Data.Either
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Int
import Data.Word

import Text.PrettyPrint

tcGuard :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcGuard e = tcExprTy (BaseT bool) e

tcExpr :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcExpr pe
    let tpe' = typed $ loc pe'
    e' <- tcExpr e
    let te' = typed $ loc e'
    op' <- tcBinaryAssignOp l op tpe' te'
    return $ BinaryAssign (Typed l tpe') pe' op' e'
tcExpr (QualExpr l e t) = do
    e' <- tcExpr e
    t' <- tcTypeSpec t
    tcTopCstrM l $ Unifies (typed $ loc e') (typed $ loc t')
    return $ QualExpr (Typed l $ typed $ loc t') e' t'
tcExpr (CondExpr l c e1 e2) = do
    c' <- tcGuard c
    k <- tryExpr2ICond c'
    e1' <- withHypotheses LocalScope $ do
        case k of
            Left x -> addHypotheses LocalScope [x]
            otherwise -> return ()
        tcExpr e1
    let t1 = typed $ loc e1'
    e2' <- withHypotheses LocalScope $ do
        case k of
            Left x -> addHypotheses LocalScope [INot x]
            otherwise -> return ()
        tcExpr e2
    let t2 = typed $ loc e2'
    t3 <- newTyVar
    tcTopCstrM l $ Coerces2 t1 t2 t3
    return $ CondExpr (Typed l t3) c' e1' e2'
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- tcExpr e1
    e2' <- tcExpr e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    top <- tcOp op
    v <- newTyVar
    dec <- newDecVar
    tcTopCstrM l $ PDec (Right $ fmap typed top) Nothing [t1,t2] v dec
    return $ BinaryExpr (Typed l v) e1' (updLoc top (Typed l $ DecT dec)) e2'
tcExpr (PreOp l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    (t',op') <- tcBinaryOp l op t t
    return $ PreOp (Typed l t') op' e'
tcExpr (PostOp l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    (t',op') <- tcBinaryOp l op t t
    return $ PostOp (Typed l t') op' e'
tcExpr (UnaryExpr l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    top <- tcOp op
    case (top,t) of
        (OpCast lcast cast,isLitType -> True) -> do
            b <- typeToBaseType (unTyped lcast) $ typed $ loc cast
            s <- newDomainTyVar AnyKind
            dim <- newDimVar
            let ct = ComplexT $ CType s b dim []
            tcTopCstrM l $ Coerces t ct
            return $ UnaryExpr (Typed l ct) top e'
        otherwise -> do
            v <- newTyVar
            dec <- newDecVar
            tcTopCstrM l $ PDec (Right $ fmap typed top) Nothing [t] v dec
            return $ UnaryExpr (Typed l v) (updLoc top (Typed l $ DecT dec)) e'
tcExpr (DomainIdExpr l s) = do
    s' <- tcSecTypeSpec s
    let t = BaseT index
    return $ DomainIdExpr (Typed l t) s'
tcExpr (StringFromBytesExpr l e) = do
    e' <- tcExprTy (ComplexT bytes) e
    return $ StringFromBytesExpr (Typed l $ BaseT string) e'
tcExpr (BytesFromStringExpr l e) = do
    e' <- tcExprTy (BaseT string) e
    return $ BytesFromStringExpr (Typed l $ ComplexT bytes) e'
tcExpr call@(ProcCallExpr l n@(ProcedureName pl pn) specs es) = do
    let vn = bimap mkVarId id n
    es' <- mapM tcExpr es
    let ts = map (typed . loc) es'
    specs' <- mapM (mapM tcTemplateTypeArgument) specs
    let tspecs = fmap (map (typed . loc)) specs'
    v <- newTyVar
    dec <- newDecVar
    tcTopCstrM l $ PDec (Left $ fmap (const ()) vn) tspecs ts v dec -- we don't know the return type on application
    return $ ProcCallExpr (Typed l v) (fmap (flip Typed (DecT dec)) vn) specs' es'
tcExpr (PostIndexExpr l e s) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    ct <- typeToComplexType l t
    (s',t') <- tcSubscript ct s
    return $ PostIndexExpr (Typed l t') e' s'
tcExpr (SelectionExpr l pe a) = do
    let va = bimap mkVarId id a
    pe' <- tcExpr pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    res <- newTyVar
    tcTopCstrM l $ ProjectStruct ctpe' (fmap (const ()) va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (notTyped "tcExpr") va)
tcExpr (ArrayConstructorPExpr l es) = do
    es' <- mapM tcExpr es
    let es'' = fmap (fmap typed) es'
    let t = ComplexT $ ArrayLit es''
    return $ ArrayConstructorPExpr (Typed l t) es'
tcExpr (RVariablePExpr l v) = do
    v' <- tcVarName v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcExpr (LitPExpr l lit) = do
    lit' <- tcLiteral lit
    let tlit = typed $ loc lit'
    return $ LitPExpr (Typed l tlit) lit'

tcBinaryAssignOp :: (VarsTcM loc,Location loc) => loc -> BinaryAssignOp loc -> Type -> Type -> TcM loc (BinaryAssignOp (Typed loc))
tcBinaryAssignOp l bop t1 t2 = do 
    let mb_op = binAssignOpToOp bop
    dec <- case mb_op of
        Just op -> do
            top <- tcOp $ fmap (const l) op
            dec <- newDecVar
            tcTopCstrM l $ PDec (Right $ fmap typed top) Nothing [t1,t2] t1 dec
            return $ DecT dec
        Nothing -> do
            tcTopCstrM l $ Coerces t2 t1
            return $ NoType "tcBinaryAssignOp"
    return (fmap (flip Typed dec) bop)
    
tcBinaryOp :: (VarsTcM loc,Location loc) => loc -> Op Identifier loc -> Type -> Type -> TcM loc (Type,Op VarIdentifier (Typed loc))
tcBinaryOp l op t1 t2 = do 
    top <- tcOp op
    v <- newTyVar
    dec <- newDecVar
    tcTopCstrM l $ PDec (Right $ fmap typed top) Nothing [t1,t2] v dec
    return (v,updLoc top (Typed l $ DecT dec))

tcOp :: (VarsTcM loc,Location loc) => Op Identifier loc -> TcM loc (Op VarIdentifier (Typed loc))
tcOp (OpCast l t) = do
    t' <- tcCastType t
    return $ OpCast (notTyped "tcOp" l) t'
tcOp op = return $ bimap mkVarId (notTyped "tcOp") op

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: (VarsTcM loc,Location loc) => ComplexType -> Subscript Identifier loc -> TcM loc (Subscript VarIdentifier (Typed loc),Type)
tcSubscript t s = do
    let l = loc s
    (s',rngs) <- mapAndUnzipM tcIndex s
    ComplexT ret <- newTyVar
    tcTopCstrM l $ ProjectMatrix t (Foldable.toList rngs) ret
    return (s',ComplexT ret)

tcIndex :: (VarsTcM loc,Location loc) => Index Identifier loc -> TcM loc (Index VarIdentifier (Typed loc),ArrayProj)
tcIndex (IndexInt l e) = do
    ((e'),mb) <- tcIndexExpr e
    ei <- case mb of
                Left err -> do
                    return $ DynArrayIndex (fmap typed e') err
                Right i -> return $ StaticArrayIndex i
    return (IndexInt (notTyped "tcIndex" l) e',ArrayIdx ei)
tcIndex (IndexSlice l e1 e2) = do
    let f x = case x of
                Nothing -> return (Nothing,NoArrayIndex)
                Just ((y),Left err) -> do
                    return (Just y,DynArrayIndex (fmap typed y) err)
                Just ((y),Right i) -> return (Just y,StaticArrayIndex i)
    (e1',mb1) <- f =<< mapM tcIndexExpr e1
    (e2',mb2) <- f =<< mapM tcIndexExpr e2
    return (IndexSlice (notTyped "tcIndex" l) e1' e2',ArraySlice mb1 mb2)

tcLiteral :: Location loc => Literal loc -> TcM loc (Literal (Typed loc))
tcLiteral (IntLit l i) = do
    let lit = IntLit () i
--    v <- newTyVar
--    tcTopCstrM l $ Coerces (ComplexT $ TyLit lit) v
--    return $ IntLit (Typed l v) i
    return $ IntLit (Typed l $ ComplexT $ TyLit lit) i
tcLiteral (StringLit l s) = do
    let lit = StringLit () s
    --v <- newTyVar
    --tcTopCstrM l $ Coerces (ComplexT $ TyLit lit) v
    --return $ StringLit (Typed l v) s
    return $ StringLit (Typed l $ ComplexT $ TyLit lit) s
tcLiteral (BoolLit l b) = do
    let lit = BoolLit () b
    --v <- newTyVar
    --tcTopCstrM l $ Coerces (ComplexT $ TyLit lit) v
    --return $ BoolLit (Typed l v) b
    return $ BoolLit (Typed l $ ComplexT $ TyLit lit) b
tcLiteral (FloatLit l f) = do
    let lit = FloatLit () f
    --v <- newTyVar
    --tcTopCstrM l $ Coerces (ComplexT $ TyLit lit) v
    --return $ FloatLit (Typed l v) f
    return $ FloatLit (Typed l $ ComplexT $ TyLit lit) f

tcVarName :: Location loc => VarName Identifier loc -> TcM loc (VarName VarIdentifier (Typed loc))
tcVarName v@(VarName l n) = do
    t <- checkVariable LocalScope $ bimap mkVarId id v
    return $ VarName (Typed l t) $ mkVarId n

-- | returns the operation performed by a binary assignment operation
binAssignOpToOp :: BinaryAssignOp loc -> Maybe (Op Identifier ())
binAssignOpToOp (BinaryAssignEqual _) = Nothing
binAssignOpToOp (BinaryAssignMul _) = Just $ OpMul ()
binAssignOpToOp (BinaryAssignDiv _) = Just $ OpDiv ()
binAssignOpToOp (BinaryAssignMod _) = Just $ OpMod ()
binAssignOpToOp (BinaryAssignAdd _) = Just $ OpAdd ()
binAssignOpToOp (BinaryAssignSub _) = Just $ OpSub ()
binAssignOpToOp (BinaryAssignAnd _) = Just $ OpBand ()
binAssignOpToOp (BinaryAssignOr _)  = Just $ OpBor ()
binAssignOpToOp (BinaryAssignXor _) = Just $ OpXor ()

-- | typechecks an expression and tries to evaluate it to an index
tcIndexExpr :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (SExpr VarIdentifier (Typed loc),Either SecrecError Word64)
tcIndexExpr e = do
    e' <- tcExprTy (BaseT index) e
    addErrorM (OrWarn . TypecheckerError (locpos $ loc e) . NonPositiveIndexExpr (pp e)) $ orWarn $ do
        ie <- expr2IExpr e'
        tcCstrM (loc e) $ IsValid $ ie .>=. IInt 0
    mb <- tryEvaluateIndexExpr e'
    return (e',mb)

tcExprTy :: (VarsTcM loc,Location loc) => Type -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let Typed l ty' = loc e'
    tcTopCstrM l $ Coerces ty' ty
    return e'

tcDimExpr :: (VarsTcM loc,Location loc) => Doc -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (SExpr VarIdentifier (Typed loc))
tcDimExpr doc v sz = do
    (sz',mb) <- tcIndexExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcTopCstrM (loc sz) $ Unifies ty (BaseT index)
    -- check if size is static and if so evaluate it
--    case mb of
--        Left err -> tcWarn (locpos $ loc sz') $ DependentMatrixDimension doc (pp sz') (fmap pp v) err
--        Right _ -> return ()
    return (sz')     
    
tcSizeExpr :: (VarsTcM loc,Location loc) => ComplexType -> Word64 -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (SExpr VarIdentifier (Typed loc))
tcSizeExpr t i v sz = do
    (sz',mb) <- tcIndexExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcTopCstrM (loc sz) $ Unifies ty (BaseT index)
    -- check if size is static and if so evaluate it
--    case mb of
--        Left err -> tcWarn (locpos $ loc sz') $ DependentMatrixSize (pp t) i (pp sz') (fmap pp v) err
--        Right _ -> return ()
    return (sz')     

tcSizes :: (VarsTcM loc,Location loc) => loc -> ComplexType -> Maybe (VarName Identifier loc) -> Maybe Word64 -> Sizes Identifier loc -> TcM loc (Sizes VarIdentifier (Typed loc))
tcSizes l ty (Just v) Nothing (szs) = tcError (locpos l) $ NoDimensionForMatrixInitialization (varNameId v)
tcSizes l ty v (Just d) (Sizes szs) = do
    -- check array's dimension
    let ds = toEnum (lengthNe szs)
    unless (d == ds) $ tcError (locpos l) $ MismatchingArrayDimension (pp ty) d ds $ Right (fmap pp v,parens $ sepBy comma $ map pp $ Foldable.toList szs)
    szs' <- mapM (\(i,x) -> tcSizeExpr ty i v x) (zip [1..] $ Foldable.toList szs)
    return $ Sizes $ fromListNe szs'

subtractIndexExprs :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc (Expression VarIdentifier Type)
subtractIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr l1 $ IntLit l2 (i1 - i2)
subtractIndexExprs l e1 e2 = do
    dec <- newDecVar
    tcCstrM l $ PDec (Right $ OpSub $ NoType "subtractIndexExprs") Nothing [BaseT index,BaseT index] (BaseT index) dec
    return (BinaryExpr (BaseT index) e1 (OpSub $ DecT dec) e2)
    
landExprs :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc (Expression VarIdentifier Type)
landExprs l e1 e2 = do
    dec <- newDecVar
    tcCstrM l $ PDec (Right $ OpSub $ NoType "landExprs") Nothing [BaseT bool,BaseT bool] (BaseT bool) dec
    return (BinaryExpr (BaseT bool) e1 (OpLand $ DecT dec) e2)

landExprsLoc :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier (Typed loc) -> Expression VarIdentifier (Typed loc) -> TcM loc (Expression VarIdentifier (Typed loc))
landExprsLoc l e1 e2 = do
    dec <- newDecVar
    tcCstrM l $ PDec (Right $ OpSub $ NoType "landExprs") Nothing [BaseT bool,BaseT bool] (BaseT bool) dec
    return (BinaryExpr (Typed l $ BaseT bool) e1 (OpLand $ Typed l $ DecT dec) e2)


