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
import Data.Monoid hiding ((<>))
import Data.Either
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Int
import Data.Word

import Text.PrettyPrint as PP

tcGuard :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))
tcGuard e = tcExprTy (BaseT bool) e

tcLValue :: (VarsIdTcM loc m,Location loc) => Bool -> Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))
tcLValue isCond (PostIndexExpr l e s) = do
    e' <- tcLValue False e
    let t = typed $ loc e'
    ct <- typeToComplexType l t
    (s',t') <- tcSubscript ct s
    return $ PostIndexExpr (Typed l t') e' s'
tcLValue isCond (SelectionExpr l pe a) = do
    let va = bimap mkVarId id a
    pe' <- tcLValue False pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    res <- newTyVar
    tcTopCstrM l $ ProjectStruct ctpe' (funit va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (notTyped "tcLValue") va)
tcLValue isCond (RVariablePExpr l v) = do
    v' <- tcVarName isCond v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcLValue isCond e = genTcError (locpos $ loc e) $ text "Not a l-value expression: " <+> quotes (pp e)

tcExpr :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcLValue True pe
    let tpe' = typed $ loc pe'
    e' <- tcExpr e
    (eres,op') <- tcBinaryAssignOp l op pe' e'
    return $ BinaryAssign (Typed l tpe') pe' op' eres
tcExpr (QualExpr l e t) = do
    e' <- tcExpr e
    t' <- tcTypeSpec t
    tcTopCstrM l $ Unifies (typed $ loc e') (typed $ loc t')
    return $ QualExpr (Typed l $ typed $ loc t') e' t'
tcExpr (CondExpr l c e1 e2) = do
    c' <- tcGuard c
    e1' <- withHypotheses LocalScope $ do
        tryAddHypothesis l LocalScope $ HypCondition $ fmap typed c'
        tcExpr e1
    let t1 = typed $ loc e1'
    e2' <- withHypotheses LocalScope $ do
        tryAddHypothesis l LocalScope $ HypNotCondition $ fmap typed c'
        tcExpr e2
    let t2 = typed $ loc e2'
    t3 <- newTyVar
    x1 <- newTypedVar "then" t3
    x2 <- newTypedVar "else" t3
    tcTopCoerces2CstrM l (fmap typed e1') t1 (fmap typed e2') t2 x1 x2 t3
    let ex1 = fmap (Typed l) $ RVariablePExpr t3 x1
    let ex2 = fmap (Typed l) $ RVariablePExpr t3 x2
    return $ CondExpr (Typed l t3) c' ex1 ex2
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- tcExpr e1
    e2' <- tcExpr e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    top <- tcOp op
    v <- newTyVar
    (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [fmap typed e1',fmap typed e2'] v
    return $ BinaryExpr (Typed l v) (fmap (Typed l) x1) (updLoc top (Typed l $ DecT dec)) (fmap (Typed l) x2)
tcExpr (PreOp l op e) = do
    e' <- tcLValue False e
    let t = typed $ loc e'
    (e'',op') <- tcBinaryOp l op e'
    let t' = typed $ loc e''
    return $ PreOp (Typed l t) op' e''
tcExpr (PostOp l op e) = do
    e' <- tcLValue False e
    let t = typed $ loc e'
    (e'',op') <- tcBinaryOp l op e'
    let t' = typed $ loc e''
    return $ PostOp (Typed l t) op' e''
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
            x <- newTypedVar "cast" ct
            tcTopCoercesCstrM l (fmap typed e') t x ct
            let ex = fmap (Typed l) $ RVariablePExpr ct x
            return $ UnaryExpr (Typed l ct) top ex
        otherwise -> do
            v <- newTyVar
            (dec,[x]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [fmap typed e'] v
            let ex = fmap (Typed l) x
            return $ UnaryExpr (Typed l v) (updLoc top (Typed l $ DecT dec)) ex
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
    (dec,xs) <- tcTopPDecCstrM l True (Left $ funit vn) tspecs (map (fmap typed) es') v
    let exs = map (fmap (Typed l)) xs
    return $ ProcCallExpr (Typed l v) (fmap (flip Typed (DecT dec)) vn) specs' exs
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
    tcTopCstrM l $ ProjectStruct ctpe' (funit va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (notTyped "tcExpr") va)
tcExpr (ArrayConstructorPExpr l es) = do
    es' <- mapM tcExpr es
    let es'' = fmap (fmap typed) es'
    let t = ComplexT $ ArrayLit es''
    return $ ArrayConstructorPExpr (Typed l t) es'
tcExpr (LitPExpr l lit) = do
    lit' <- tcLiteral lit
    return lit'
tcExpr e = tcLValue False e

tcBinaryAssignOp :: (VarsIdTcM loc m,Location loc) => loc -> BinaryAssignOp loc -> Expression VarIdentifier (Typed loc) -> (Expression VarIdentifier (Typed loc)) -> TcM loc m (Expression VarIdentifier (Typed loc),BinaryAssignOp (Typed loc))
tcBinaryAssignOp l bop lv1 e2 = do 
    let t1 = typed $ loc lv1
    let t2 = typed $ loc e2
    let mb_op = binAssignOpToOp bop
    (eres,dec) <- case mb_op of
        Just op -> do
            top <- tcOp $ fmap (const l) op
            (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [fmap typed lv1,fmap typed e2] t1
            let ex2 = fmap (Typed l) x2
            return (ex2,DecT dec)
        Nothing -> do
            x1 <- newTypedVar "assign" t1
            tcTopCoercesCstrM l (fmap typed e2) t2 x1 t1
            let ex1 = fmap (Typed l) $ RVariablePExpr t1 x1
            return (ex1,NoType "tcBinaryAssignOp")
    return (eres,fmap (flip Typed dec) bop)
    
tcBinaryOp :: (VarsIdTcM loc m,Location loc) => loc -> Op Identifier loc -> Expression VarIdentifier (Typed loc) -> TcM loc m (Expression VarIdentifier (Typed loc),Op VarIdentifier (Typed loc))
tcBinaryOp l op e1 = do 
    let t1 = typed $ loc e1
    top <- tcOp op
    let tlit1 = ComplexT $ TyLit $ IntLit () 1
    let elit1 = LitPExpr tlit1 $ IntLit tlit1 1
    (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [fmap typed e1,elit1] t1
    let ex1 = fmap (Typed l) x1
    return (ex1,updLoc top (Typed l $ DecT dec))

tcOp :: (VarsIdTcM loc m,Location loc) => Op Identifier loc -> TcM loc m (Op VarIdentifier (Typed loc))
tcOp (OpCast l t) = do
    t' <- tcCastType t
    return $ OpCast (notTyped "tcOp" l) t'
tcOp op = return $ bimap (mkVarId) (notTyped "tcOp") op

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: (VarsIdTcM loc m,Location loc) => ComplexType -> Subscript Identifier loc -> TcM loc m (Subscript VarIdentifier (Typed loc),Type)
tcSubscript t s = do
    let l = loc s
    (s',rngs) <- mapAndUnzipM tcIndex s
    ComplexT ret <- newTyVar
    tcTopCstrM l $ ProjectMatrix t (Foldable.toList rngs) ret
    return (s',ComplexT ret)

tcIndex :: (VarsIdTcM loc m,Location loc) => Index Identifier loc -> TcM loc m (Index VarIdentifier (Typed loc),ArrayProj)
tcIndex (IndexInt l e) = do
    e' <- tcIndexExpr e
    let ei = DynArrayIndex (fmap typed e')
    return (IndexInt (notTyped "tcIndex" l) e',ArrayIdx ei)
tcIndex (IndexSlice l e1 e2) = do
    let f x = case x of
                Nothing -> return (Nothing,NoArrayIndex)
                Just y -> do
                    return (Just y,DynArrayIndex (fmap typed y))
    (e1',mb1) <- f =<< mapM tcIndexExpr e1
    (e2',mb2) <- f =<< mapM tcIndexExpr e2
    return (IndexSlice (notTyped "tcIndex" l) e1' e2',ArraySlice mb1 mb2)

tcLiteral :: (VarsIdTcM loc m,Location loc) => Literal loc -> TcM loc m (Expression VarIdentifier (Typed loc))
tcLiteral li = do
    let l = loc li
    let lit = ComplexT $ TyLit $ funit li
    let elit = LitPExpr lit $ fmap (const lit) li
    return $ fmap (Typed l) elit

tcVarName :: (MonadIO m,Location loc) => Bool -> VarName Identifier loc -> TcM loc m (VarName VarIdentifier (Typed loc))
tcVarName isCond v@(VarName l n) = checkVariable isCond LocalScope (bimap mkVarId id v)

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

tcIndexCond :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))
tcIndexCond e = tcExprTy (BaseT bool) e

-- | typechecks an expression and tries to evaluate it to an index
tcIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))
tcIndexExpr e = do
    e' <- tcExprTy (BaseT index) e
    return e'

tcExprTy :: (VarsIdTcM loc m,Location loc) => Type -> Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let Typed l ty' = loc e'
    tcTopCstrM l $ Unifies ty' ty
    return e'

tcDimExpr :: (VarsIdTcM loc m,Location loc) => Doc -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))
tcDimExpr doc v sz = do
    sz' <- tcIndexExpr sz
    -- check if size is static and if so evaluate it
--    case mb of
--        Left err -> tcWarn (locpos $ loc sz') $ DependentMatrixDimension doc (pp sz') (fmap pp v) err
--        Right _ -> return ()
    return sz'
    
tcSizeExpr :: (VarsIdTcM loc m,Location loc) => ComplexType -> Word64 -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))
tcSizeExpr t i v sz = do
    sz' <- tcIndexExpr sz
    -- check if size is static and if so evaluate it
--    case mb of
--        Left err -> tcWarn (locpos $ loc sz') $ DependentMatrixSize (pp t) i (pp sz') (fmap pp v) err
--        Right _ -> return ()
    return sz'

tcSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Maybe (VarName Identifier loc) -> Sizes Identifier loc -> TcM loc m (Sizes VarIdentifier (Typed loc))
tcSizes l ty v (Sizes szs) = do
    -- check array's dimension
    let d = toEnum (lengthNe szs)
    tcCstrM l $ MatchTypeDimension ty d
    szs' <- mapM (\(i,x) -> tcSizeExpr ty i v x) (zip [1..] $ Foldable.toList szs)
    return $ Sizes $ fromListNe szs'

subtractIndexExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)
subtractIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr l1 $ IntLit l2 (i1 - i2)
subtractIndexExprs l e1 e2 = do
    (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ OpSub $ NoType "subtractIndexExprs") Nothing [e1,e2] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpSub $ DecT dec) x2)
    
landExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)
landExprs l e1 e2 = do
    (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ OpSub $ NoType "landExprs") Nothing [e1,e2] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpLand $ DecT dec) x2)

eqExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)
eqExprs l e1 e2 = do
    (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ OpEq $ NoType "eqExprs") Nothing [e1,e2] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpEq $ DecT dec) x2)

--landExprsLoc :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier (Typed loc) -> Expression VarIdentifier (Typed loc) -> TcM loc m (Expression VarIdentifier (Typed loc))
--landExprsLoc l e1 e2 = do
--    (dec,[x1,x2]) <- tcTopPDecCstrM l True (Right $ OpSub $ NoType "landExprs") Nothing [(fmap typed e1),(fmap typed e2)] (BaseT bool)
--    return (BinaryExpr (Typed l $ BaseT bool) (fmap (Typed l) x1) (OpLand $ Typed l $ DecT dec) (fmap (Typed l) x2))







