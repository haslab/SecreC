{-# LANGUAGE TupleSections, ImpredicativeTypes, Rank2Types, ViewPatterns, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Utils as Utils
import Language.SecreC.Pretty
import Language.SecreC.Position
import Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import Language.SecreC.Prover.Base

import Safe

import Data.Typeable
import Data.Either
import Data.Maybe
import Data.Unique
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set(..))
import Data.Map (Map(..))
import Data.Foldable
import Data.Graph.Inductive.Graph as Graph
import Data.Generics

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Control.Monad.State as State

import Text.PrettyPrint

instance (MonadIO m) => Vars VarIdentifier (TcM m) [(Bool,Constrained Var,IsVariadic)] where
    traverseVars f = mapM f

instance PP [(Bool,Constrained Var,IsVariadic)] where
    pp = sepBy comma . map (\(x,y,z) -> ppConst x <+> ppVariadicArg pp (y,z))

instance PP [(Expr,Var)] where
    pp = sepBy comma . map (\(e,v) -> ppExprTy e <+> text "~~>" <+> ppVarTy v)

instance PP [Var] where
    pp = sepBy comma . map ppVarTy

-- Procedure arguments are maybe provided with index expressions
-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (ProverK loc m) => loc -> Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> Maybe Type -> [Var] -> TcM m [EntryEnv] -> TcM m DecType
matchTemplate l doCoerce n targs pargs ret rets check = do
    entries <- check
    instances <- instantiateTemplateEntries l doCoerce n targs pargs ret rets entries
    let oks = rights instances
    let errs = lefts instances
    def <- ppTpltAppM l n targs pargs ret
    case oks of
        [] -> do
            defs <- forM errs $ \(e,err) -> do
                t' <- ppM l $ entryType e
                return (locpos $ entryLoc e,t',err)
            tcError (locpos l) $ Halt $ NoMatchingTemplateOrProcedure def defs
        [(e,e',wrap,subst)] -> do
            dec <- resolveTemplateEntry l n targs pargs ret e' wrap subst
            return dec
        otherwise -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,e',wrap,subst):_) <- sortByM (compareTemplateDecls def l n) oks
            -- return the instantiated body of the most specific declaration
            dec <- resolveTemplateEntry l n targs pargs ret e' wrap subst
            return dec

templateCstrs :: Location loc => (Int,SecrecError -> SecrecError) -> Doc -> loc -> TDict -> TDict
templateCstrs (i,arr) doc p d = d { tCstrs = Graph.nmap upd (tCstrs d) }
    where
    upd (Loc l k) = Loc l $ k { kCstr = DelayedK (kCstr k) (succ i,SecrecErrArr arr) }

resolveTemplateEntry :: (ProverK loc m) => loc -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> Maybe Type -> EntryEnv -> Bool -> TDict -> TcM m DecType
resolveTemplateEntry p n targs pargs ret e doWrap dict = do
    def <- ppTpltAppM p n targs pargs ret
    -- guarantee that the most specific template can be fully instantiated
    arr <- askErrorM'
    dec <- typeToDecType p (entryType e)
    --liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppr n ++ " " ++ ppr targs ++ " " ++ ppr pargs ++ " " ++ ppr dec'
    let wrap = if doWrap then withTpltDecRec p dec else id
    -- prove the body (with a recursive declaration)
    wrap $ prove p "resolveTemplateEntry" $ addHeadTDict p $ templateCstrs arr def p dict
    let tycl@(Proc _ rs ws) = tyProcClass $ DecT dec
    isPure <- getPure
    when isPure $ unless (Set.null rs && Set.null ws) $ genTcError (locpos p) $ text "procedure not pure" <+> def
    addProcClass tycl
    return dec

removeTemplate :: (ProverK loc m) => loc -> DecType -> TcM m (Maybe DecType)
removeTemplate l t@(DecType i isrec targs hdict hfrees bdict bfrees specs d) = if (not isrec) && (isTemplateDecType t)
    then do
        j <- newModuleTyVarId
        return $ Just $ DecType j False [] emptyPureTDict hfrees emptyPureTDict bfrees [] d
    else return Nothing
removeTemplate l (DVar v) = resolveDVar l v >>= removeTemplate l
removeTemplate l t = genTcError (locpos l) $ text "removeTemplate" <+> pp t

ppTpltAppM :: (ProverK loc m) => loc -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> Maybe Type -> TcM m Doc
ppTpltAppM l pid args es ret = do
    ss <- getTSubsts l
    pid' <- substFromTSubsts "ppTplt" l ss False Map.empty pid
    args' <- mapM (mapM (mapFstM (substFromTSubsts "ppTplt" l ss False Map.empty))) args
    es' <- mapM (mapM (mapFstM (substFromTSubsts "ppTplt" l ss False Map.empty))) es
    ret' <- substFromTSubsts "ppTplt" l ss False Map.empty ret
    return $ ppTpltApp pid' args' es' ret'

ppTpltApp :: TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> Maybe Type -> Doc
ppTpltApp (Left n) args Nothing Nothing = text "struct" <+> pp n <> abrackets (sepBy comma $ map (ppVariadicArg pp) $ concat $ args)
ppTpltApp (Right (Left n)) targs args (Just ret) = pp ret <+> pp n <> abrackets (sepBy comma $ map pp $ concat targs) <> parens (sepBy comma $ map (\(e,b) -> pp e <+> text "::" <+> ppVariadic (pp $ loc e) b) $ concat args)
ppTpltApp (Right (Right n)) targs args (Just ret) = pp ret <+> pp n <> abrackets (sepBy comma $ map pp $ concat targs) <> parens (sepBy comma $ map (\(e,b) -> pp e <+> text "::" <+> ppVariadic (pp $ loc e) b) $ concat args)

compareProcedureArgs :: (ProverK loc m) => loc -> [(Bool,Constrained Var,IsVariadic)] -> [(Bool,Constrained Var,IsVariadic)] -> TcM m (Comparison (TcM m))
compareProcedureArgs l xs@[] ys@[] = return (Comparison xs ys EQ)
compareProcedureArgs l ((_,Constrained v1@(VarName t1 n1) c1,isVariadic1):xs) ((_,Constrained v2@(VarName t2 n2) c2,isVariadic2):ys) = do
--    liftIO $ putStrLn $ "comparePArgExp " ++ ppr v1 ++ " " ++ ppr v2 ++ " "
    o0 <- comparesExpr l True (varExpr v1) (varExpr v2)
--    liftIO $ putStr $ show (compOrdering o0)
--    liftIO $ putStrLn $ "comparePArg " ++ ppr t1 ++ " " ++ ppr t2 ++ " "
    o1 <- compares l t1 t2
--    liftIO $ putStr $ show (compOrdering o1)
    unless (isVariadic1 == isVariadic2) $ constraintError (ComparisonException "procedure argument") l t1 pp t2 pp Nothing
    o2 <- compareProcedureArgs l xs ys
    appendComparisons l [o0,o1,o2]
compareProcedureArgs l xs ys = constraintError (ComparisonException "procedure argument") l xs pp ys pp Nothing

-- | Tells if one declaration is strictly more specific than another, and if not it fails.
-- Since we are unifying base types during instantiation, it may happen that the most specific match is chosen over another more generic best match. This problem does not arise though if we only resolve templates on full instantiation. If we ever change this, we should use instead a three-way comparison that also tries to minimize the number of instantiated type variables in the context.
-- An example is if we tried to match the template over a type variable T:
-- y = f ((T) x)
-- bool f (int x) { ... }     (1)
-- bool f (T x) { ... }       (2)
-- bool f (T [[N]] x) { ... } (3)
-- We would be choosing choosing (1), even though the best match is in principle (2), that does not instantiate T.
-- doesn't take into consideration index conditions
compareTemplateDecls :: (ProverK loc m) => Doc -> loc -> TIdentifier -> (EntryEnv,EntryEnv,Bool,TDict) -> (EntryEnv,EntryEnv,Bool,TDict) -> TcM m Ordering
compareTemplateDecls def l n (e1,_,_,_) (e2,_,_,_) = liftM fst $ tcProve l "compare" $ tcBlock $ do
    --liftIO $ putStrLn $ "compareTemplateDecls " ++ ppr e1 ++ "\n" ++ ppr e2
    State.modify $ \env -> env { localDeps = Set.empty, globalDeps = Set.empty }
    --e1' <- localTemplate e1
    --e2' <- localTemplate e2
    (targs1,pargs1,ret1) <- templateArgs (entryLoc e1) n (entryType e1)
    (targs2,pargs2,ret2) <- templateArgs (entryLoc e2) n (entryType e2)
    --removeTSubsts $ tpltTyVars targs1
    --removeTSubsts $ tpltTyVars targs2
    let defs = map (\e -> (locpos $ entryLoc e,pp (entryType e))) [e1,e2]
    let err = TypecheckerError (locpos l) . Halt . ConflictingTemplateInstances def defs
    ord <- addErrorM l err $ do
--        ss <- liftM (tSubsts . mconcat . tDict) State.get
--        liftIO $ putStrLn $ show $ ppTSubsts ss
--        liftIO $ putStrLn $ "compareTplt " ++ ppr l ++" "++ show (fmap (map (ppVarTy . unConstrained. snd3)) pargs1) ++" "++ ppr ret1 ++" "++ show (fmap (map (ppVarTy . unConstrained. snd3)) pargs2) ++" "++ ppr ret2
        ord2 <- compareProcedureArgs l (concat pargs1) (concat pargs2)
        ord3 <- comparesList l (maybeToList ret1) (maybeToList ret2)
        appendComparison l ord2 ord3
    when (compOrdering ord == EQ) $ tcError (locpos l) $ DuplicateTemplateInstances def defs
    --liftIO $ putStrLn $ "finished comparing " ++ ppr e1 ++ "\n" ++ ppr e2
    return $ compOrdering ord
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (ProverK loc m) => loc -> Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> Maybe Type -> [Var] -> [EntryEnv] -> TcM m [Either (EntryEnv,SecrecError) (EntryEnv,EntryEnv,Bool,TDict)]
instantiateTemplateEntries p doCoerce n targs pargs ret rets es = mapM (instantiateTemplateEntry p doCoerce n targs pargs ret rets) es

unifyTemplateTypeArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Constrained Type,IsVariadic)] -> TcM m ()
unifyTemplateTypeArgs l lhs rhs = do
--    liftIO $ putStrLn $ "unifyTpltTyArg " ++ ppr lhs ++ " " ++ ppr (map (\(x,y) -> (unConstrainedx,y)) rhs)
    (cs,ks) <- tcWithCstrs l "unity tplt type args" $ do
        -- expand the passed type arguments
        ts <- concatMapM (expandVariadicType l) lhs
        -- separate procedure argument types from their conditions
        let (tts,catMaybes -> tcs) = unzip $ map (\(Constrained t c,b) -> ((t,b),c)) rhs
        -- match each procedure argument type
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "template type arguments") (pp tts) (pp ts) . Just)
            (matchVariadicTypeArgs l tts ts)
        return tcs
    -- check the procedure argument conditions
    forM_ cs $ \c -> withDependencies ks $ tcCstrM_ l $ IsValid c      

matchVariadicTypeArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [Type] -> TcM m ()
matchVariadicTypeArgs l [] [] = return ()
matchVariadicTypeArgs l xs@[] ys = genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> pp xs <+> pp ys
matchVariadicTypeArgs l (x:xs) ys = do
    ys' <- matchVariadicTypeArg l x ys
    matchVariadicTypeArgs l xs ys'

-- matches a procedure argument type with a list of types, and produces a remainder of unmatched types
matchVariadicTypeArg :: (ProverK loc m) => loc -> (Type,IsVariadic) -> [Type] -> TcM m [Type]
matchVariadicTypeArg l x@(t,False) ys@[] = genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> pp x <+> pp ys
matchVariadicTypeArg l (t,False) (y:ys) = do
    tcCstrM_ l $ Unifies t y
    return ys
matchVariadicTypeArg l (VArrayT (VAVal ts _),True) xs = do
    let (xs1,xs2) = splitAt (length ts) xs
    unifiesList l ts xs1
    return xs2
matchVariadicTypeArg l (t,True) xs = do
    let tt = tyOf t
    sz <- typeSize l tt
    b <- typeBase l tt
    (xs1,xs2) <- spanM (isTyOf l b) xs
    -- match the array content
    tcCstrM_ l $ Unifies t (VArrayT $ VAVal xs1 b)
    -- match the array size
    unifiesExprTy l True sz (indexExpr $ toEnum $ length xs1)
    return xs2      

matchVariadicPArgs :: (ProverK loc m) => Bool -> loc -> [(Bool,Expr,IsVariadic)] -> [(Expr,Var)] -> TcM m ()
matchVariadicPArgs doCoerce l [] [] = return ()
matchVariadicPArgs doCoerce l xs@[] ys = genTcError (locpos l) $ text "Procedure argument variadic mismatch" <+> pp (map (\(x,y,z) -> (y,z)) xs) <+> pp (map fst ys)
matchVariadicPArgs doCoerce l (x:xs) ys = do
    ys' <- matchVariadicPArg doCoerce l x ys
    matchVariadicPArgs doCoerce l xs ys'

matchVariadicPArg :: (ProverK loc m) => Bool -> loc -> (Bool,Expr,IsVariadic) -> [(Expr,Var)] -> TcM m [(Expr,Var)]
matchVariadicPArg doCoerce l (isConst,v,False) exs@[] = genTcError (locpos l) $ text "Procedure argument variadic mismatch" <+> pp v <+> pp (map fst exs)
matchVariadicPArg doCoerce l (isConst,v,False) ((e,x):exs) = do
    coercePArg doCoerce l isConst v (e,x)
    return exs
matchVariadicPArg doCoerce l (isConst,v,True) exs = do
    let t = loc v
    case t of
        VArrayT (VAVal ts b) -> do -- constant array
            let (exs1,exs2) = splitAt (length ts) exs
            vs <- expandVariadicExpr l (v,True)
            matchVariadicPArgs doCoerce l (map (\v -> (isConst,v,False)) vs) exs1
            return exs2
        otherwise -> do
            sz <- typeSize l t
            b <- typeBase l t
            (unzip -> (vs,exs1),exs2) <- spanMaybeM (\ex -> newTypedVar "varr" b Nothing >>= \v -> tryCstrMaybe l (coercePArg doCoerce l isConst (varExpr v) ex >> return (v,ex))) exs
            -- match the array content
            if isConst
                then unifiesExprTy l True v (ArrayConstructorPExpr t $ map varExpr vs)
                else tcCstrM_ l $ Unifies (loc v) t
            -- match the array size
            unifiesExprTy l True sz (indexExpr $ toEnum $ length exs1)
            return exs2

coercePArg :: (ProverK loc m) => Bool -> loc -> Bool -> Expr -> (Expr,Var) -> TcM m ()
coercePArg doCoerce l isConst v2 (e,x2) = do
--    liftIO $ putStrLn $ show $ text "coercePArg" <+> ppExprTy v2 <+> ppExprTy e <+> ppExprTy x2
    let tt = loc v2
    let t = loc e
    let tx2 = loc x2
    tcCstrM_ l $ Unifies tx2 tt
    if doCoerce
        then tcCstrM_ l $ Coerces e x2
        else do
            tcCstrM_ l $ Unifies (loc x2) (loc e)
            assignExpr l x2 e
    tcCstrM_ l $ Unifies (loc v2) (loc x2)

expandPArgExpr :: (ProverK loc m) => loc -> ((Expr,IsVariadic),Var) -> TcM m [(Expr,Var)]
expandPArgExpr l ((e,False),x) = return [(e,x)]
expandPArgExpr l ((e,True),x) = do
    vs <- expandVariadicExpr l (e,True)
    ct0 <- newTyVar Nothing
    let at = VAType ct0 (indexExpr $ toEnum $ length vs)
    xs <- forM vs $ \v -> newTypedVar "xi" ct0 Nothing
    -- match array content
    tcCstrM_ l $ Unifies (loc x) at
    assignExpr l x (ArrayConstructorPExpr at $ map varExpr xs)
    return $ zip vs xs

coerceProcedureArgs :: (ProverK loc m) => Bool -> loc -> [((Expr,IsVariadic),Var)] -> [(Bool,Constrained Var,IsVariadic)] -> TcM m ()
coerceProcedureArgs doCoerce l lhs rhs = do
    (cs,ks) <- tcWithCstrs l "coerce proc args" $ do
        -- expand passed expressions
        exs <- concatMapM (expandPArgExpr l) lhs
        -- separate procedure arguments from their conditions
        let (vs,catMaybes -> cs) = unzip $ map (\(isConst,Constrained v c,b) -> ((isConst,varExpr v,b),c)) rhs
        -- match each procedure argument
        addErrorM l
            (TypecheckerError (locpos l) . (CoercionException "procedure arguments") (pp exs) (pp $ map (\(x,y,z) -> (y,z)) vs) . Just)
            (matchVariadicPArgs doCoerce l vs exs)
        return cs
    -- check the procedure argument conditions
    forM_ cs $ \c -> withDependencies ks $ checkCstrM_ l ks $ CheckAssertion c

instantiateTemplateEntry :: (ProverK loc m) => loc -> Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> Maybe Type -> [Var] -> EntryEnv -> TcM m (Either (EntryEnv,SecrecError) (EntryEnv,EntryEnv,Bool,TDict))
instantiateTemplateEntry p doCoerce n targs pargs ret rets e = do
    let l = entryLoc e
    --e <- localTemplate l e
--    doc <- liftM ppTSubsts getTSubsts
--    liftIO $ putStrLn $ "inst " ++ show doc
    --liftIO $ putStrLn $ "instantiating " ++ ppr p ++ " " ++ ppr l ++ " " ++ ppr n ++ " " ++ ppr (fmap (map fst) targs) ++ " " ++ show (fmap (map (\(e,b) -> ppVariadicArg pp (e,b) <+> text "::" <+> pp (loc e))) pargs) ++ " " ++ ppr ret ++ " " ++ ppr rets ++ " " ++ ppr (entryType e)
    (tplt_targs,tplt_pargs,tplt_ret) <- templateArgs (entryLoc e) n (entryType e)
    isPure <- getPure
    (e',hdict,bdict,bgr) <- templateTDict isPure e
    let addDicts = do
        addHeadTDict l hdict
        addHeadTDict l bdict
    let matchName = unifiesTIdentifier l (templateIdentifier $ entryType e') n
    let proveHead = do
        (_,ks) <- tcWithCstrs l "instantiate" $ withoutEntry e $ do   
            tcAddDeps l "tplt type args" $ do
                -- unify the explicit invocation template arguments unify with the base template
                when (isJust targs) $ unifyTemplateTypeArgs l (concat targs) (concat tplt_targs)
                -- unify the procedure return type
                unifiesList l (maybeToList tplt_ret) (maybeToList ret)
            -- coerce procedure arguments into the base procedure arguments
            coerceProcedureArgs doCoerce l (zip (concat pargs) rets) (concat tplt_pargs)
        -- if there are no explicit template type arguments, we need to make sure to check the type invariants
        when (isNothing targs) $ do
            forM_ (maybe [] (catMaybes . map (\(Constrained x c,isVariadic) -> c)) tplt_targs) $ \c -> do
                withDependencies ks $ tcCstrM_ l $ IsValid c
        return ()
    ok <- newErrorM $ proveWith l ("instantiate with names " ++ ppr n) (addDicts >> matchName >> proveHead)
    --ks <- ppConstraints =<< liftM (maybe Graph.empty tCstrs . headMay . tDict) State.get
    --liftIO $ putStrLn $ "instantiate with names " ++ ppr n ++ " " ++ show ks
    case ok of
        Left err -> return $ Left (e,err)
        Right (_,TDict hgr _ subst) -> do
                (e',(subst',bgr')) <- localTemplateWith l e' (subst,bgr)
                hgr' <- substFromTSubsts "instantiate tplt" l subst' False Map.empty (toPureCstrs hgr)
--                liftIO $ putStrLn $ "worked " ++ ppr l -- ++ " % " ++ show (ppTSubsts (tSubsts subst)) ++ " %"
                gr' <- liftIO $ fromPureCstrs $ unionGr bgr' hgr'
                let depCstrs = TDict gr' Set.empty subst'
                --depCstrs <- mergeDependentCstrs l subst' bgr''
                --doc <- ppConstraints bgr'
                --liftIO $ putStrLn $ "remainder" ++ ppr n ++ " " ++ show doc
                dec <- typeToDecType l (entryType e')
                mb_dec1 <- removeTemplate l dec
                (e'',doWrap) <- case mb_dec1 of
                            Nothing -> do
                                dec2 <- substFromTSubsts "instantiate tplt" l subst' False Map.empty dec
                                liftIO $ putStrLn $ "withTplt: " ++ ppr l ++ " " ++ ppr (decTypeTyVarId dec) ++ ppr (decTypeTyVarId dec2) ++ "\n" ++ ppr subst ++ "\n+++\n"++ppr subst' ++ "\n" ++ ppr dec2
                                return (e' { entryType = DecT dec2 },False)
                            Just dec1 -> do
                                --dec'' <- substFromTDict "instantiate tplt" l subst False Map.empty dec'
--                                liftIO $ putStrLn $ "instantiated declaration  " ++ ppr dec'' ++ "\n" ++ show (ppTSubsts (tSubsts subst))
                                dec2 <- substFromTSubsts "instantiate tplt" l subst' False Map.empty dec1
                                liftIO $ putStrLn $ "withTplt: " ++ ppr l ++ " " ++ ppr (decTypeTyVarId dec) ++ ppr (decTypeTyVarId dec2) ++ "\n" ++ ppr subst ++ "\n+++\n"++ppr subst' ++ "\n" ++ ppr dec2
                                has <- hasCondsDecType dec2
                                return (e' { entryType = DecT dec2 },not has)
                return $ Right (e,e'',doWrap,depCstrs)

-- merge two dictionaries with the second depending on the first
--mergeDependentCstrs :: (ProverK loc m) => loc -> TDict -> TDict -> TcM m (TDict)
--mergeDependentCstrs l from to = do
--    let froms = map fst $ endsGr $ tCstrs from
--    let tos = map fst $ rootsGr $ tCstrs to
--    let deps = [ (f,t) | f <- froms, t <- tos ]
--    fromto <- appendTDict l CheckS from to
--    let merge = foldl' (\d (f,t) -> d { tCstrs = insEdge (f,t,()) (tCstrs d) } ) fromto deps
--    return merge

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (DecType _ _ _ _ _ _ _ _ t) = templateIdentifier' t
    templateIdentifier' (ProcType _ n _ _ _ _ _) = Right n
    templateIdentifier' (StructType _ n _) = Left n
   
-- has procedure conditions     
hasCondsDecType :: (MonadIO m) => DecType -> TcM m Bool
hasCondsDecType (DecType _ _ targs _ _ _ _ _ d) = do
    b <- hasCondsDecType d
    return $ b || (any hasConstrained $ map fst targs)
hasCondsDecType (ProcType _ _ pargs _ _ _ _) = return $ any hasConstrained $ map snd3 pargs
hasCondsDecType _ = return False
        
-- | Extracts a head signature from a template type declaration (template arguments,procedure arguments, procedure return type)
templateArgs :: (MonadIO m,Location loc) => loc -> TIdentifier -> Type -> TcM m (Maybe [(Constrained Type,IsVariadic)],Maybe [(Bool,Constrained Var,IsVariadic)],Maybe Type)
templateArgs l (Left name) t = case t of
    DecT (DecType _ _ args hcstrs hfrees cstrs bfrees [] body) -> do -- a base template uses the base arguments
        return (Just $ map (mapFst (fmap varNameToType)) args,Nothing,Nothing)
    DecT (DecType _ _ args hcstrs hfrees cstrs bfrees specials body) -> do -- a specialization uses the specialized arguments
        return (Just $ map (mapFst (flip Constrained Nothing)) specials,Nothing,Nothing)
templateArgs l (Right name) t = case t of
    DecT (DecType _ _ args hcstrs hfrees cstrs bfrees [] (ProcType _ n vars ret ann stmts _)) -> do -- include the return type
        return (Just $ map (mapFst (fmap varNameToType)) args,Just vars,Just ret)
    otherwise -> genTcError (locpos l) $ text "Invalid type for procedure template"

tpltTyVars :: Maybe [(Constrained Type,IsVariadic)] -> Set VarIdentifier
tpltTyVars Nothing = Set.empty
tpltTyVars (Just xs) = Set.fromList $ map (varNameId . fromJust . typeToVarName . unConstrained . fst) xs

templateTDict :: (ProverK Position m) => Bool -> EntryEnv -> TcM m (EntryEnv,TDict,TDict,TCstrGraph)
templateTDict isPure e = case entryType e of
    DecT (DecType i isFree vars hd hfrees d bfrees specs ss) -> do
        hd' <- liftIO $ fromPureTDict $ hd { pureCstrs = purify $ pureCstrs hd }
        let d' = TDict Graph.empty Set.empty (pureSubsts d)
        let e' = e { entryType = DecT (DecType i isFree vars emptyPureTDict hfrees emptyPureTDict bfrees specs ss) }
        return (e',hd',d',purify $ pureCstrs d)
    otherwise -> return (e,emptyTDict,emptyTDict,Graph.empty)
  where
    purify :: TCstrGraph -> TCstrGraph
    purify = Graph.nmap (fmap add)
    add :: TCstr -> TCstr
    add (DelayedK c arr) = DelayedK (add c) arr
    add (TcK c b1 b2) = TcK c b1 (b2 || isPure)
    add (CheckK c b1 b2) = CheckK c b1 (b2 || isPure)
    add (HypK c b1 b2) = HypK c b1 (b2 || isPure)
  

condVarType (Constrained (VarName t n) c) = constrainedType t c
condVar (Constrained (VarName t n) c) = VarName (constrainedType t c) n
condT (Constrained t c) = constrainedType t c

-- | renames the variables in a template to local names
localTemplate :: (ProverK loc m) => loc -> EntryEnv -> TcM m EntryEnv
localTemplate l e = liftM fst $ localTemplateWith l e ()

localTemplateWith :: (Vars VarIdentifier (TcM m) a,ProverK loc m) => loc -> EntryEnv -> a -> TcM m (EntryEnv,a)
localTemplateWith l e a = case entryType e of
    DecT t -> do
        --liftIO $ putStrLn $ "localTemplate: " ++ ppr l ++ "\n" ++ ppr t
        (t',ss,ssBounds) <- localTemplateType emptySubstsProxy Map.empty (entryLoc e) t
        --liftIO $ putStrLn $ "localSS: " ++ ppr l ++ "\n" ++ ppr ssBounds
        --liftIO $ putStrLn $ "localTemplate': " ++ ppr l ++ "\n" ++ ppr t'
        a' <- substProxy "localTplt" ss False ssBounds a
        liftIO $ putStrLn $ "localTemplateReturn: " ++ ppr l ++ ppr a'
        return (EntryEnv (entryLoc e) $ DecT t',a')

localTemplateType :: (ProverK loc m) => SubstsProxy VarIdentifier (TcM m) -> Map VarIdentifier VarIdentifier -> loc -> DecType -> TcM m (DecType,SubstsProxy VarIdentifier (TcM m),Map VarIdentifier VarIdentifier)
localTemplateType (ss0::SubstsProxy VarIdentifier (TcM m)) ssBounds (l::loc) et = case et of
    DecType tpltid isrec (unzip -> (args,isVariadics)) hcstrs hfrees cstrs bfrees (unzip -> (specials,isVariadics2)) body -> do
        (hfrees',hfreelst) <- Utils.mapAndUnzipM freeVar $ Set.toList hfrees
        (bfrees',bfreelst) <- Utils.mapAndUnzipM freeVar $ Set.toList bfrees
        let freelst = hfreelst ++ bfreelst
        let freess :: SubstsProxy VarIdentifier (TcM m)
            freess = substsProxyFromList freelst `appendSubstsProxy` ss0
        let ssBounds1 = ssBounds `Map.union` Map.fromList freelst
        (args',ss,ssBounds2) <- uniqueVars l freess ssBounds1 args
        specials' <- substProxy "localTplt" ss False ssBounds2 specials
        (body',ss',ssBounds3) <- localTemplateType ss ssBounds2 l body
        hcstrs' <- substProxy "localTplt" ss' False ssBounds3 hcstrs
        cstrs' <- substProxy "localTplt" ss' False ssBounds3 cstrs
        return (DecType tpltid isrec (zip args' isVariadics) hcstrs' (Set.fromList hfrees') cstrs' (Set.fromList bfrees') (zip specials' isVariadics2) body',ss',ssBounds3)
    ProcType p pid (unzip3 -> (isConsts,args,isVariadics)) ret ann stmts c -> do
        (args',ss,ssBounds1) <- uniqueVars l ss0 ssBounds args
        pid' <- substProxy "localTplt" ss False ssBounds1 pid
        ret' <- substProxy "localTplt" ss False ssBounds1 ret
        ann' <- substProxy "localTplt" ss False ssBounds1 ann
        stmts' <- substProxy "localTplt" ss False ssBounds1 stmts
        return (ProcType p pid' (zip3 isConsts args' isVariadics) ret' ann' stmts' c,ss,ssBounds1)
    otherwise -> return (et,ss0,ssBounds)
  where
    freeVar v = do
        (mn,j) <- newModuleTyVarId
        let v' = v { varIdUniq = Just j, varIdModule = Just mn }
        return (v',(v,v'))
    uniqueVar :: loc -> SubstsProxy VarIdentifier (TcM m) -> Map VarIdentifier VarIdentifier -> Constrained Var -> TcM m (Constrained Var,SubstsProxy VarIdentifier (TcM m), Map VarIdentifier VarIdentifier)
    uniqueVar (l::loc) ss ssBounds (Constrained i@(VarName t v) c) = do
        v' <- freshVarId (varIdBase v) Nothing
        t' <- substProxy "localTplt" ss False ssBounds t
        let i' = VarName t' v'
        let ss' :: SubstsProxy VarIdentifier (TcM m)
            ss' = substsProxyFromTSubsts l (TSubsts $ Map.singleton v (varNameToType i')) `appendSubstsProxy` ss
        let ssBounds' :: Map VarIdentifier VarIdentifier
            ssBounds' = Map.insert v v' ssBounds
        c' <- substProxy "localTplt" ss' False ssBounds' c
        return (Constrained i' c',ss',ssBounds')
    uniqueVars :: loc -> SubstsProxy VarIdentifier (TcM m) -> Map VarIdentifier VarIdentifier -> [Constrained Var] -> TcM m ([Constrained Var],SubstsProxy VarIdentifier (TcM m),Map VarIdentifier VarIdentifier)
    uniqueVars l ss ssBounds [] = return ([],ss,ssBounds)
    uniqueVars l ss ssBounds (x:xs) = do
        (x',ss',ssBounds') <- uniqueVar l ss ssBounds x
        (xs',ss'',ssBounds'') <- uniqueVars l ss' ssBounds' xs
        return (x' : xs',ss'',ssBounds'')










