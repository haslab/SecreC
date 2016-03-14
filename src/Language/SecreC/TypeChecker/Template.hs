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
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Index
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type

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

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Control.Monad.State as State

import Text.PrettyPrint

instance (MonadIO m) => Vars VarIdentifier (TcM loc m) [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] where
    traverseVars f = mapM f

instance PP [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] where
    pp = sepBy comma . map (\(x,y,z) -> ppConst x <+> ppVariadicArg pp (y,z))

-- Procedure arguments are maybe provided with index expressions
-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> Maybe [VarName VarIdentifier Type] -> TcM loc m [EntryEnv loc] -> TcM loc m (DecType)
matchTemplate l doCoerce n targs pargs ret rets check = do
    entries <- check
    instances <- instantiateTemplateEntries doCoerce n targs pargs ret rets entries
    let oks = rights instances
    let errs = lefts instances
    def <- ppTpltAppM l n targs pargs ret
    case oks of
        [] -> do
            defs <- forM errs $ \(e,err) -> do
                t' <- ppM l $ entryType e
                return (locpos $ entryLoc e,t',err)
            tcError (locpos l) $ Halt $ NoMatchingTemplateOrProcedure def defs
        [(e,wrap,subst)] -> do
            dec <- resolveTemplateEntry l n targs pargs ret e wrap subst
            return dec
        otherwise -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,wrap,subst):_) <- sortByM (compareTemplateDecls def l n) oks
            -- return the instantiated body of the most specific declaration
            dec <- resolveTemplateEntry l n targs pargs ret e wrap subst
            return dec

templateCstrs :: Location loc => (Int,SecrecErrArr) -> Doc -> loc -> TDict loc -> TDict loc
templateCstrs (i,arr) doc p d = d { tCstrs = Graph.nmap upd (tCstrs d) }
    where
    upd (Loc l k) = Loc l $ k { kCstr = DelayedK (kCstr k) (succ i,arr . TypecheckerError (locpos p) . TemplateSolvingError doc) }

resolveTemplateEntry :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> EntryEnv loc -> Bool -> TDict loc -> TcM loc m DecType
resolveTemplateEntry p n targs pargs ret e doWrap dict = do
--    liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppr n ++ " " ++ ppr args ++ " " ++ ppr (entryType e)
    def <- ppTpltAppM p n targs pargs ret
    -- guarantee that the most specific template can be fully instantiated
    arr <- askErrorM'
    dec <- typeToDecType p (entryType e)
    let wrap = if doWrap then withTpltDecRec p dec else id
    -- prove the body (with a recursive declaration)
    wrap $ prove p "resolveTemplateEntry" $ addHeadTDict $ templateCstrs arr def p dict
    return dec

removeTemplate :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> TcM loc m (Maybe DecType)
removeTemplate l t@(DecType i isrec targs hdict hfrees bdict bfrees specs d) = if (not isrec) && (isTemplateDecType t)
    then do
        j <- newTyVarId
        return $ Just $ DecType j False [] hdict hfrees mempty bfrees [] d
    else return Nothing
removeTemplate l (DVar v) = resolveDVar l v >>= removeTemplate l
removeTemplate l t = genTcError (locpos l) $ text "removeTemplate" <+> pp t

ppTpltAppM :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> TcM loc m Doc
ppTpltAppM l pid args es ret = do
    ss <- getTSubsts
    pid' <- substFromTSubsts "ppTplt" l ss False Map.empty pid
    args' <- mapM (mapM (mapFstM (substFromTSubsts "ppTplt" l ss False Map.empty))) args
    es' <- mapM (mapM (mapFstM (substFromTSubsts "ppTplt" l ss False Map.empty))) es
    ret' <- substFromTSubsts "ppTplt" l ss False Map.empty ret
    return $ ppTpltApp pid' args' es' ret'

ppTpltApp :: TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> Doc
ppTpltApp (Left n) args Nothing Nothing = text "struct" <+> pp n <> abrackets (sepBy comma $ map (ppVariadicArg pp) $ concat $ args)
ppTpltApp (Right (Left n)) targs args (Just ret) = pp ret <+> pp n <> abrackets (sepBy comma $ map pp $ concat targs) <> parens (sepBy comma $ map (\(e,b) -> pp e <+> text "::" <+> pp (loc e) <> ppVariadic b) $ concat args)
ppTpltApp (Right (Right n)) targs args (Just ret) = pp ret <+> pp n <> abrackets (sepBy comma $ map pp $ concat targs) <> parens (sepBy comma $ map (\(e,b) -> pp e <+> text "::" <+> pp (loc e) <> ppVariadic b) $ concat args)

compareProcedureArgs :: (VarsIdTcM loc m,Location loc) => loc -> [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] -> [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] -> TcM loc m (Comparison (TcM loc m))
compareProcedureArgs l xs@[] ys@[] = return (Comparison xs ys EQ)
compareProcedureArgs l ((_,Cond v1@(VarName t1 n1) c1,isVariadic1):xs) ((_,Cond v2@(VarName t2 n2) c2,isVariadic2):ys) = do
    let e1 = varExpr v1
    let e2 = varExpr v2
    unifiesExprTy l e1 e2
    o1 <- compares l t1 t2
    unless (isVariadic1 == isVariadic2) $ constraintError (ComparisonException "procedure argument") l t1 pp t2 pp Nothing
    o2 <- compareProcedureArgs l xs ys
    appendComparison l o1 o2
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
compareTemplateDecls :: (VarsIdTcM loc m,Location loc) => Doc -> loc -> TIdentifier -> (EntryEnv loc,Bool,TDict loc) -> (EntryEnv loc,Bool,TDict loc) -> TcM loc m Ordering
compareTemplateDecls def l n (e1,_,_) (e2,_,_) = tcBlock $ do
    State.modify $ \env -> env { localDeps = Set.empty, globalDeps = Set.empty }
    e1' <- localTemplate e1
    e2' <- localTemplate e2
    (targs1,pargs1,ret1) <- templateArgs (entryLoc e1') n (entryType e1')
    (targs2,pargs2,ret2) <- templateArgs (entryLoc e1') n (entryType e2')
    let defs = map (\e -> (locpos $ entryLoc e,pp (entryType e))) [e1,e2]
    let err = TypecheckerError (locpos l) . Halt . ConflictingTemplateInstances def defs
    ord <- addErrorM l err $ do
        ord2 <- compareProcedureArgs l (concat pargs1) (concat pargs2)
        ord3 <- comparesList l (maybeToList ret1) (maybeToList ret2)
        appendComparison l ord2 ord3
    when (compOrdering ord == EQ) $ do
        tcError (locpos l) $ DuplicateTemplateInstances def defs
    solve l
    return $ compOrdering ord
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (VarsIdTcM loc m,Location loc) => Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> Maybe [VarName VarIdentifier Type] -> [EntryEnv loc] -> TcM loc m [Either (EntryEnv loc,SecrecError) (EntryEnv loc,Bool,TDict loc)]
instantiateTemplateEntries doCoerce n targs pargs ret rets es = mapM (instantiateTemplateEntry doCoerce n targs pargs ret rets) es

unifyTemplateTypeArgs :: (VarsIdTcM loc m,Location loc) => loc -> [(Type,IsVariadic)] -> [(Cond Type,IsVariadic)] -> TcM loc m ()
unifyTemplateTypeArgs l lhs rhs = do
    (cs,ks) <- tcWithCstrs l "unity tplt type args" $ do
        -- expand the passed type arguments
        ts <- concatMapM (expandVariadicType l) lhs
        -- separate procedure argument types from their conditions
        let (tts,catMaybes -> tcs) = unzip $ map (\(Cond t c,b) -> ((t,b),c)) rhs
        -- match each procedure argument type
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "template type arguments") (pp tts) (pp ts) . Just)
            (matchVariadicTypeArgs l tts ts)
        return tcs
    -- check the procedure argument conditions
    forM_ cs $ \c -> withDependencies ks $ tcCstrM l $ IsValid c      

matchVariadicTypeArgs :: (VarsIdTcM loc m,Location loc) => loc -> [(Type,IsVariadic)] -> [Type] -> TcM loc m ()
matchVariadicTypeArgs l [] [] = return ()
matchVariadicTypeArgs l xs@[] ys = genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> pp xs <+> pp ys
matchVariadicTypeArgs l (x:xs) ys = do
    ys' <- matchVariadicTypeArg l x ys
    matchVariadicTypeArgs l xs ys'

-- matches a procedure argument type with a list of types, and produces a remainder of unmatched types
matchVariadicTypeArg :: (VarsIdTcM loc m,Location loc) => loc -> (Type,IsVariadic) -> [Type] -> TcM loc m [Type]
matchVariadicTypeArg l x@(t,False) ys@[] = genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> pp x <+> pp ys
matchVariadicTypeArg l (t,False) (y:ys) = do
    tcCstrM l $ Unifies t y
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
    tcCstrM l $ Unifies t (VArrayT $ VAVal xs1 b)
    -- match the array size
    unifiesExprTy l sz (indexSExpr $ toEnum $ length xs1)
    return xs2      

matchVariadicPArgs :: (VarsIdTcM loc m,Location loc) => Bool -> loc -> [(Bool,SExpr VarIdentifier Type,IsVariadic)] -> [(Expression VarIdentifier Type,VarName VarIdentifier Type)] -> TcM loc m ()
matchVariadicPArgs doCoerce l [] [] = return ()
matchVariadicPArgs doCoerce l xs@[] ys = genTcError (locpos l) $ text "Procedure argument variadic mismatch" <+> pp (map (\(x,y,z) -> (y,z)) xs) <+> pp (map fst ys)
matchVariadicPArgs doCoerce l (x:xs) ys = do
    ys' <- matchVariadicPArg doCoerce l x ys
    matchVariadicPArgs doCoerce l xs ys'

matchVariadicPArg :: (VarsIdTcM loc m,Location loc) => Bool -> loc -> (Bool,SExpr VarIdentifier Type,IsVariadic) -> [(Expression VarIdentifier Type,VarName VarIdentifier Type)] -> TcM loc m [(Expression VarIdentifier Type,VarName VarIdentifier Type)]
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
                then unifiesExprTy l v (ArrayConstructorPExpr t $ map varExpr vs)
                else tcCstrM l $ Unifies (loc v) t
            -- match the array size
            unifiesExprTy l sz (indexSExpr $ toEnum $ length exs1)
            return exs2

coercePArg :: (VarsIdTcM loc m,Location loc) => Bool -> loc -> Bool -> SExpr VarIdentifier Type -> (Expression VarIdentifier Type,VarName VarIdentifier Type) -> TcM loc m ()
coercePArg doCoerce l isConst v2 (e,x2) = do
--    liftIO $ putStrLn $ show $ text "coercePArg" <+> ppExprTy v2 <+> ppExprTy e <+> ppExprTy x2
    let tt = loc v2
    let t = loc e
    let tx2 = loc x2
    tcCstrM l $ Unifies tx2 tt
    if doCoerce
        then tcCstrM l $ Coerces e x2
        else unifiesExprTy l (varExpr x2) e
    if isConst
        then unifiesExprTy l v2 (varExpr x2)
        else tcCstrM l $ Unifies (loc v2) (loc x2)

expandPArgExpr :: (VarsIdTcM loc m,Location loc) => loc -> ((Expression VarIdentifier Type,IsVariadic),VarName VarIdentifier Type) -> TcM loc m [(Expression VarIdentifier Type,VarName VarIdentifier Type)]
expandPArgExpr l ((e,False),x) = return [(e,x)]
expandPArgExpr l ((e,True),x) = do
    vs <- expandVariadicExpr l (e,True)
    news <- newDomainTyVar AnyKind Nothing
    newb <- newBaseTyVar Nothing
    let ct = ComplexT $ CType news newb (indexSExpr 1) [(indexSExpr $ toEnum $ length vs,False)]
    let ct0 = ComplexT $ CType news newb (indexSExpr 0) []
    xs <- forM vs $ \v -> newTypedVar "xi" ct0 Nothing
    -- match array content
    unifiesExprTy l (varExpr x) (ArrayConstructorPExpr ct $ map varExpr xs)
    -- match array type
    tcCstrM l $ Unifies ct (loc x)
    return $ zip vs xs

coerceProcedureArgs :: (VarsIdTcM loc m,Location loc) => Bool -> loc -> [((Expression VarIdentifier Type,IsVariadic),VarName VarIdentifier Type)] -> [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] -> TcM loc m ()
coerceProcedureArgs doCoerce l lhs rhs = do
    (cs,ks) <- tcWithCstrs l "coerce proc args" $ do
        -- expand passed expressions
        exs <- concatMapM (expandPArgExpr l) lhs
        -- separate procedure arguments from their conditions
        let (vs,catMaybes -> cs) = unzip $ map (\(isConst,Cond v c,b) -> ((isConst,varExpr v,b),c)) rhs
        -- match each procedure argument
        addErrorM l
            (TypecheckerError (locpos l) . (CoercionException "procedure arguments") (pp $ map fst exs) (pp $ map (\(x,y,z) -> (y,z)) vs) . Just)
            (matchVariadicPArgs doCoerce l vs exs)
        return cs
    -- check the procedure argument conditions
    forM_ cs $ \c -> withDependencies ks $ tcCstrM l $ IsValid c

instantiateTemplateEntry :: (VarsIdTcM loc m,Location loc) => Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> Maybe [VarName VarIdentifier Type] -> EntryEnv loc -> TcM loc m (Either (EntryEnv loc,SecrecError) (EntryEnv loc,Bool,TDict loc))
instantiateTemplateEntry doCoerce n targs pargs ret rets e = do
    let l = entryLoc e
    e' <- localTemplate e
--    doc <- liftM ppTSubsts getTSubsts
--    liftIO $ putStrLn $ "inst " ++ show doc
--    liftIO $ putStrLn $ "instantiating " ++ ppr l ++ " " ++ ppr n ++ " " ++ ppr (fmap (map fst) targs) ++ " " ++ show (fmap (map (\(e,b) -> ppVariadicArg pp (e,b) <+> text "::" <+> pp (loc e))) pargs) ++ " " ++ ppr ret ++ " " ++ ppr (entryType e')
    (tplt_targs,tplt_pargs,tplt_ret) <- templateArgs (entryLoc e') n (entryType e')
    let (hdict,bdict) = templateTDict e'
    let addDicts = do
        addHeadTDict hdict
        addHeadTDict $ TDict Graph.empty (tChoices bdict) (tSubsts bdict)
    let matchName = unifiesTIdentifier l (templateIdentifier $ entryType e') n -- reverse unification
    let proof = do
        (_,ks) <- tcWithCstrs l "instantiate" $ do   
            -- if the instantiation has explicit template arguments, unify them with the base template
            tcAddDeps l "tplt type args" $ when (isJust targs) $ unifyTemplateTypeArgs l (concat targs) (concat tplt_targs)
            -- coerce procedure arguments into the base procedure arguments
            coerceProcedureArgs doCoerce l (zip (concat pargs) (concat rets)) (concat tplt_pargs)
            -- unify the procedure return type
            unifiesList l (maybeToList tplt_ret) (maybeToList ret) -- reverse unification
        -- if there are no explicit template type arguments, we need to make sure to check the invariants
        when (isNothing targs) $ do
            forM_ (maybe [] (catMaybes . map (\(Cond x c,isVariadic) -> c)) tplt_targs) $ \c -> do
                withDependencies ks $ tcCstrM l $ IsValid c
    ok <- newErrorM $ proveWith l "instantiate with names" (addDicts >> matchName >> proof)
    case ok of
        Left err -> do
--            liftIO $ putStrLn $ "did not work " ++ ppr l 
            return $ Left (e',err)
        Right (_,subst) -> do
--            doc <- ppConstraints subst
--            liftIO $ putStrLn $ "worked " ++ ppr l ++ " % " ++ show doc ++ " %"
            depCstrs <- mergeDependentCstrs l subst (TDict (tCstrs bdict) Set.empty Map.empty)
            dec <- typeToDecType l (entryType e')
            mb_dec' <- removeTemplate l dec
            (dec',doWrap) <- case mb_dec' of
                        Nothing -> return (e',False)
                        Just dec' -> do
                            dec'' <- substFromTDict "instantiate tplt" l subst False Map.empty dec'
--                            liftIO $ putStrLn $ "instantiated declaration  " ++ ppr dec'' ++ "\n" ++ show (ppTSubsts (tSubsts subst))
                            has <- hasCondsDecType dec''
                            return (e' { entryType = DecT dec'' },not has)
            return $ Right (dec',doWrap,depCstrs)

-- merge two dictionaries with the second depending on the first
mergeDependentCstrs :: (VarsIdTcM loc m,Location loc) => loc -> TDict loc -> TDict loc -> TcM loc m (TDict loc)
mergeDependentCstrs l from to = do
    let froms = map fst $ endsGr $ tCstrs from
    let tos = map fst $ rootsGr $ tCstrs to
    let deps = [ (f,t) | f <- froms, t <- tos ]
    let merge = foldl' (\d (f,t) -> d { tCstrs = insEdge (f,t,()) (tCstrs d) } ) (to `mappend` from) deps
    return merge

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (DecType _ _ _ _ _ _ _ _ t) = templateIdentifier' t
    templateIdentifier' (ProcType _ n _ _ _ _) = Right n
    templateIdentifier' (StructType _ n _) = Left n
        
hasCondsDecType :: (MonadIO m,Location loc) => DecType -> TcM loc m Bool
hasCondsDecType (DecType _ _ targs _ _ _ _ _ d) = do
    b <- hasCondsDecType d
    return $ b || (any hasCond $ map fst targs)
hasCondsDecType (ProcType _ _ pargs _ _ _) = return $ any hasCond $ map snd3 pargs
hasCondsDecType _ = return False
        
-- | Extracts a head signature from a template type declaration (template arguments,procedure arguments, procedure return type)
templateArgs :: (MonadIO m,Location loc) => loc -> TIdentifier -> Type -> TcM loc m (Maybe [(Cond Type,IsVariadic)],Maybe [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)],Maybe Type)
templateArgs l (Left name) t = case t of
    DecT (DecType _ _ args hcstrs hfrees cstrs bfrees [] body) -> do -- a base template uses the base arguments
        return (Just $ map (mapFst (fmap varNameToType)) args,Nothing,Nothing)
    DecT (DecType _ _ args hcstrs hfrees cstrs bfrees specials body) -> do -- a specialization uses the specialized arguments
        return (Just $ map (mapFst (flip Cond Nothing)) specials,Nothing,Nothing)
templateArgs l (Right name) t = case t of
    DecT (DecType _ _ args hcstrs hfrees cstrs bfrees [] (ProcType _ n vars ret stmts _)) -> do -- include the return type
        return (Just $ map (mapFst (fmap varNameToType)) args,Just vars,Just ret)
    otherwise -> genTcError (locpos l) $ text "Invalid type for procedure template"

templateTDict :: Location loc => EntryEnv loc -> (TDict loc,TDict loc)
templateTDict e = case entryType e of
    DecT (DecType _ _ _ hd hfrees d bfrees _ _) -> (fmap (updpos l) hd,fmap (updpos l) d)
    otherwise -> (mempty,mempty)
  where l = entryLoc e

condVarType (Cond (VarName t n) c) = condType t c
condVar (Cond (VarName t n) c) = VarName (condType t c) n
condT (Cond t c) = condType t c

-- | renames the variables in a template to local names
localTemplate :: (VarsIdTcM loc m,Location loc) => EntryEnv loc -> TcM loc m (EntryEnv loc)
localTemplate e = case entryType e of
    DecT t -> do
        (t',_) <- localTemplateType emptySubstsProxy Map.empty (entryLoc e) t
        return $ EntryEnv (entryLoc e) $ DecT t'

localTemplateType :: (VarsIdTcM loc m,Location loc) => SubstsProxy VarIdentifier (TcM loc m) -> Map VarIdentifier VarIdentifier -> loc -> DecType -> TcM loc m (DecType,SubstsProxy VarIdentifier (TcM loc m))
localTemplateType (ss0::SubstsProxy VarIdentifier (TcM loc m)) ssBounds (l::loc) et = case et of
    DecType tpltid isrec (unzip -> (args,isVariadics)) hcstrs hfrees cstrs bfrees (unzip -> (specials,isVariadics2)) body -> do
        (hfrees',hfreelst) <- Utils.mapAndUnzipM freeVar $ Set.toList hfrees
        (bfrees',bfreelst) <- Utils.mapAndUnzipM freeVar $ Set.toList bfrees
        let freelst = hfreelst ++ bfreelst
        let freess :: SubstsProxy VarIdentifier (TcM loc m)
            freess = substsProxyFromList freelst `appendSubstsProxy` ss0
        let ssBounds' = ssBounds `Map.union` Map.fromList freelst
        (args',ss) <- uniqueVars l freess ssBounds' args
        specials' <- substProxy "localTplt" ss False ssBounds' specials
        (body',ss') <- localTemplateType ss ssBounds' l body
        hcstrs' <- substProxy "localTplt" ss' False ssBounds' hcstrs
        cstrs' <- substProxy "localTplt" ss' False ssBounds' cstrs
        return (DecType tpltid isrec (zip args' isVariadics) hcstrs' (Set.fromList hfrees') cstrs' (Set.fromList bfrees') (zip specials' isVariadics2) body',ss')
    ProcType p pid (unzip3 -> (isConsts,args,isVariadics)) ret stmts c -> do
        (args',ss) <- uniqueVars l ss0 ssBounds args
        ret' <- substProxy "localTplt" ss False ssBounds ret
        stmts' <- substProxy "localTplt" ss False ssBounds stmts
        return (ProcType p pid (zip3 isConsts args' isVariadics) ret' stmts' c,ss)
    otherwise -> return (et,ss0)
  where
    freeVar v = do
        j <- newTyVarId
        let v' = v { varIdUniq = Just j }
        return (v',(v,v'))
    uniqueVar :: loc -> SubstsProxy VarIdentifier (TcM loc m) -> Map VarIdentifier VarIdentifier -> Cond (VarName VarIdentifier Type) -> TcM loc m (Cond (VarName VarIdentifier Type),SubstsProxy VarIdentifier (TcM loc m))
    uniqueVar (l::loc) ss ssBounds (Cond i@(VarName t v) c) = do
        j <- uniqVarId (varIdBase v) Nothing
        t' <- substProxy "localTplt" ss False ssBounds t
        let i' = VarName t' j
        let ss' :: SubstsProxy VarIdentifier (TcM loc m)
            ss' = substsProxyFromTSubsts l (Map.singleton v (varNameToType i')) `appendSubstsProxy` ss
        c' <- substProxy "localTplt" ss' False ssBounds c
        return (Cond i' c',ss')
    uniqueVars :: loc -> SubstsProxy VarIdentifier (TcM loc m) -> Map VarIdentifier VarIdentifier -> [Cond (VarName VarIdentifier Type)] -> TcM loc m ([Cond (VarName VarIdentifier Type)],SubstsProxy VarIdentifier (TcM loc m))
    uniqueVars l ss ssBounds [] = return ([],ss)
    uniqueVars l ss ssBounds (x:xs) = do
        (x',ss') <- uniqueVar l ss ssBounds x
        (xs',ss'') <- uniqueVars l ss' ssBounds xs
        return (x' : xs',ss'')










