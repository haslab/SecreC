{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, ConstraintKinds, StandaloneDeriving, DeriveDataTypeable, MultiParamTypeClasses, TupleSections, GADTs, FlexibleContexts, ViewPatterns #-}

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
import Language.SecreC.TypeChecker.Index
import Language.SecreC.TypeChecker.SMT
import Language.SecreC.TypeChecker.Semantics

import Control.Monad
import Control.Monad.Except
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer
import Control.Monad.RWS as RWS hiding ((<>))

import Data.Word
import Data.Bifunctor
import Data.Either
import Data.Monoid hiding ((<>))
import Data.Unique
import Data.Maybe
import Data.Foldable as Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data hiding (cast)
import qualified Data.Map as Map
import Data.Generics hiding (LT,GT,cast,typeOf)
import qualified Data.Generics as Generics
import Data.List as List
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.Graph.Inductive.Query.TransClos as Graph

import Text.PrettyPrint as PP hiding (equals)

import Safe

-- * Constraint Engine

-- solves all hypotheses in the environment
solveHypotheses :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m [ICond]
solveHypotheses l = do
    hyps <- liftM Set.toList getHyps
    (_,dhyps) <- tcWith l "solveHypotheses" $ do
        addHeadTDict $ TDict (Graph.insNodes (map (\x -> (ioCstrId $ unLoc x,x)) hyps) Graph.empty) Set.empty Map.empty
        solve l
    addHeadTDict $ dhyps { tCstrs = Graph.empty }
    -- collect the result for the hypotheses
    liftM concat $ forM hyps $ \(Loc _ iok) -> do
        liftM (maybeToList . join) $ ioCstrResult l iok proxy
  where proxy = Proxy :: Proxy (Maybe (ICond))

-- | solves all constraints in the top environment
solve :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m ()
solve l = do
    env <- State.get
    let dict = headNe $ tDict env
    let gr = tCstrs dict
    unless (Graph.isEmpty gr) $ newErrorM $ tcNoDeps $ do
        liftIO $ putStrLn $ "solving " ++ " " ++ ppr l
        gr' <- buildCstrGraph $ flattenIOCstrGraphSet gr
        updateHeadTDict $ \d -> return ((),d { tCstrs = gr' })
        ss <- ppConstraints =<< liftM (headNe . tDict) State.get
        liftIO $ putStrLn $ "solve " ++ show (inTemplate env) ++ " [" ++ show ss ++ "\n]"
        solveCstrs l
        updateHeadTDict $ \d -> return ((),d { tCstrs = Graph.nfilter (`elem` Graph.nodes gr) (tCstrs d) })

priorityRoots :: (x,Loc loc IOCstr) -> (x,Loc loc IOCstr) -> Ordering
priorityRoots x y = priorityTCstr (kCstr $ unLoc $ snd x) (kCstr $ unLoc $ snd y)

solveCstrs :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m ()
solveCstrs l = do
    dict <- liftM (headNe . tDict) State.get
    ss <- ppConstraints dict
    liftIO $ putStrLn $ "solveCstrs [" ++ show ss ++ "\n]"
--    doc <- liftM ppTSubsts getTSubsts
--    liftIO $ putStrLn $ show doc
    let gr = tCstrs dict
    unless (Graph.isEmpty gr) $ do
        let roots = sortBy priorityRoots $ rootsGr gr -- sort by constraint priority
        when (List.null roots) $ error $ "solveCstrs: no root constraints to proceed"
        liftIO $ putStrLn $ "solveCstrsG [" ++ show (sepBy space $ map (pp . ioCstrId . unLoc . snd) roots) ++ "\n]"
        go <- trySolveSomeCstrs $ map snd roots
        case go of
            Left _ -> solveCstrs l
            Right errs -> do
                doAll <- liftM (not . inTemplate) State.get
--                guessCstrs l doAll errs
                guessError doAll errs
                return ()

-- Left True = one constraint solved
-- Left False = no remaining unsolved constraints
-- Right err = failed
type SolveRes = Either Bool [(Unique,TCstr,SecrecError)]

mergeSolveRes :: SolveRes -> SolveRes -> SolveRes
mergeSolveRes (Left True) b = Left True
mergeSolveRes (Left False) b = b
mergeSolveRes a (Left True) = Left True
mergeSolveRes a (Left False) = a
mergeSolveRes (Right a) (Right b) = Right (a ++ b)

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (VarsIdTcM loc m,Location loc) => [Loc loc IOCstr] -> TcM loc m SolveRes
trySolveSomeCstrs = foldlM solveBound (Left False)
    where
    solveBound b x@(Loc l iok) = do
        doAll <- liftM (not . inTemplate) State.get
        ok <- trySolveCstr doAll x
        return (mergeSolveRes b ok)

getErrors :: [(Unique,TCstr,SecrecError)] -> [SecrecError]
getErrors = map thr3 . flattenErrors
    
flattenErrors :: [(Unique,TCstr,SecrecError)] -> [(Unique,TCstr,SecrecError)]
flattenErrors [] = []
flattenErrors ((x,y,MultipleErrors errs):xs) = flattenErrors (map (\e -> (x,y,e)) errs ++ xs)
flattenErrors (err:xs) = err : flattenErrors xs

-- gets the first group of possible multiple substitutions from a set constraint errors
getOpts :: (Monad m,Location loc) => [(Unique,TCstr,SecrecError)] -> TcM loc m (Maybe [TSubsts])
getOpts [] = return Nothing
getOpts ((u,x,y):xs) = case errorOpts x of
    Just opts -> do
        done <- isChoice u
        if done
            then getOpts xs
            else do
                addChoice u
                return $ Just opts
    otherwise -> getOpts xs

errorOpts :: TCstr -> Maybe [TSubsts]
errorOpts = everything append (mkQ Nothing aux)
    where
    aux :: TCstr -> Maybe [TSubsts]
    aux (TcK (MultipleSubstitutions v opts)) = Just $ map (Map.singleton v . fst) opts
    aux _ = Nothing
    append Nothing y = y
    append x y = x
    
filterErrors :: (Monad m,Location loc) => Bool -> [(Unique,TCstr,SecrecError)] -> TcM loc m ([(Unique,TCstr,SecrecError)])
filterErrors False errs = do
    let errs1 = filter (not . isOrWarnError . thr3) errs
    let errs2 = flattenErrors $ filter (not . isGlobalCstr . snd3) errs1
    let errs3 = filter (not . isHaltError . thr3) errs2
    let errs4 = filter (not . isHypCstr . snd3) errs3
    return errs4
filterErrors True errs = filterWarnings errs

filterWarnings :: (Monad m,Location loc) => [(Unique,TCstr,SecrecError)] -> TcM loc m [(Unique,TCstr,SecrecError)]
filterWarnings = filterM $ \x -> if isOrWarnError (thr3 x)
    then do
        errWarn $ thr3 x
        return False
    else return True

guessError :: (MonadIO m,Location loc) => Bool -> [(Unique,TCstr,SecrecError)] -> TcM loc m ()
guessError doAll errs = do
    (errs') <- filterErrors doAll errs
    unless (null errs') $ throwError $ MultipleErrors $ getErrors errs'

--guessCstrs :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> [(Unique,TCstr,SecrecError)] -> TcM loc m ()
--guessCstrs l False errs = guessError False errs
--guessCstrs l True errs = do
--    mb <- getOpts errs
--    case mb of
--        Nothing -> guessError True errs
--        Just opts -> do
--            tries <- steps opts
--            unless (List.null tries) $ throwError $ Halt $ TypecheckerError (locpos l) $ MultipleTypeSubstitutions tries
--  where
--    tryStep o e = text "Tried substitution:" <+> quotes (pp o) $+$ text "Sub-error:" <+> pp e
--    steps [] = return []
--    steps (o:os) = do
--        tryO <- step o
--        case tryO of
--            Nothing -> return []
--            Just err -> liftM (err:) (steps os)
--    step o = (do
----        ss <- ppConstraints =<< liftM (headNe . tDict) State.get
----        liftIO $ putStrLn $ "guessStep [" ++ show ss ++ "\n]" ++ ppr o
--        addSubsts o
--        solveCstrs l
--        return Nothing) `catchError` \e -> return (Just $ tryStep o e)

-- since templates are only resolved at instantiation time, we prevent solving of overloadable constraints
trySolveCstr :: (VarsIdTcM loc m,Location loc) => Bool -> Loc loc IOCstr -> TcM loc m SolveRes
trySolveCstr False (Loc l iok) | isGlobalCstr (kCstr iok) = do
    return $ Right [(uniqId $ kStatus iok,kCstr iok,TypecheckerError (locpos l) $ Halt $ GenTcError $ text "Unsolved global constraint")]
trySolveCstr doAll (Loc l iok) = catchError
    (solveIOCstr l iok >> return (Left True))
    (\e -> return $ Right [(uniqId $ kStatus iok,kCstr iok,e)])

solveIOCstr :: (VarsIdTcM loc m,Location loc) => loc -> IOCstr -> TcM loc m ShowOrdDyn
solveIOCstr l iok = resolveIOCstr l iok $ \k -> do
--    liftIO $ putStrLn $ "solveIOCstr " ++ ppr iok
    gr <- liftM (tCstrs . headNe . tDict) State.get
    let (ins,_,_,outs) = fromJustNote ("solveCstrNodeCtx " ++ ppr iok) $ contextGr gr (ioCstrId iok)
    let ins'  = map (fromJustNote "ins" . Graph.lab gr . snd) ins
    let outs' = map (fromJustNote "outs" . Graph.lab gr . snd) outs
    (res,rest) <- tcWith l ("solveIOCstr " ++ ppr iok) $ resolveTCstr l k
    addHeadTDict $ rest { tCstrs = Graph.empty }
    unless (Graph.isEmpty $ tCstrs rest) $ do
        replaceCstrWithGraph l (ioCstrId iok) (Set.fromList ins') (tCstrs rest) (Set.fromList outs')
    return res

-- * Throwing Constraints

checkCstrM :: (VarsIdTcM loc m,Location loc) => loc -> Set (Loc loc IOCstr) -> CheckCstr -> TcM loc m ()
checkCstrM l deps k = withDeps LocalScope $ do
    addDeps LocalScope deps
    tCstrM l $ CheckK k

tCstrsM :: (VarsIdTcM loc m,Location loc) => loc -> [TCstr] -> TcM loc m ()
tCstrsM l = mapM_ (tCstrM l)

tCstrM :: (VarsIdTcM loc m,Location loc) => loc -> TCstr -> TcM loc m ()
tCstrM l k | isTrivialCstr k = return ()
tCstrM l k = do
--    liftIO $ putStrLn $ "tCstrM " ++ ppr k
    newTCstr l k

tcCstrsM :: (VarsIdTcM loc m,Location loc) => loc -> [TcCstr] -> TcM loc m ()
tcCstrsM l = mapM_ (tcCstrM l)

tcCstrM :: (VarsIdTcM loc m,Location loc) => loc -> TcCstr -> TcM loc m ()
tcCstrM l k = tCstrM l $ TcK k

tcTopCstrM :: (VarsIdTcM loc m,Location loc) => loc -> TcCstr -> TcM loc m ()
tcTopCstrM l k = newErrorM $ tcCstrM l k

newTCstr :: (VarsIdTcM loc m,Location loc) => loc -> TCstr -> TcM loc m ()
newTCstr l k = do
    doSome <- liftM inTemplate State.get
    deps <- getDeps
    delay <- askErrorM'
    let k' = DelayedK k delay
    iok <- newTemplateConstraint l k'
    addIOCstrDependenciesM deps (Loc l iok) Set.empty
    
    unless ((doSome || not (Set.null deps)) && isGlobalCstr k) $ do
        catchError
            (newErrorM $ resolveIOCstr l iok (resolveTCstr l) >> return ())
            (\e -> unless (isHaltError e) $ throwError e)
                
resolveTCstr :: (VarsIdTcM loc m,Location loc) => loc -> TCstr -> TcM loc m ShowOrdDyn
resolveTCstr l (TcK k) = liftM ShowOrdDyn $ withDeps GlobalScope $ do
    resolveTcCstr l k
resolveTCstr l (HypK h) = liftM ShowOrdDyn $ withDeps GlobalScope $ do
    resolveHypCstr l h
resolveTCstr l (CheckK c) = liftM ShowOrdDyn $ withDeps GlobalScope $ do
    resolveCheckCstr l c
resolveTCstr l (DelayedK k (i,err)) = addErrorM' l (i,err) $ resolveTCstr l k

-- tests if a constraint is only used as part of an hypothesis
--isHypInGraph :: Int -> IOCstrGraph loc -> Bool
--isHypInGraph kid gr = case Graph.match kid gr of
--    (Nothing,gr') -> False
--    (Just (_,_,(kCstr . unLoc) -> HypK {},_),gr') -> True
--    (Just (_,_,_,outs),gr') -> all (flip isHypInGraph gr' . snd) outs

resolveTcCstr :: (VarsIdTcM loc m,Location loc) => loc -> TcCstr -> TcM loc m ()
resolveTcCstr l k = do
--    gr <- liftM (tCstrs . headNe . tDict) State.get
--    let warn = isHypInGraph kid gr
--    liftIO $ putStrLn $ "resolve " ++ show warn ++ " " ++ ppr k
--    if warn then newErrorM $ orWarn_ $ resolveTcCstr' k else 
    resolveTcCstr' k
  where
    resolveTcCstr' k@(TRet t x) = do
        res <- templateDecReturn l t
        addErrorM l
            (TypecheckerError (locpos l) . TemplateSolvingError (text "Return type of" <+> quotes (pp t)))
            (tcCstrM l $ Unifies x res)
    resolveTcCstr' k@(TDec n args x) = do
        (res) <- matchTemplate l True (Left n) (Just args) Nothing Nothing Nothing (checkTemplateType $ fmap (const l) n)
        addErrorM l
            (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp n <+> parens (sepBy comma $ map pp args))))
            (tcCstrM l $ Unifies (DecT x) (DecT res))
    resolveTcCstr' k@(PDec (Left n) specs args r x xs) = do
        let doCoerce = isJust xs
        (res) <- matchTemplate l doCoerce (Right $ Left n) specs (Just args) (Just r) xs (checkProcedure $ fmap (const l) n)
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp r <+> pp n <+> parens (sepBy comma $ map pp args)))) $ do
            tcCstrM l $ Unifies (DecT x) (DecT res)
    resolveTcCstr' k@(PDec (Right o) specs args r x xs) = do
        let doCoerce = isJust xs
        (res) <- matchTemplate l doCoerce (Right $ Right o) specs (Just args) (Just r) xs (checkOperator $ fmap (const l) o)
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp r <+> pp o <+> parens (sepBy comma $ map pp args)))) $ do
            tcCstrM l $ Unifies (DecT x) (DecT res)
    resolveTcCstr' k@(Equals t1 t2) = do
        equals l t1 t2
    resolveTcCstr' k@(Coerces e1 x2) = do
        coerces l e1 x2
    resolveTcCstr' k@(Coerces2 e1 e2 x1 x2) = do
        coerces2 l e1 e2 x1 x2
    resolveTcCstr' k@(CoercesSec e1 x2) = do
        coercesSec l e1 x2
    resolveTcCstr' k@(Coerces2Sec e1 e2 x1 x2) = do
        coerces2Sec l e1 e2 x1 x2
    resolveTcCstr' k@(Unifies t1 t2) = do
        unifies l t1 t2
    resolveTcCstr' k@(UnifiesSizes szs1 szs2) = do
        unifiesSizes l szs1 szs2
    resolveTcCstr' k@(SupportedPrint t xs) = do
        isSupportedPrint l t xs
    resolveTcCstr' k@(ProjectStruct t a x) = do
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedFieldProjection (pp t) (pp a <+> char '=' <+> pp x))
            (projectStructField l t a >>= \res -> tcCstrM l $ Unifies x res)
    resolveTcCstr' k@(ProjectMatrix ct rngs x) = do
        ct' <- ppM l ct
        rngs' <- ppArrayRangesM l rngs
        x' <- ppM l x
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedMatrixProjection ct' (brackets rngs' <+> char '=' <+> x'))
            (projectMatrixType l ct rngs >>= \res -> tcCstrM l $ Unifies x res)
    resolveTcCstr' k@(IsReturnStmt cs ret) = do
        isReturnStmt l cs ret
    resolveTcCstr' (MultipleSubstitutions v s) = do
        multipleSubstitutions l v s
    resolveTcCstr' (MatchTypeDimension t d) = matchTypeDimension l t d
    resolveTcCstr' (EvalVarExprs t) = evalVarExprs l t
    resolveTcCstr' (IsValid c) = do
        x <- ppM l c
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid x) $ do
            ic <- prove l "resolve isValid" $ expr2ICond $ fmap (Typed l) c
            isValid l ic

resolveHypCstr :: (VarsIdTcM loc m,Location loc) => loc -> HypCstr -> TcM loc m (Maybe (ICond))
resolveHypCstr l hyp = do
    doSome <- liftM inTemplate State.get
    if doSome -- if we don't need to solve all constraints we accept no less than solving the hypothesis
        then liftM Just $ resolveHypCstr' hyp
        else newErrorM $ addErrorM l (TypecheckerError (locpos l) . FailAddHypothesis (pp hyp)) $ orWarn $ resolveHypCstr' hyp
  where
    resolveHypCstr' (HypCondition c) = expr2ICond $ fmap (Typed l) c
    resolveHypCstr' (HypNotCondition c) = liftM INot $ expr2ICond $ fmap (Typed l) c
    resolveHypCstr' (HypEqual e1 e2) = do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return $ i1 .==. i2
    
resolveCheckCstr :: (VarsIdTcM loc m,Location loc) => loc -> CheckCstr -> TcM loc m ()
resolveCheckCstr l k = addErrorM l (TypecheckerError (locpos l) . StaticAssertionFailure (pp k)) $ orWarn_ $ do
    resolveCheckCstr' k
  where
    resolveCheckCstr' (CheckAssertion c) = checkAssertion l c
    resolveCheckCstr' (CheckEqual e1 e2) = checkEqual l e1 e2
    resolveCheckCstr' (CheckArrayAccess t d low up sz) = checkArrayAccess l t d low up sz

ioCstrResult :: (IsScVar a,MonadIO m,Location loc) => loc -> IOCstr -> Proxy a -> TcM loc m (Maybe a)
ioCstrResult l iok proxy = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated t -> liftM Just $ cstrResult l (kCstr iok) proxy t
        Erroneous err -> return Nothing
        Unevaluated -> return Nothing
    where
    cstrResult :: (IsScVar a,Monad m,Location loc) => loc -> TCstr -> Proxy a -> ShowOrdDyn -> TcM loc m a
    cstrResult l k (Proxy::Proxy t) dyn = case fromShowOrdDyn dyn of
        Nothing -> genError (locpos l) $ text "Wrong IOCstr output type" <+> text (show dyn) <+> text "::" <+> text (show $     applyShowOrdDyn Generics.typeOf dyn) <+> text "with type" <+> text (show $ Generics.typeOf (error "applyShowOrdDyn"::t)) <+> pp k
        Just x -> return x

tcProve :: (VarsIdTcM loc m,Location loc) => loc -> String -> TcM loc m a -> TcM loc m (a,TDict loc)
tcProve l msg m = do
    newDict l $ "tcProve " ++ msg
    x <- m
    solve l
    d <- liftM (headNe . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (ConsNe x xs) = xs

proveWith :: (VarsIdTcM loc m,Location loc) => loc -> String -> TcM loc m a -> TcM loc m (Either SecrecError (a,TDict loc))
proveWith l msg proof = try `catchError` (return . Left)
    where
    try = liftM Right $ tcProve l msg proof

prove :: (VarsIdTcM loc m,Location loc) => loc -> String -> TcM loc m a -> TcM loc m a
prove l msg m = do
    (a,dict) <- tcProve l msg m
    addHeadTDict dict
    return a

-- * Solving constraints

--multipleSubstitutions :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> [(Type,[TcCstr])] -> TcM loc m ()
--multipleSubstitutions l v ss = do
--    t <- resolveTVar l v
--    ok <- matchOne l t ss
--    case ok of
--        Nothing -> return ()
--        Just errs -> addErrorM l Halt $ tcError (locpos l) $ MultipleTypeSubstitutions errs

multipleSubstitutions :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> [(Type,[TcCstr])] -> TcM loc m ()
multipleSubstitutions l v ss = do
    ok <- matchAll l (SecT $ SVar v AnyKind) ss []
    case ok of
        [] -> return ()
        errs -> tcError (locpos l) $ Halt $ MultipleTypeSubstitutions $ map pp errs

matchAll :: (VarsIdTcM loc m,Location loc) => loc -> Type -> [(Type,[TcCstr])] -> [SecrecError] -> TcM loc m [SecrecError]
matchAll l t [] errs = return errs
matchAll l t (x:xs) errs = catchError
    (matchOne l t x >> return [])
    (\e -> matchAll l t xs (errs++[e]))

matchOne :: (VarsIdTcM loc m,Location loc) => loc -> Type -> (Type,[TcCstr]) -> TcM loc m ()
matchOne l t1 (t,deps) = do
    (_,ks) <- tcWithCstrs l "matchOne" $ tcCstrM l $ Unifies t1 t
    withDependencies ks $ mapM_ (tcCstrM l) deps
    solve l

--matchOne :: (VarsIdTcM loc m,Location loc) => loc -> Type -> [(Type,[TcCstr])] -> TcM loc m (Maybe [Doc])
--matchOne l t1 [] = return $ Just []
--matchOne l t1 ((t,ks):ts) = do
--    ok <- tryUnifies l t1 t
--    case ok of
--        Nothing -> do
--            mapM_ (tcCstrM l) ks
--            --liftM conc $ mapM (\t -> tryNotUnifies l t1 t) $ map fst ts
--            return $ Nothing
--        Just err -> liftM (fmap (pp err:)) $ matchOne l t1 ts
-- where
--    conc [] = Nothing
--    conc (Left x:xs) = fmap (x:) (conc xs)
--    conc (Right x:xs) = fmap (pp x:) (conc xs)
        
tryUnifies :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m (Maybe SecrecError)
tryUnifies l t1 t2 = (prove l "tryUnifies" $ unifies l t1 t2 >> return Nothing) `catchError` (return . Just)

tryUnifiesBool :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m Bool
tryUnifiesBool l t1 t2 = do
    mb <- tryUnifies l t1 t2
    case mb of
        Nothing -> return True
        Just err -> if isHaltError err
            then throwError err
            else return False

-- can the second argument be given the first type?
isTyOf :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m Bool
isTyOf l tt t = tryUnifiesBool l (tyOf t) tt

--tryNotUnifies :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m (Either Doc SecrecError)
--tryNotUnifies l t1 t2 = (prove l True (unifies l t1 t2) >> return (Right err)) `catchError` handleErr
--    where
--    err = GenericError (locpos l) $ text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "should not unify."
--    ok = text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "unify."
--    handleErr e = if isHaltError e
--        then throwError e
--        else return $ Left ok

-- checks if two types are equal, without using coercions, not performing substitutions
equals :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m ()
equals l (NoType _) (NoType _) = return ()
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
equals l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM l $ Equals b1 b2
    equalsExprTy l sz1 sz2
equals l (SType k1) (SType k2) | k1 == k2 = return ()
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
equals l (CondType t1 c1) (CondType t2 c2) = do
    equals l t1 t2
    equalsExprTy l c1 c2
equals l (VArrayT a1) (VArrayT a2) = equalsArray l a1 a2
equals l t1 t2 = constraintError (EqualityException "type") l t1 pp t2 pp Nothing

equalsArray :: (VarsIdTcM loc m,Location loc) => loc -> VArrayType -> VArrayType -> TcM loc m ()
equalsArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    equalsList l ts1 ts2
    tcCstrM l $ Equals b1 b2
equalsArray l (VAVar v1 b1 sz1) (VAVar v2 b2 sz2) | v1 == v2 = do
    tcCstrM l $ Equals b1 b2
    equalsExprTy l  sz1 sz2
equalsArray l t1 t2 = constraintError (EqualityException "array") l t1 pp t2 pp Nothing

equalsSys :: (VarsIdTcM loc m,Location loc) => loc -> SysType -> SysType -> TcM loc m ()
equalsSys l (SysPush t1) (SysPush t2) = tcCstrM l $ Equals t1 t2
equalsSys l (SysRet t1) (SysRet t2) = tcCstrM l $ Equals t1 t2
equalsSys l (SysRef t1) (SysRef t2) = tcCstrM l $ Equals t1 t2
equalsSys l (SysCRef t1) (SysCRef t2) = tcCstrM l $ Equals t1 t2
equalsSys l t1 t2 = constraintError (EqualityException "syscall type") l t1 pp t2 pp Nothing

equalsSec :: (VarsIdTcM loc m,Location loc) => loc -> SecType -> SecType -> TcM loc m ()
equalsSec l Public Public = return ()
equalsSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
equalsSec l (SVar v1 k1) (SVar v2 k2) | v1 == v2 && k1 == k2 = return ()
equalsSec l (SVar v _) s2 = do
    s1 <- resolveSVar l v
    tcCstrM l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 (SVar v _) = do
    s2 <- resolveSVar l v
    tcCstrM l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 s2 = constraintError (EqualityException "security type") l s1 pp s2 pp Nothing

equalsDec :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> DecType -> TcM loc m ()
equalsDec l (DVar v1) (DVar v2) | v1 == v2 = return ()
equalsDec l (DVar v1) d2 = do
    d1 <- resolveDVar l v1
    tcCstrM l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 (DVar v2) = do
    d2 <- resolveDVar l v2
    tcCstrM l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 d2 | decTypeTyVarId d1 == decTypeTyVarId d2 = return ()
equalsDec l d1 d2 = constraintError (EqualityException "declaration type") l d1 pp d2 pp Nothing

equalsComplex :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc m ()
equalsComplex l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
equalsComplex l (ArrayLit es1) (ArrayLit es2) = do
    constraintList (EqualityException "size") (equalsExprTy l) l es1 es2
    return ()
equalsComplex l (CType s1 t1 d1 sz1) (CType s2 t2 d2 sz2) = do
    tcCstrM l $ Equals (SecT s1) (SecT s2)
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
    equalsExprTy l d1 d2
    equalsSizes l sz1 sz2
equalsComplex l (CVar v1) (CVar v2) | v1 == v2 = return ()
equalsComplex l (CVar v) c2 = do
    c1 <- resolveCVar l v
    tcCstrM l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l c1 (CVar v) = do
    c2 <- resolveCVar l v
    tcCstrM l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l Void Void = return ()
equalsComplex l c1 c2 = constraintError (EqualityException "complex type") l c1 pp c2 pp Nothing

equalsBase :: (VarsIdTcM loc m,Location loc) => loc -> BaseType -> BaseType -> TcM loc m ()
equalsBase l (BVar v1) (BVar v2) | v1 == v2 = return ()
equalsBase l (BVar v) t2 = do
    t1 <- resolveBVar l v
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
equalsBase l t1 (BVar v) = do
    t2 <- resolveBVar l v
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
equalsBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2
equalsBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
equalsBase l b1 b2 = constraintError (EqualityException "base type") l b1 pp b2 pp Nothing

equalsFoldable :: (VarsIdTcM loc m,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc m ()
equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)

equalsList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m ()
equalsList l [] [] = return ()
equalsList l (x:xs) (y:ys) = do
    tcCstrM l $ Equals x y
    equalsList l xs ys
equalsList l xs ys = constraintError (EqualityException "type") l xs pp ys pp Nothing

zipSizes :: (VarsIdTcM loc m,Location loc) => loc -> [Expression VarIdentifier Type] -> [Expression VarIdentifier Type] -> TcM loc m [(Expression VarIdentifier Type,Expression VarIdentifier Type)]
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

equalsPrim :: (VarsIdTcM loc m,Location loc) => loc -> PrimitiveDatatype () -> PrimitiveDatatype () -> TcM loc m ()
equalsPrim l p1 p2 | p1 == p2 = return ()
equalsPrim l t1 t2 = constraintError (EqualityException "primitive type") l t1 pp t2 pp Nothing

expandCTypeVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m ComplexType
expandCTypeVar l v = do
    d <- newDomainTyVar AnyKind
    t <- newBaseTyVar
    dim <- newDimVar
    szs <- newSizesVar dim
    let ct = CType d t dim szs
    addSubstM l (VarName TType v) $ ComplexT ct
    return ct

-- | Non-directed coercion, with implicit security coercions.
-- Returns the unified type.
-- applies substitutions
coerces2 :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coerces2 l e1@(loc -> BaseT t1) e2@(loc -> BaseT t2) x1 x2 = do
    tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
    unifiesExprTy l (varExpr x1) e1
    unifiesExprTy l (varExpr x2) e2
coerces2 l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT t2) x1 x2 = coerces2Complex l e1 e2 x1 x2
coerces2 l e1@(loc -> ComplexT c1) e2@(loc -> BaseT b2) x1 x2 = do
    coerces2Complex l e1 (updLoc e2 $ ComplexT $ defCType b2) x1 x2
coerces2 l e1@(loc -> BaseT b1) e2@(loc -> ComplexT c2) x1 x2 =
    coerces2Complex l (updLoc e1 $ ComplexT $ defCType b1) e2 x1 x2
coerces2 l e1 e2 x1 x2 = addErrorM l (TypecheckerError (locpos l) . BiCoercionException "type" Nothing (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM l $ Unifies (loc e1) (loc e2)
    unifiesExprTy l (varExpr x1) e1
    unifiesExprTy l (varExpr x2) e2

coerces2Complex :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coerces2Complex l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT t2) x1 x2 | isVoid t1 || isVoid t2 = addErrorM l (TypecheckerError (locpos l) . BiCoercionException "complex type" Nothing (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM l $ Unifies (ComplexT t1) (ComplexT t2)
    unifiesExprTy l (varExpr x1) e1
    unifiesExprTy l (varExpr x2) e2
coerces2Complex l e1@(loc -> t1@(ComplexT (isLitCType -> True))) e2@(loc -> t2@(ComplexT (isLitCType -> True))) x1 x2 = do
    tcCstrM l $ Unifies t1 t2
    tcCstrM l $ Coerces e1 x1
    tcCstrM l $ Coerces e2 x2
coerces2Complex l e1@(loc -> t1@(ComplexT (TyLit lit))) e2@(loc -> t2@(ComplexT ct2)) x1 x2 = do
    prove l "coerces2Complex" $ tcCstrM l $ Unifies (loc x1) t2
    coercesLitComplex l e1 x1 -- literals are never variables
    unifiesExprTy l (varExpr x2) e2
coerces2Complex l e1@(loc -> ComplexT (ArrayLit lit)) e2@(loc -> ComplexT t2) x1 x2 = do
    prove l "coerces2Complex" $ tcCstrM l $ Unifies (loc x1) (ComplexT t2)
    coercesArrayLitComplex l e1 x1 -- literals are never variables
    unifiesExprTy l (varExpr x2) e2
coerces2Complex l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT (TyLit lit)) x1 x2 = do
    prove l "coerces2Complex" $ tcCstrM l $ Unifies (loc x2) (ComplexT t1)
    coercesLitComplex l e2 x2 -- literals are never variables
    unifiesExprTy l (varExpr x1) e1
coerces2Complex l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT (ArrayLit lit)) x1 x2 = do
    prove l "coerces2Complex" $ tcCstrM l $ Unifies (loc x2) (ComplexT t1)
    coercesArrayLitComplex l e2 x2 -- literals are never variables
    unifiesExprTy l (varExpr x1) e1
coerces2Complex l e1@(loc -> ComplexT ct1@(CType s1 t1 d1 sz1)) e2@(loc -> ComplexT ct2@(CType s2 t2 d2 sz2)) x1 x2 = addErrorM l (TypecheckerError (locpos l) . (BiCoercionException "complex type") Nothing (ppExprTy e1) (ppExprTy e2) . Just) $ do
    (_,ks) <- tcWithCstrs l "coerces2Complex" $ do
        tcCstrM l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
        unifiesExprTy l d1 d2
        tcCstrM l $ Coerces2Sec e1 e2 x1 x2
    withDependencies ks $ tcCstrM l $ UnifiesSizes sz1 sz2
coerces2Complex l e1@(loc -> ComplexT t1@(CVar v1)) e2@(loc -> ComplexT t2@(CVar v2)) x1 x2 = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just t1',Just t2') -> tcCstrM l $ Coerces2 (updLoc e1 $ ComplexT t1') (updLoc e2 $ ComplexT t2') x1 x2
        (Just t1',Nothing) -> tcCstrM l $ Coerces2 (updLoc e1 $ ComplexT t1') e2 x1 x2
        (Nothing,Just t2') -> tcCstrM l $ Coerces2 e1 (updLoc e2 $ ComplexT t2') x1 x2
        (Nothing,Nothing) -> constraintError (BiCoercionException "complex type" Nothing) l e1 ppExprTy e2 ppExprTy Nothing
coerces2Complex l e1@(loc -> ComplexT t1@(CVar v)) e2@(loc -> ComplexT t2) x1 x2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1' -> do
            tcCstrM l $ Coerces2 (updLoc e1 $ ComplexT t1') e2 x1 x2
        Nothing -> do
            t1' <- expandCTypeVar l v
            tcCstrM l $ Coerces2 (updLoc e1 $ ComplexT t1') e2 x1 x2
coerces2Complex l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT t2@(CVar v)) x1 x2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2' -> do
            tcCstrM l $ Coerces2 e1 (updLoc e2 $ ComplexT t2') x1 x2
        Nothing -> do
            t2' <- expandCTypeVar l v
            tcCstrM l $ Coerces2 e1 (updLoc e2 $ ComplexT t2') x1 x2
coerces2Complex l e1 e2 x1 x2 = constraintError (BiCoercionException "complex type" Nothing) l e1 ppExprTy e2 ppExprTy Nothing

coerces2Sec :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coerces2Sec l e1@(loc -> ComplexT ct1) e2@(loc -> ComplexT ct2) x1 x2 = do
    let s1 = cSec ct1
    let s2 = cSec ct2
    opts <- TcM $ lift Reader.ask
    if implicitClassify opts
        then do
            let left = prove l "coerces2Sec left" $ do
                (_,ks) <- tcWithCstrs l "coerces2Sec left" $ tcCstrM l $ Unifies (loc x1) (ComplexT $ setCSec ct1 s2)
                withDependencies ks $ do
                    tcCstrM l $ CoercesSec e1 x1
                    unifiesExprTy l (varExpr x2) e2
            let right = prove l "coerces2Sec right" $ do
                (_,ks) <- tcWithCstrs l "coerces2Sec right" $ tcCstrM l $ Unifies (loc x2) (ComplexT $ setCSec ct2 s1)
                withDependencies ks $ do
                    tcCstrM l $ CoercesSec e2 x2
                    unifiesExprTy l (varExpr x1) e1
            addErrorM l
                (TypecheckerError (locpos l) . BiCoercionException "security type" Nothing (ppExprTy e1) (ppExprTy e2) . Just)
                (left `mplus` right)
        else do
            tcCstrM l $ Unifies (ComplexT ct1) (ComplexT ct2)
            unifiesExprTy l (varExpr x1) e1
            unifiesExprTy l (varExpr x2) e2

coercesE :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Type -> TcM loc m (Expression VarIdentifier Type)
coercesE l e1 t2 = do
    x2 <- newTypedVar "coerces" t2
    tcCstrM l $ Coerces e1 x2
    return $ varExpr x2

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coerces l e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(BaseT b2)) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "base type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    unifiesExprTy l (varExpr x2) e1
coerces l e1@(loc -> t1@(ComplexT ct1)) x2@(loc -> t2@(ComplexT ct2)) = coercesComplex l e1 x2
coerces l e1@(loc -> t1@(ComplexT c1)) x2@(loc -> t2@(BaseT b2)) = coercesComplex l e1 (updLoc x2 $ ComplexT $ defCType b2)
coerces l e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(ComplexT c2)) = coercesComplex l (updLoc e1 $ ComplexT $ defCType b1) x2
coerces l e1 x2 = addErrorM l (TypecheckerError (locpos l) . (CoercionException "type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    unifiesExprTy l (varExpr x2) e1

coercesComplexE :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> TcM loc m (Expression VarIdentifier Type)
coercesComplexE l e1 ct2 = do
    x2 <- newTypedVar "coerces_complex" $ ComplexT ct2
    coercesComplex l e1 x2
    return $ varExpr x2

coercesComplex :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coercesComplex l e1@(loc -> ComplexT t1) x2@(loc -> ComplexT t2) | isVoid t1 || isVoid t2 = addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") (ppExprTy e1) (ppExprTy x2) . Just) $ do
    unifiesExprTy l (varExpr x2) e1
coercesComplex l e1@(loc -> ComplexT t1@(TyLit lit)) x2@(loc -> t2) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") (ppExprTy e1) (ppExprTy x2) . Just) $ do
    coercesLitComplex l e1 x2 -- literals are never variables
coercesComplex l e1@(loc -> ComplexT t1@(ArrayLit lit)) x2@(loc -> ComplexT t2) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    coercesArrayLitComplex l e1 x2 -- literals are never variables
coercesComplex l e1@(loc -> ComplexT ct1@(CType s1 t1 d1 sz1)) x2@(loc -> ComplexT ct2@(CType s2 t2 d2 sz2)) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    (_,ks) <- tcWithCstrs l "coercesComplex" $ do
        tcCstrM l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
        unifiesExprTy l d1 d2
        tcCstrM l $ CoercesSec e1 x2
    withDependencies ks $ tcCstrM l $ UnifiesSizes sz1 sz2
coercesComplex l e1@(loc -> ComplexT ct1@(CVar v1)) x2@(loc -> ComplexT ct2@(CVar v2)) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just ct1',Just ct2') -> do
            tcCstrM l $ Coerces (updLoc e1 $ ComplexT ct1') (updLoc x2 $ ComplexT ct2')
        (Just ct1',Nothing) -> do
            tcCstrM l $ Coerces (updLoc e1 $ ComplexT ct1') x2
        (Nothing,Just ct2') -> do
            tcCstrM l $ Coerces e1 (updLoc x2 $ ComplexT ct2')
        (Nothing,Nothing) -> constraintError (CoercionException "complex type") l e1 ppExprTy x2 ppVarTy Nothing
coercesComplex l e1@(loc -> ComplexT (CVar v)) x2@(loc -> ComplexT ct2) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct1' -> coercesComplex l (updLoc e1 $ ComplexT ct1') x2
        Nothing -> do
            ct1' <- expandCTypeVar l v
            tcCstrM l $ Coerces (updLoc e1 $ ComplexT ct1') x2
coercesComplex l e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT (CVar v)) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct2' -> coercesComplex l e1 (updLoc x2 $ ComplexT ct2')
        Nothing -> do
            ct2' <- expandCTypeVar l v
            tcCstrM l $ Coerces e1 (updLoc x2 $ ComplexT ct2')
coercesComplex l e1 x2 = constraintError (CoercionException "complex type") l e1 ppExprTy x2 ppVarTy Nothing

cSec (CType s _ _ _) = s

coercesSecE :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> SecType -> TcM loc m (Expression VarIdentifier Type)
coercesSecE l e1 s2 = do
    ct1 <- typeToComplexType l (loc e1)
    let t2 = ComplexT $ setCSec ct1 s2
    x2 <- newTypedVar "coerces_sec" t2
    coercesSec l e1 x2
    return $ varExpr x2

coercesSec :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coercesSec l e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT t2) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "security type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    opts <- TcM $ lift Reader.ask
    if implicitClassify opts
        then do
            coercesSec' l e1 ct1 x2 (cSec t2)
        else unifiesExprTy l (varExpr x2) e1

coercesSec' :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> ComplexType -> VarName VarIdentifier Type -> SecType -> TcM loc m ()
coercesSec' l e1 (cSec -> SVar v1 k1) x2 (SVar v2 k2) | v1 == v2 && k1 == k2 = do
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 (cSec -> Public) x2 Public = do
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> s1@Public) x2 s2@(SVar v AnyKind) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2' -> coercesSec' l e1 ct1 x2 s2'
        Nothing -> do
            opts <- askOpts
            if implicitClassify opts
                then do
                    v' <- newDomainTyVar $ PrivateKind Nothing
                    ks <- classifiesCstrs l e1 ct1 x2 s2
                    tcCstrM l $ MultipleSubstitutions v [(SecT Public,[Unifies (loc x2) (loc e1),Unifies (IdxT $ varExpr x2) (IdxT e1)]),(SecT v',ks)]
                else do
                    tcCstrM l $ Unifies (SecT s1) (SecT s2)
                    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Public) x2 s2@(SVar v k) = do
    s2' <- resolveSVar l v
    coercesSec' l e1 ct1 x2 s2'
coercesSec' l e1 ct1@(cSec -> s1@(SVar v _)) x2 s2@(Public) = do
    tcCstrM l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Private d1 k1) x2 (Private d2 k2) | d1 == d2 && k1 == k2 = do
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> s1@(Private d1 k1)) x2 s2@(SVar v _) = do
    tcCstrM l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> s1@(SVar v1 (PrivateKind k1))) x2 s2@(SVar v2 k2) = do
    tcCstrM l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> s1@(SVar v1 AnyKind)) x2 s2@(Private d2 k2) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> do
            let ct1' = setCSec ct1 s1'
            coercesSec' l (updLoc e1 $ ComplexT ct1') ct1' x2 s2
        Nothing -> do
            opts <- askOpts
            if implicitClassify opts
                then do
                    ks <- classifiesCstrs l e1 ct1 x2 s2
                    tcCstrM l $ MultipleSubstitutions v1 [(SecT Public,ks),(SecT s2,[Unifies (loc x2) (loc e1),Unifies (IdxT $ varExpr x2) (IdxT e1)])]
                else do
                    tcCstrM l $ Unifies (SecT s1) (SecT s2)
                    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> s1@(SVar v _)) x2 s2@(Private d2 k2) = do
    tcCstrM l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Public) x2 s2@(Private d2 k2) = do
    opts <- askOpts
    if implicitClassify opts
        then do
            ks <- classifiesCstrs l e1 ct1 x2 s2
            tcCstrsM l ks
        else constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing
coercesSec' l e1 ct1@(cSec -> SVar v1 _) x2 s2@(SVar v2 _) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just t1',Just t2') -> coercesSec' l e1 (setCSec ct1 t1') x2 t2'
        (Just t1',Nothing) -> coercesSec' l e1 (setCSec ct1 t1') x2 s2
        (Nothing,Just t2') -> coercesSec' l e1 ct1 x2 t2'
        (Nothing,Nothing) -> constraintError (\x y -> Halt . CoercionException "security type" x y) l e1 ppExprTy x2 ppVarTy Nothing
coercesSec' l e1 t1 x2 t2 = constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing

classifiesCstrs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> VarName VarIdentifier Type -> SecType -> TcM loc m [TcCstr]
classifiesCstrs l e1 ct1 x2 s2 = do
    let ct2 = setCSec ct1 s2
    let classify = ProcedureName () $ mkVarId "classify"
    dec <- newDecVar
    let k1 = PDec (Left classify) Nothing [(e1,False)] (ComplexT ct2) dec Nothing
    let k2 = Unifies (loc x2) (ComplexT ct2)
    let k3 = Unifies (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) (fmap (const $ DecT dec) classify) Nothing [(e1,False)])
    return [k1,k2,k3]

-- | coerces a literal into a complex type
coercesLitComplex :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coercesLitComplex l e1@(loc -> ComplexT (TyLit lit)) x2@(loc -> ComplexT ct@(CType s t d sz)) = do
    coercesLitBase l lit t
    tcCstrM l $ CoercesSec (updLoc e1 $ ComplexT $ setCSec ct Public) x2  -- coerce the security type
    -- we need to know the fixed size of arrays of literals
    tcCstrM l $ EvalVarExprs ((d,False):sz)
coercesLitComplex l e1@(loc -> ComplexT (TyLit lit)) x2@(loc -> ComplexT (CVar v)) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> coercesLitComplex l e1 (updLoc x2 $ ComplexT c2)
        Nothing -> do
            c2 <- expandCTypeVar l v
            coercesLitComplex l e1 (updLoc x2 $ ComplexT c2)
coercesLitComplex l e1@(loc -> ComplexT (TyLit lit1)) x2@(loc -> ComplexT ct2@(TyLit lit2)) = do
    coercesLit l lit1 lit2
    unifiesExprTy l (varExpr x2) (updLoc e1 $ ComplexT ct2)
coercesLitComplex l e1 x2 = constraintError (CoercionException "literal complex type") l e1 ppExprTy x2 ppVarTy Nothing  
    
coercesArrayLitComplex :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> VarName VarIdentifier Type -> TcM loc m ()
coercesArrayLitComplex l e1@(loc -> ComplexT (ArrayLit es)) x2@(loc -> ComplexT ct@(CType s t d sz)) = do
    mapM_ (\e -> tcCstrM l $ Unifies (loc e) (BaseT t)) es
    let e1' = updLoc e1 $ ComplexT $ setCSec ct Public
    tcCstrM l $ CoercesSec e1' x2 -- coerce the security type
    tcCstrM l $ MatchTypeDimension (ComplexT ct) [(indexSExpr 1,False)]
    tcCstrM l $ UnifiesSizes sz [(indexSExpr $ toEnum $ length es,False)]
    unifiesExprTy l (varExpr x2) e1'
coercesArrayLitComplex l e1@(loc -> ComplexT (ArrayLit es)) x2@(loc -> ComplexT (CVar v)) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> coercesArrayLitComplex l e1 (updLoc x2 $ ComplexT c2)
        Nothing -> do
            c2 <- expandCTypeVar l v
            coercesArrayLitComplex l e1 (updLoc x2 $ ComplexT c2)
coercesArrayLitComplex l e1@(loc -> ComplexT (ArrayLit es1)) x2@(loc -> ComplexT t2@(ArrayLit es2)) = do
    constraintList (CoercionException "array literal to complex") (equalsExprTy l) l es1 es2
    return ()
coercesArrayLitComplex l e1 x2 = constraintError (CoercionException "array literal complex type") l e1 ppExprTy x2 ppExprTy Nothing  

coercesLit :: (VarsIdTcM loc m,Location loc) => loc -> Literal () -> Literal () -> TcM loc m ()
coercesLit l lit1 lit2 | lit1 == lit2 = return ()
coercesLit l (IntLit _ i1) (IntLit _ i2) | i1 == i2 = return ()
coercesLit l (IntLit _ i1) (FloatLit _ f2) | fromInteger i1 == f2 = return ()
coercesLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
coercesLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
coercesLit l lit1 lit2 = constraintError (CoercionException "literal type") l lit1 pp lit2 pp Nothing  

-- coerces a literal into a base type
coercesLitBase :: (VarsIdTcM loc m,Location loc) => loc -> Literal () -> BaseType -> TcM loc m ()
coercesLitBase l lit t2@(BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
       Just t2' -> coercesLitBase l lit t2'
       Nothing -> do
           b <- case lit of
                StringLit _ s -> return $ TyPrim $ DatatypeString ()
                BoolLit _ b -> return $ TyPrim $ DatatypeBool ()
                otherwise -> constraintError (\x y e -> Halt $ CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
           addSubstM l (VarName BType v) (BaseT b)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primIntBounds -> Just (min,max)))) = do
    unless (min <= i && i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primFloatBounds -> Just (min,max)))) = do
    unless (min <= fromInteger i && fromInteger i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (FloatLit _ f) (TyPrim (t@(primFloatBounds -> Just (min,max)))) | isPrimFloat t = do
    unless (min <= f && f <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show f) (pp t) (show min) (show max)
coercesLitBase l (BoolLit _ b) (TyPrim (DatatypeBool _)) = return ()
coercesLitBase l (StringLit _ s) (TyPrim (DatatypeString _)) = return ()
coercesLitBase l l1 t2 = constraintError (CoercionException "literal base type") l l1 pp t2 pp Nothing  

-- | Checks if a type is more specific than another, performing substitutions
compares :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m (Comparison (TcM loc m))
compares l (IdxT e1) (IdxT e2) = comparesExpr l e1 e2
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
compares l (DecT d1) (DecT d2) = do
    comparesDec l d1 d2
compares l (VArrayT a1) (VArrayT a2) = do
    comparesArray l a1 a2
compares l (VAType b1 sz1) (VAType b2 sz2) = do
    o1 <- compares l b1 b2
    o2 <- compares l (IdxT sz1) (IdxT sz2)
    appendComparisons l [o1,o2]
--compares l (CondType t1 c1) (CondType t2 c2) = do
--    o1 <- compares l t1 t2
--    o2 <- comparesSCond l c1 c2
--    return $ o1 `mappend` o2
--compares l (CondType t1 c1) t2 = do
--    o1 <- compares l t1 t2
--    o2 <- comparesSCond l c1 trueSCond
--    return $ o1 `mappend` o2
--compares l t1 (CondType t2 c2) = do
--    o1 <- compares l t1 t2
--    o2 <- comparesSCond l trueSCond c2
--    return $ o1 `mappend` o2
compares l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (ComparisonException "type") (pp t1) (pp t2) . Just)
    (equals l t1 t2 >> return (Comparison t1 t2 EQ))

decToken :: MonadIO m => TcM loc m DecType
decToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ DVar v

secToken :: MonadIO m => TcM loc m SecType
secToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ SVar v AnyKind
    
baseToken :: MonadIO m => TcM loc m BaseType
baseToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ BVar v

arrayToken :: MonadIO m => Type -> SExpr VarIdentifier Type -> TcM loc m VArrayType
arrayToken b sz = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ VAVar v b sz

complexToken :: MonadIO m => TcM loc m ComplexType
complexToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ CVar v

exprToken :: MonadIO m => TcM loc m (Expression VarIdentifier Type)
exprToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    let t = BaseT $ BVar v
    return $ RVariablePExpr t (VarName t v)

comparesDec :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> DecType -> TcM loc m (Comparison (TcM loc m))
comparesDec l t1@(DVar v1) t2@(DVar v2) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- decToken
            addSubst l v1 $ DecT x
            addSubst l v2 $ DecT x
            return (Comparison t1 t2 EQ)
        (Just t1',Nothing) -> comparesDec l t1' t2
        (Nothing,Just t2') -> comparesDec l t1 t2'
        (Just t1',Just t2') -> comparesDec l t1' t2'        
comparesDec l t1 t2@(DVar v) = do
    mb <- tryResolveDVar l v
    case mb of
        Just t2 -> comparesDec l t1 t2
        Nothing -> do
            addSubst l v $ DecT t1
            return (Comparison t1 t2 LT)
comparesDec l t1@(DVar v) t2 = do
    mb <- tryResolveDVar l v
    case mb of
        Just t1 -> comparesDec l t1 t2
        Nothing -> do
            addSubst l v $ DecT t2
            return (Comparison t1 t2 GT)
comparesDec l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (ComparisonException "declaration type") (pp t1) (pp t2) . Just)
    (equalsDec l t1 t2 >> return (Comparison t1 t2 EQ))

comparesArray :: (VarsIdTcM loc m,Location loc) => loc -> VArrayType -> VArrayType -> TcM loc m (Comparison (TcM loc m))
comparesArray l a1@(VAVal ts1 _) a2@(VAVal ts2 _) = do
    comparesList l ts1 ts2
comparesArray l a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) | v1 == v2 = return (Comparison a1 a2 EQ)
comparesArray l a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) = do
    mb1 <- tryResolveVAVar l v1 sz1
    mb2 <- tryResolveVAVar l v2 sz2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- arrayToken b1 sz1
            addSubst l v1 $ VArrayT x
            addSubst l v2 $ VArrayT x
            return $ Comparison a1 a2 EQ
        (Just a1',Nothing) -> comparesArray l a1' a2
        (Nothing,Just a2') -> comparesArray l a1 a2'
        (Just a1',Just a2') -> comparesArray l a1' a2'        
comparesArray l a1 a2@(VAVar v2 b2 sz2) = do
    mb <- tryResolveVAVar l v2 sz2
    case mb of
        Just a2 -> comparesArray l a1 a2
        Nothing -> do
            addSubst l v2 $ VArrayT a2
            return $ Comparison a1 a2 LT
comparesArray l a1@(VAVar v1 b1 sz1) a2 = do
    mb <- tryResolveVAVar l v1 sz1
    case mb of
        Just t1 -> comparesArray l a1 a2
        Nothing -> do
            addSubst l v1 $ VArrayT a2
            return $ Comparison a1 a2 GT
--comparesArray l a1 a2 = constraintError (ComparisonException "array type") l a1 pp a2 pp Nothing

comparesSec :: (VarsIdTcM loc m,Location loc) => loc -> SecType -> SecType -> TcM loc m (Comparison (TcM loc m))
comparesSec l t1@Public t2@Public = return (Comparison t1 t2 EQ)
comparesSec l t1@(Private d1 k1) t2@(Private d2 k2) | d1 == d2 && k1 == k2 = return (Comparison t1 t2 EQ)
--comparesSec l Public (Private {}) = return LT -- public computations are preferrable
--comparesSec l (Private {}) Public = return GT -- public computations are preferrable
comparesSec l t1@(SVar v1 k1) t2@(SVar v2 k2) | v1 == v2 && k1 == k2 = return (Comparison t1 t2 EQ)
comparesSec l t1@(SVar v1 k1) t2@(SVar v2 k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> case (k1,k2) of
            (AnyKind,PrivateKind _) -> return $ Comparison t1 t2 GT
            (PrivateKind _,AnyKind) -> return $ Comparison t1 t2 LT
            (k1,(==k1) -> True) -> do
                x <- secToken
                addSubst l v1 $ SecT x
                addSubst l v2 $ SecT x
                return $ Comparison t1 t2 EQ
            otherwise -> constraintError (ComparisonException "security type") l t1 pp t2 pp Nothing
        (Just t1',Nothing) -> comparesSec l t1' t2
        (Nothing,Just t2') -> comparesSec l t1 t2'
        (Just t1',Just t2') -> comparesSec l t1' t2'        
comparesSec l t1 t2@(SVar v _) = do
    mb <- tryResolveSVar l v
    case mb of
        Just t2 -> comparesSec l t1 t2
        Nothing -> do
            addSubst l v $ SecT t1
            return $ Comparison t1 t2 LT
comparesSec l t1@(SVar v _) t2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just t1 -> comparesSec l t1 t2
        Nothing -> do
            addSubst l v $ SecT t2
            return $ Comparison t1 t2 GT
comparesSec l t1 t2 = constraintError (ComparisonException "security type") l t1 pp t2 pp Nothing

comparesSys :: (VarsIdTcM loc m,Location loc) => loc -> SysType -> SysType -> TcM loc m (Comparison (TcM loc m))
comparesSys l (SysPush t1) (SysPush t2) = do
    compares l t1 t2
comparesSys l (SysRet t1) (SysRet t2) = do
    compares l t1 t2
comparesSys l (SysRef t1) (SysRef t2) = do
    compares l t1 t2
comparesSys l (SysCRef t1) (SysCRef t2) = do
    compares l t1 t2
comparesSys l t1 t2 = constraintError (ComparisonException "syscall type") l t1 pp t2 pp Nothing

comparesBase :: (VarsIdTcM loc m,Location loc) => loc -> BaseType -> BaseType -> TcM loc m (Comparison (TcM loc m))
comparesBase l t1@(TyDec d1) t2@(TyDec d2) = equalsDec l d1 d2 >> return (Comparison t1 t2 EQ)
comparesBase l t1@(TyPrim p1) t2@(TyPrim p2) = equalsPrim l p1 p2 >> return (Comparison t1 t2 EQ)
comparesBase l t1@(BVar v1) t2@(BVar v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- baseToken
            addSubst l v1 $ BaseT x
            addSubst l v2 $ BaseT x
            return $ Comparison t1 t2 EQ
        (Just t1',Nothing) -> comparesBase l t1' t2
        (Nothing,Just t2') -> comparesBase l t1 t2'
        (Just t1',Just t2') -> comparesBase l t1' t2'        
comparesBase l t1 t2@(BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> comparesBase l t1 t2
        Nothing -> do
            addSubst l v $ BaseT t1
            return $ Comparison t1 t2 LT
comparesBase l t1@(BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> comparesBase l t1 t2
        Nothing -> do
            addSubst l v $ BaseT t2
            return $ Comparison t1 t2 GT
comparesBase l t1 t2 = constraintError (ComparisonException "base type") l t1 pp t2 pp Nothing

comparesComplex :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc m (Comparison (TcM loc m))
comparesComplex l t1@Void t2@Void = return $ Comparison t1 t2 EQ
comparesComplex l t1@(TyLit lit1) t2@(TyLit lit2) | lit1 == lit2 = return $ Comparison t1 t2 EQ
--comparesComplex l t1@(TyLit lit) t2 = do
--    let e1 = LitPExpr (ComplexT t1) $ fmap (const (ComplexT t1)) lit
--    coercesLitComplex l e1 lit t2
--    return $ Comparison t1 t2 GT
--comparesComplex l t1 t2@(TyLit lit) = do
--    let e2 = LitPExpr (ComplexT t2) $ fmap (const (ComplexT t2)) lit
--    coercesLitComplex l e2 lit t1
--    return $ Comparison t1 t2 LT
--comparesComplex l ct1@(ArrayLit es1) ct2@(ArrayLit es2) = do
--    if (length es1 == length es2)
--        then do
--            os <- mapM (\(x,y) -> comparesExpr l x y) $ zip (Foldable.toList es1) (Foldable.toList es2)
--            appendComparisons l os
--        else return $ Comparison ct1 ct2 $ compare (length es1) (length es2)
--comparesComplex l t1@(ArrayLit lit) t2 = do
--    let e1 = ArrayConstructorPExpr (ComplexT t1) lit
--    coercesArrayLitComplex l e1 lit t2
--    return $ Comparison t1 t2 GT
--comparesComplex l t1 t2@(ArrayLit lit) = do
--    let e2 = ArrayConstructorPExpr (ComplexT t2) lit
--    coercesArrayLitComplex l e2 lit t1
--    return $ Comparison t1 t2 LT
comparesComplex l ct1@(CType s1 t1 d1 sz1) ct2@(CType s2 t2 d2 sz2) = do
    o1 <- comparesSec l s1 s2
    o2 <- comparesBase l t1 t2
    o3 <- comparesExpr l d1 d2
    o4 <- comparesSizes l sz1 sz2
    appendComparisons l [o1,o2,o3,o4]
comparesComplex l t1@(CVar v1) t2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- complexToken
            addSubst l v1 $ ComplexT x
            addSubst l v2 $ ComplexT x
            return $ Comparison t1 t2 EQ
        (Just t1',Nothing) -> comparesComplex l t1' t2
        (Nothing,Just t2') -> comparesComplex l t1 t2'
        (Just t1',Just t2') -> comparesComplex l t1' t2'        
comparesComplex l t1 t2@(CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2 -> comparesComplex l t1 t2
        Nothing -> do
            addSubst l v $ ComplexT t1
            return $ Comparison t1 t2 LT
comparesComplex l t1@(CVar v) t2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1 -> comparesComplex l t1 t2
        Nothing -> do
            addSubst l v $ ComplexT t2
            return $ Comparison t1 t2 GT
comparesComplex l t1 t2 = constraintError (ComparisonException "complex type") l t1 pp t2 pp Nothing
    
comparesFoldable :: (VarsIdTcM loc m,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc m (Comparison (TcM loc m))
comparesFoldable l xs ys = comparesList l (toList xs) (toList ys)

data Comparison m where
    Comparison :: VarsId m a => a -> a -> Ordering -> Comparison m
  deriving (Typeable)
    
instance Typeable m => Data (Comparison m) where
    gfoldl k z (Comparison x y o) = z Comparison `k` x `k` y `k` o
    gunfold k z c = error "gunfold Comparison"
    toConstr (Comparison {}) = con_Comparison
    dataTypeOf _ = ty_Comparison

con_Comparison = mkConstr ty_Comparison "Comparison" [] Prefix
ty_Comparison   = mkDataType "Language.SecreC.TypeChecker.Constraint.Comparison" [con_Comparison]
    
instance Eq (Comparison m) where
    (Comparison x1 y1 o1) == (Comparison x2 y2 o2) = o1 == o2
instance Ord (Comparison m) where
    compare (Comparison _ _ o1) (Comparison _ _ o2) = compare o1 o2
deriving instance Show (Comparison m)

instance PP (Comparison m) where
    pp (Comparison x y o) = pp x <+> pp o <+> pp y
instance (GenVar VarIdentifier m,Typeable m) => Vars VarIdentifier m (Comparison m) where
    traverseVars f (Comparison x y o) = do
        x' <- f x
        y' <- f y
        o' <- f o
        return $ Comparison x' y' o'

compOrdering :: Comparison m -> Ordering
compOrdering (Comparison _ _ o) = o
ppCompares x y o = pp x <+> pp o <+> pp y

comparesList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m (Comparison (TcM loc m))
comparesList l a@[] b@[] = return $ Comparison a b EQ
comparesList l a@(x:xs) b@(y:ys) = do
    f <- compares l x y
    g <- comparesList l xs ys
    appendComparison l f g
comparesList l xs ys = constraintError (ComparisonException "type") l xs pp ys pp Nothing
    
appendComparison :: (VarsIdTcM loc m,Location loc) => loc -> Comparison (TcM loc m) -> Comparison (TcM loc m) -> TcM loc m (Comparison (TcM loc m))
appendComparison l (Comparison x1 x2 EQ) y@(Comparison y1 y2 o) = return y
appendComparison l x@(Comparison x1 x2 o) (Comparison y1 y2 EQ) = return x
appendComparison l (Comparison x1 x2 LT) y@(Comparison y1 y2 LT) = return y
appendComparison l (Comparison x1 x2 GT) y@(Comparison y1 y2 GT) = return y
appendComparison l c1 c2 = constraintError (ComparisonException "comparison") l c1 pp c2 pp Nothing

appendComparisons :: (VarsIdTcM loc m,Location loc) => loc -> [Comparison (TcM loc m)] -> TcM loc m (Comparison (TcM loc m))
appendComparisons l xs = foldr1M (appendComparison l) xs

-- | Non-directed unification, without implicit security coercions.
-- applies substitutions
unifies :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m ()
unifies l (IdxT e1) (IdxT e2) = unifiesExpr l e1 e2
unifies l (SecT s1) (SecT s2) = unifiesSec l s1 s2
unifies l (SysT s1) (SysT s2) = unifiesSys l s1 s2
unifies l (BaseT b1) (BaseT b2) = unifiesBase l b1 b2
unifies l (BaseT b1) (ComplexT c2) = unifiesComplex l (defCType b1) c2
unifies l (ComplexT c1) (BaseT b2) = unifiesComplex l c1 (defCType b2)
unifies l (ComplexT c1) (ComplexT c2) = unifiesComplex l c1 c2
unifies l (DecT d1) (DecT d2) = unifiesDec l d1 d2
unifies l (VArrayT a1) (VArrayT a2) = unifiesArray l a1 a2
unifies l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM l $ Unifies b1 b2
    unifiesExprTy l sz1 sz2
unifies l t1@(CondType t1' c1) t2@(CondType t2' c2) = do
    unifies l t1' t2'
    unifiesSCond l c1 c2
unifies l t1@(CondType t1' c1) t2 = do
    unifies l t1' t2
    unifiesSCond l c1 trueSCond
unifies l t1 t2@(CondType t2' c2) = do
    unifies l t1 t2'
    unifiesSCond l trueSCond c2
unifies l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (UnificationException "type") (pp t1) (pp t2) . Just)
    (equals l t1 t2)

unifiesArray :: (VarsIdTcM loc m,Location loc) => loc -> VArrayType -> VArrayType -> TcM loc m ()
unifiesArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    unifiesList l ts1 ts2
    tcCstrM l $ Unifies b1 b2
unifiesArray l a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) = do
    tcCstrM l $ Unifies b1 b2
    unifiesExprTy l sz1 sz2
    mb1 <- tryResolveVAVar l v1 sz1
    mb2 <- tryResolveVAVar l v2 sz2
    case (mb1,mb2) of
        (Just a1',Just a2') -> tcCstrM l $ Unifies (VArrayT a1') (VArrayT a2')
        (Just a1',Nothing) -> tcCstrM l $ Unifies (VArrayT a1') (VArrayT a2)
        (Nothing,Just a2') -> tcCstrM l $ Unifies (VArrayT a1) (VArrayT a2')
        (Nothing,Nothing) -> addSubstM l (VarName (VAType b1 sz1) v1) (VArrayT a2)
unifiesArray l a1@(VAVar v1 b1 sz1) a2 = do
    mb1 <- tryResolveVAVar l v1 sz1
    unifiesExprTy l sz1 (vArraySize a2)
    case mb1 of
        Just a1' -> tcCstrM l $ Unifies (VArrayT a1') (VArrayT a2)
        Nothing -> addSubstM l (VarName (VAType b1 sz1) v1) (VArrayT a2)
unifiesArray l a1 a2@(VAVar v2 b2 sz2) = do
    mb2 <- tryResolveVAVar l v2 sz2
    unifiesExprTy l (vArraySize a1) (vArraySize a2)
    case mb2 of
        Just a2' -> tcCstrM l $ Unifies (VArrayT a1) (VArrayT a2')
        Nothing -> addSubstM l (VarName (VAType b2 sz2) v2) (VArrayT a1)
--unifiesArray l a1 a2 = addErrorM l
--    (TypecheckerError (locpos l) . (UnificationException "array") (pp a1) (pp a2) . Just)
--    (equalsArray l a1 a2)

unifiesDec :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> DecType -> TcM loc m ()
unifiesDec l d1@(DVar v1) d2@(DVar v2) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (DecT d1') (DecT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (DecT d1') (DecT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (DecT d1) (DecT d2')
        (Nothing,Nothing) -> addSubstM l (VarName DType v1) (DecT d2)
unifiesDec l d1@(DVar v1) d2 = do
    mb <- tryResolveDVar l v1
    case mb of
        Just d1' -> tcCstrM l $ Unifies (DecT d1') (DecT d2)
        Nothing -> addSubstM l (VarName DType v1) (DecT d2)
unifiesDec l d1 (DVar v2) = do
    mb <- tryResolveDVar l v2
    case mb of
        Just d2' -> tcCstrM l $ Unifies (DecT d1) (DecT d2')
        Nothing -> addSubstM l (VarName DType v2) (DecT d1)
unifiesDec l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (UnificationException "declaration type") (pp t1) (pp t2) . Just)
    (equalsDec l t1 t2)

unifiesComplex :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc m ()
unifiesComplex l Void Void = return ()
--unifiesComplex l t1@(TyLit lit) t2 = withoutImplicitClassify $ do
--    let e1 = LitPExpr (ComplexT t1) $ fmap (const $ ComplexT t1) lit
--    coercesLitComplex l e1 lit t2
--    return ()
--unifiesComplex l t1 t2@(TyLit lit) = withoutImplicitClassify $ do
--    let e2 = LitPExpr (ComplexT t2) $ fmap (const $ ComplexT t2) lit
--    coercesLitComplex l e2 lit t1
--    return ()
--unifiesComplex l t1@(ArrayLit es) t2 = withoutImplicitClassify $ do
--    let e1 = ArrayConstructorPExpr (ComplexT t1) $ fmap (fmap (const $ ComplexT t1)) es
--    coercesArrayLitComplex l e1 es t2
--    return ()
--unifiesComplex l t1 t2@(ArrayLit es) = withoutImplicitClassify $ do
--    let e2 = ArrayConstructorPExpr (ComplexT t2) $ fmap (fmap (const $ ComplexT t2)) es
--    coercesArrayLitComplex l e2 es t1
--    return ()
unifiesComplex l ct1@(CType s1 t1 d1 sz1) ct2@(CType s2 t2 d2 sz2) = addErrorM l (TypecheckerError (locpos l) . (UnificationException "complex") (pp ct1) (pp ct2) . Just) $ do
    (_,ks) <- tcWithCstrs l "unifiesComplex" $ do
        tcCstrM l $ Unifies (SecT s1) (SecT s2)
        tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
        unifiesExprTy l d1 d2
    withDependencies ks $ tcCstrM l $ UnifiesSizes sz1 sz2
unifiesComplex l d1@(CVar v1) d2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (ComplexT d1') (ComplexT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (ComplexT d1') (ComplexT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (ComplexT d1) (ComplexT d2')
        (Nothing,Nothing) -> addSubstM l (VarName TType v1) (ComplexT d2)
unifiesComplex l (CVar v) c2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just c1 -> tcCstrM l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (VarName TType v) (ComplexT c2)
unifiesComplex l c1 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> tcCstrM l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (VarName TType v) (ComplexT c1)
unifiesComplex l t1 t2 = constraintError (UnificationException "complex type") l t1 pp t2 pp Nothing

unifiesSVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> SVarKind -> SecType -> TcM loc m ()
unifiesSVar l v k@AnyKind s1 = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind Nothing) s1@(Private _ _) = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind (Just n)) s1@(Private d ((==n) -> True)) = addSVarSubstM l v s1
unifiesSVar l v k s1@(SVar v1 k1) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> tcCstrM l $ Unifies (SecT $ SVar v k) (SecT s1')
        Nothing -> if k <= k1
            then addSVarSubstM l v s1
            else addSVarSubstM l v1 (SVar v k)
unifiesSVar l v k s = constraintError (UnificationException "security type") l (SVar v k) pp s pp Nothing

addSVarSubstM l v s = addSubstM l (VarName (SType $ secTypeKind s) v) (SecT s)

unifiesSec :: (VarsIdTcM loc m,Location loc) => loc -> SecType -> SecType -> TcM loc m ()
unifiesSec l Public Public = return ()
unifiesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
unifiesSec l d1@(SVar v1 k1) d2@(SVar v2 k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (SecT d1') (SecT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (SecT d1') (SecT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (SecT d1) (SecT d2')
        (Nothing,Nothing) -> unifiesSVar l v1 k1 d2
unifiesSec l (SVar v k) s2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just s1 -> tcCstrM l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s2
unifiesSec l s1 (SVar v k) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s1
unifiesSec l t1 t2 = constraintError (UnificationException "security type") l t1 pp t2 pp Nothing

unifiesSys :: (VarsIdTcM loc m,Location loc) => loc -> SysType -> SysType -> TcM loc m ()
unifiesSys l (SysPush t1) (SysPush t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l (SysRet t1) (SysRet t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l (SysRef t1) (SysRef t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l (SysCRef t1) (SysCRef t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l t1 t2 = constraintError (UnificationException "syscall type") l t1 pp t2 pp Nothing

unifiesBase :: (VarsIdTcM loc m,Location loc) => loc -> BaseType -> BaseType -> TcM loc m ()
unifiesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
unifiesBase l d1@(BVar v1) d2@(BVar v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (BaseT d1') (BaseT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (BaseT d1') (BaseT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (BaseT d1) (BaseT d2')
        (Nothing,Nothing) -> addSubstM l (VarName BType v1) (BaseT d2)
unifiesBase l (BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (VarName BType v) (BaseT t2)
unifiesBase l t1 (BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (VarName BType v) (BaseT t1)
unifiesBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2
unifiesBase l t1 t2 = constraintError (UnificationException "base type") l t1 pp t2 pp Nothing

unifiesSizes :: (VarsIdTcM loc m,Location loc) => loc -> [(Expression VarIdentifier Type,IsVariadic)] -> [(Expression VarIdentifier Type,IsVariadic)] -> TcM loc m ()
unifiesSizes l szs1 szs2 = addErrorM l (TypecheckerError (locpos l) . (UnificationException "sizes") (pp szs1) (pp szs2) . Just) $ do
    unifiesSizes' l szs1 szs2

unifiesSizes' l szs1@(all (not . snd) -> True) [(e2,True)] = unifiesExprTy l e2 (ArrayConstructorPExpr (loc e2) $ map fst szs1)
unifiesSizes' l [(e1,True)] szs2@(all (not . snd) -> True) = unifiesExprTy l e1 (ArrayConstructorPExpr (loc e1) $ map fst szs2)
unifiesSizes' l [(e1,True)] [(e2,True)] = unifiesExprTy l e1 e2
unifiesSizes' l szs1 szs2 = do
    szs1' <- concatMapM (expandVariadicExpr l) szs1
    szs2' <- concatMapM (expandVariadicExpr l) szs2
    constraintList (UnificationException "sizes") (unifiesExprTy l) l szs1' szs2'
    return ()

expandVariadicExpr :: (VarsIdTcM loc m,Location loc) => loc -> (SExpr VarIdentifier Type,IsVariadic) -> TcM loc m [SExpr VarIdentifier Type]
expandVariadicExpr l (e,False) = case loc e of
    VAType {} -> genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (pp e)
    VArrayT {} -> genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (pp e)
    otherwise -> return [e]
expandVariadicExpr l (ArrayConstructorPExpr t es,True) = case t of
    VAType {} -> return es
    VArrayT {} -> return es
    otherwise -> genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)
expandVariadicExpr l (e,True) = do
    let t = loc e
    case t of
        VAType {} -> do
            d <- evaluateTypeDim l t
            case d of
                0 -> return [e]
                1 -> do
                    sz <- evaluateTypeSize l t
                    b <- typeBase l t
                    vs <- forM [0..pred (fromEnum sz)] $ \i -> newTypedVar ("vex"++show i) b
                    let es = map varExpr vs
                    tcCstrM l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t es)
                    return es
                otherwise -> genTcError (locpos l) $ text "Variadic matrix" <+> quotes (pp t) <+> text "not supported"
        VArrayT a -> do
            ts <- expandVariadicType l (VArrayT a,True)
            vs <- forM ts $ \t -> newTypedVar "vex" t
            let es = map varExpr vs
            tcCstrM l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t es)
            return es
        otherwise -> genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)
    
expandVariadicType :: (VarsIdTcM loc m,Location loc) => loc -> (Type,IsVariadic) -> TcM loc m [Type]
expandVariadicType l (t,False) = case tyOf t of
    VAType {} -> genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (pp t)
    otherwise -> return [t]
expandVariadicType l (VArrayT (VAVal ts _),True) = return ts
expandVariadicType l (t@(VArrayT a),True) = do
    let tt = tyOf t
    sz <- evaluateTypeSize l tt
    b <- typeBase l tt
    vs <- forM [0..pred (fromEnum sz)] $ \i -> newVarOf ("varr"++show i) b
    tcCstrM l $ Unifies t (VArrayT $ VAVal vs b)
    return vs
expandVariadicType l (t,True) = genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)

unifiesList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError (UnificationException "type") l xs pp ys pp Nothing

resolveCVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m ComplexType
resolveCVar l v = resolveTVar l v >>= typeToComplexType l

resolveSVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m SecType
resolveSVar l v = resolveTVar l v >>= typeToSecType l

resolveVAVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> SExpr VarIdentifier Type -> TcM loc m VArrayType
resolveVAVar l v sz = resolveTVar l v >>= \t -> typeToVArrayType l t sz

resolveDVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m DecType
resolveDVar l v = resolveTVar l v >>= typeToDecType l

resolveBVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m BaseType
resolveBVar l v = resolveTVar l v >>= typeToBaseType l

resolveTVar :: (MonadIO m,Location loc) => loc -> VarIdentifier -> TcM loc m Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> tcError (locpos l) $ Halt $ UnresolvedVariable (pp v)
        Just t -> return t

tryResolveSVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe SecType)
tryResolveSVar l v = tryResolveTVar l v >>= mapM (typeToSecType l)

tryResolveVAVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> SExpr VarIdentifier Type -> TcM loc m (Maybe VArrayType)
tryResolveVAVar l v sz = tryResolveTVar l v >>= mapM (\t -> typeToVArrayType l t sz)

tryResolveBVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe BaseType)
tryResolveBVar l v = tryResolveTVar l v >>= mapM (typeToBaseType l)

tryResolveCVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe ComplexType)
tryResolveCVar l v = tryResolveTVar l v >>= mapM (typeToComplexType l)

tryResolveDVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe DecType)
tryResolveDVar l v = tryResolveTVar l v >>= mapM (typeToDecType l)

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: (MonadIO m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe Type)
tryResolveTVar l v | varIdTok v = return Nothing
tryResolveTVar l v = do
    addVarDependencies v
    -- lookup in the substitution environment
    s <- getTSubsts
    mb <- substsFromMap s v
    return $ mb

-- | tries to resolve an expression
tryResolveEVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> Type -> TcM loc m (Maybe (SExpr VarIdentifier (Typed loc)))
tryResolveEVar l v t | varIdTok v = return Nothing
tryResolveEVar l v t = do
    addVarDependencies v
    ss <- getTSubsts
    case Map.lookup v ss of
        Just (IdxT e) -> do
            tcCstrM l $ Unifies t (loc e)
            return $ Just (fmap (Typed l) e)
        Just a@(VArrayT (VAVal (unIdxs -> Just es) _)) -> do
            tcCstrM l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ ArrayConstructorPExpr (tyOf a) es
        Just a@(VArrayT (VAVar v _ _)) -> do
            tcCstrM l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ RVariablePExpr (tyOf a) (VarName (tyOf a) v)
        otherwise -> return Nothing

unIdx :: Type -> Maybe (SExpr VarIdentifier Type)
unIdx (IdxT e) = Just e
unIdx _ = Nothing

unIdxs :: [Type] -> Maybe [SExpr VarIdentifier Type]
unIdxs [] = Just []
unIdxs (x:xs) = case (unIdx x,unIdxs xs) of
    (Just x,Just xs) -> Just (x:xs)
    otherwise -> Nothing

setCSec (CType _ t d sz) s = CType s t d sz

isSupportedPrint :: (VarsIdTcM loc m,Location loc) => loc -> [(Expression VarIdentifier Type,IsVariadic)] -> [VarName VarIdentifier Type] -> TcM loc m ()
isSupportedPrint l es xs = forM_ (zip es xs) $ \(e,x) -> do
    (dec,[(y,_)]) <- tcTopPDecCstrM l True (Left $ ProcedureName () (mkVarId "tostring")) Nothing [e] (BaseT string)
    unifiesExprTy l (varExpr x) y
    return ()

isReturnStmt :: (VarsIdTcM loc m,Location loc) => loc -> Set StmtClass -> Type -> TcM loc m ()
isReturnStmt l cs ret = addErrorM l (\err -> TypecheckerError (locpos l) $ NoReturnStatement (pp ret)) $ do
    aux $ Set.toList cs
  where
    aux [StmtReturn] = return () -- because we already checked the return type when typechecking the statements
    aux c = do
        tcCstrM l $ Unifies (ComplexT Void) ret
        return ()

unifiesSCond :: (VarsIdTcM loc m,Location loc) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc m ()
unifiesSCond l e1 e2 = unifiesExprTy l e1 e2 `mplus` satisfiesSConds l [e1,e2]

satisfiesSConds :: (VarsIdTcM loc m,Location loc) => loc -> [SCond VarIdentifier Type] -> TcM loc m ()
satisfiesSConds l is = do
    cs <- prove l "satisfiesSConds" $ mapM (expr2ICond . fmap (Typed l)) is
    isValid l $ IAnd cs

unifiesExpr :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m ()
unifiesExpr l e1@(RVariablePExpr t1 v1@(VarName _ n)) e2@(RVariablePExpr t2 v2) = do
    mb1 <- tryResolveEVar l (varNameId v1) t1
    mb2 <- tryResolveEVar l (varNameId v2) t2
    case (mb1,mb2) of
        (Just e1',Just e2') -> unifiesExpr l (fmap typed e1') (fmap typed e2')
        (Just e1',Nothing) -> unifiesExpr l (fmap typed e1') e2
        (Nothing,Just e2') -> unifiesExpr l e1 (fmap typed e2')
        (Nothing,Nothing) -> addValueM l v1 e2
unifiesExpr l e1@(RVariablePExpr t1 v1) e2 = do
    mb <- tryResolveEVar l (varNameId v1) t1
    case mb of
        Nothing -> addValueM l v1 e2
        Just e1' -> unifiesExpr l (fmap typed e1') e2
unifiesExpr l e1 e2@(RVariablePExpr t2 v2) = do
    mb <- tryResolveEVar l (varNameId v2) t2
    case mb of
        Nothing -> addValueM l v2 e1
        Just e2' -> unifiesExpr l e1 (fmap typed e2')
unifiesExpr l (ArrayConstructorPExpr t1 es1) (ArrayConstructorPExpr t2 es2) = do
    constraintList (UnificationException "expression") (unifiesExprTy l) l es1 es2
    return ()
unifiesExpr l e1 e2 = addErrorM l (TypecheckerError (locpos l) . (EqualityException "expression") (pp e1) (pp e2) . Just) $ equalsExpr l e1 e2
    
unifiesTIdentifier :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> TIdentifier -> TcM loc m ()
unifiesTIdentifier l (Right (Right (OpCast _ t1))) (Right (Right (OpCast _ t2))) = do
    unifies l (castTypeToType t1) (castTypeToType t2)
unifiesTIdentifier l (Right (Right op1)) (Right (Right op2)) | funit op1 == funit op2 = return ()
unifiesTIdentifier l n1 n2 | n1 == n2 = return ()
unifiesTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing
    
equalsSizes :: (VarsIdTcM loc m,Location loc) => loc -> [(SExpr VarIdentifier Type,IsVariadic)] -> [(SExpr VarIdentifier Type,IsVariadic)] -> TcM loc m ()
equalsSizes l szs1 szs2 = do
    szs1' <- concatMapM (expandVariadicExpr l) szs1
    szs2' <- concatMapM (expandVariadicExpr l) szs2
    constraintList (EqualityException "size") (equalsExprTy l) l szs1' szs2'
    return ()

equalsExpr :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
equalsExpr l e1 e2 | e1 == e2 = return ()
equalsExpr l e1 e2 = do
    i1 <- prove l ("equalsExpr1 " ++ ppr e1) $ expr2ICondOrExpr $ fmap (Typed l) e1
    i2 <- prove l ("equalsExpr2 " ++ ppr e2) $ expr2ICondOrExpr $ fmap (Typed l) e2
    case (i1,i2) of
        (Left ic1,Left ic2) -> do
            b <- equalICond l ic1 ic2
            if b then return () else genTcError (locpos l) $ text "false"
        (Right ie1,Right ie2) -> isValid l (ie1 .==. ie2)
        otherwise -> genTcError (locpos l) $ text "mismatching expression types"

comparesSizes :: (VarsIdTcM loc m,Location loc) => loc -> [(Expression VarIdentifier Type,IsVariadic)] -> [(Expression VarIdentifier Type,IsVariadic)] -> TcM loc m (Comparison (TcM loc m))
comparesSizes l szs1 szs2 = do
    os <- constraintList (ComparisonException "size") comparesSize l szs1 szs2
    appendComparisons l os
  where
    comparesSize (sz1,b1) (sz2,b2) = do
        unless (b1 == b2) $ genTcError (locpos l) $ text "incomparable sizes"
        comparesExpr l sz1 sz2
    
comparesExpr :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Comparison (TcM loc m))
comparesExpr l e1 e2 | e1 == e2 = return (Comparison e1 e2 EQ)
comparesExpr l e1@(RVariablePExpr t1 v1@(VarName _ n)) e2@(RVariablePExpr t2 v2) = do
    mb1 <- tryResolveEVar l (varNameId v1) t1
    mb2 <- tryResolveEVar l (varNameId v2) t2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- exprToken
            addValueM l v1 x
            addValueM l v2 x
            return (Comparison e1 e2 EQ)
        (Just e1',Nothing) -> comparesExpr l (fmap typed e1') e2
        (Nothing,Just e2') -> comparesExpr l e1 (fmap typed e2')
        (Just e1',Just e2') -> comparesExpr l (fmap typed e1') (fmap typed e2')
comparesExpr l e1@(RVariablePExpr t1 v1) e2 = do
    mb <- tryResolveEVar l (varNameId v1) t1
    case mb of
        Nothing -> do
            addValueM l v1 e2
            return (Comparison e1 e2 GT)
        Just e1' -> comparesExpr l (fmap typed e1') e2
comparesExpr l e1 e2@(RVariablePExpr t2 v2) = do
    mb <- tryResolveEVar l (varNameId v2) t2
    case mb of
        Nothing -> do
            addValueM l v2 e1
            return (Comparison e1 e2 LT)
        Just e2' -> comparesExpr l e1 (fmap typed e2')
comparesExpr l e1 e2 = equalsExpr l e1 e2 >> return (Comparison e1 e2 EQ)

equalsExprTy :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
equalsExprTy l e1 e2 = addErrorM l (TypecheckerError (locpos l) . (EqualityException "typed expression") (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM l $ Equals (loc e1) (loc e2)
    tcCstrM l $ Equals (IdxT e1) (IdxT e2)

unifiesExprTy :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
unifiesExprTy l e1 e2 = addErrorM l (TypecheckerError (locpos l) . (UnificationException "typed expression") (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM l $ Unifies (loc e1) (loc e2)
    tcCstrM l $ Unifies (IdxT e1) (IdxT e2)
    
constraintError :: (VarsIdTcM loc m,VarsId (TcM loc m) a,VarsId (TcM loc m) b,Location loc) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> Doc) -> b -> (b -> Doc) -> Maybe SecrecError -> TcM loc m res
constraintError k l e1 pp1 e2 pp2 (Just suberr) = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    tcError (locpos l) $ k (pp1 e1') (pp2 e2') $ Just suberr
constraintError k l e1 pp1 e2 pp2 Nothing = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    tcError (locpos l) $ k (pp1 e1') (pp2 e2') Nothing

constraintList :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) [a],VarsId (TcM loc m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM loc m x) -> loc -> [a] -> [b] -> TcM loc m [x]
constraintList err f l [] [] = return []
constraintList err f l (x:xs) (y:ys) = do
    r <- f x y
    rs <- constraintList err f l xs ys
    return (r:rs)
constraintList err f l xs ys = constraintError err l xs pp ys pp Nothing

checkAssertion :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> TcM loc m ()
checkAssertion l e = do
    ic <- prove l "checkassertion" $ expr2ICond $ fmap (Typed l) e
    isValid l ic
    
checkEqual :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m ()
checkEqual l e1 e2 = do
    (i1,i2) <- prove l "checkequal" $ do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return (i1,i2)
    isValid l (i1 .==. i2)

checkIndex :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> TcM loc m ()
checkIndex l e = do
    ie <- prove l "checkindex" $ expr2IExpr $ fmap (Typed l) e
    isValid l $ ie .>=. IInt 0

checkArrayAccess :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Word64 -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
checkArrayAccess l t d low up sz = do
    (il,iu,isz) <- prove l "checkarrayaccess" $ do
        il <- expr2IExpr $ fmap (Typed l) low
        iu <- expr2IExpr $ fmap (Typed l) up
        isz <- expr2IExpr $ fmap (Typed l) sz
        return (il,iu,isz)
    isValid l $ IAnd [il .>=. IInt 0,iu .>=. IInt 0,isz .>=. il,iu .<=. isz]

tcTopPDecCstrM :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expression VarIdentifier Type,IsVariadic)] -> Type -> TcM loc m (DecType,[(Expression VarIdentifier Type,IsVariadic)])
tcTopPDecCstrM l doCoerce pid targs es tret = do
    dec <- newDecVar
    opts <- askOpts
    if (doCoerce && implicitClassify opts)
        then do
            xs <- replicateM (length es) $ do
                tx <- newTyVar
                x <- newTypedVar "parg" tx
                return x
            tcTopCstrM l $ PDec pid targs es tret dec $ Just xs
            let es' = zip (map varExpr xs) (map snd es)
            return (dec,es')
        else do
            tcTopCstrM l $ PDec pid targs es tret dec Nothing
            return (dec,es)
