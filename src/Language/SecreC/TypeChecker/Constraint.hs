{-# LANGUAGE DeriveGeneric, ScopedTypeVariables, FlexibleInstances, ConstraintKinds, StandaloneDeriving, DeriveDataTypeable, MultiParamTypeClasses, TupleSections, GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import {-# SOURCE #-} Language.SecreC.Prover.Expression
import Language.SecreC.Prover.Semantics
import Language.SecreC.Prover.SMT
import Language.SecreC.Prover.Base
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Pretty as PP
import Language.SecreC.Utils

import Control.Monad
import Control.Monad.Except
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer
import Control.Monad.RWS as RWS hiding ((<>))

import Data.Word
import Data.Bifunctor
import Data.Either
import Data.Hashable
import Data.Monoid hiding ((<>))
import Data.Unique
import Data.Maybe
import Data.Foldable as Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data hiding (cast)
import qualified Data.Map as Map
import Data.Map (Map(..))
import qualified Data.Generics as Generics
import Data.List as List
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.PatriciaTree as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.Graph.Inductive.Query.TransClos as Graph
import qualified Data.Graph.Inductive.Basic as Graph

import GHC.Generics (Generic)

import Text.PrettyPrint as PP hiding (equals)

import Safe

-- * Constraint Engine

-- solves all hypotheses in the environment
solveHypotheses :: (ProverK loc m) => loc -> TcM m [IExpr]
solveHypotheses l = do
    hyps <- liftM Set.toList getHyps
    (_,dhyps) <- tcWith (locpos l) "solveHypotheses" $ do
        addHeadTCstrs l "solveHypotheses" $ Graph.insNodes (map (\x -> (ioCstrId $ unLoc x,x)) hyps) Graph.empty
        solve l "solveHypotheses"
    addHeadTDict l "solveHypotheses" $ dhyps { tCstrs = Graph.empty }
    -- collect the result for the hypotheses
    liftM concat $ forM hyps $ \(Loc _ iok) -> do
        liftM (maybeToList . join) $ ioCstrResult l iok proxy
  where proxy = Proxy :: Proxy (Maybe IExpr)

solveSelectionWith :: ProverK loc m => loc -> String -> SolveMode -> Set LocIOCstr -> TcM m ()
solveSelectionWith l msg mode cs = tcNoDeps $ do
    newDict l $ "solveSelection " ++ msg
    mb <- solveMb l ("solveSelection " ++ msg ++ " " ++ show mode) mode cs
    case mb of
        Just err -> throwError err
        Nothing -> do
            d <- liftM (head . tDict) State.get
            State.modify $ \e -> e { tDict = tail (tDict e) }
            addHeadTDict l (msg++" solveSelectionWith") d

-- | solves the whole constraint stack
--solveAll :: ProverK loc m => loc -> String -> TcM m ()
--solveAll l msg = do
--    env <- State.get
--    let dicts = tDict env
--    let depth = length dicts
--    liftIO $ putStrLn $ "solveAll " ++ msg ++ " " ++ show depth ++ " " ++ ppr (vcat $ map (\x -> text ">" <> pp x) dicts)
--    replicateM_ depth $ do
--        solve' l msg True
--        env <- State.get
--        dicts' <- mergeHeadDict l (tDict env)
--        State.put $ env { tDict = dicts' }
--    State.modify $ \env -> env { tDict = (replicate (depth - 1) emptyTDict) ++ tDict env }

mergeHeadDict :: ProverK loc m => loc -> [TDict] -> TcM m [TDict]
mergeHeadDict l [] = return []
mergeHeadDict l [x] = return [x]
mergeHeadDict l (x:y:xs) = do
    xy <- appendTDict l (SubstMode NoCheckS False) x y
    return (xy:xs)

solveTop :: ProverK loc m => loc -> String -> TcM m ()
solveTop l msg = do
    mode <- defaultSolveMode
    solveWith l msg (mode { solveScope = SolveAll })
    gr <- State.gets (tCstrs . head . tDict)
    unless (Graph.isEmpty gr) $ do
        doc <- ppConstraints gr
        ppl <- ppr l
        error $ "solveTop: " ++ ppl ++ " " ++ msg ++ " couldn't solve all constraints " ++ show doc

solve :: ProverK loc m => loc -> String -> TcM m ()
solve l msg = do
    mode <- defaultSolveMode
    solveWith l msg mode

defaultSolveMode :: ProverK Position m => TcM m SolveMode
defaultSolveMode = do
    doAll <- getDoAll
    doSolve <- getDoSolve
    case (doAll,doSolve) of
        (True,True) -> return $ SolveMode (AllFail True) SolveAll
        (True,False) -> return $ SolveMode (AllFail False) SolveGlobal
        otherwise -> return $ SolveMode (AllFail False) SolveLocal
    
-- | solves all constraints in the top environment
solveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m ()
solveWith l msg mode = do
    cs <- topCstrs l
    mb <- solveMb l msg mode cs
    case mb of
        Nothing -> return ()
        Just err -> throwError err

solveMb :: (ProverK loc m) => loc -> String -> SolveMode -> Set LocIOCstr -> TcM m (Maybe SecrecError)
solveMb l msg mode cs = do
    --liftIO $ putStrLn $ "solving " ++ msg ++ " " ++ show doAll ++ " " ++ show doSolve ++ " " ++ ppr l ++ ppr cs
    if Set.null cs
        then return Nothing
        else newErrorM $ tcNoDeps $ do
            gr' <- buildCstrGraph l (mapSet (ioCstrId . unLoc) cs)
            debugTc $ do
                ppl <- ppr l
                ss <- ppConstraints gr'
                liftIO $ putStrLn $ "solveMb " ++ show msg ++ " " ++ ppl ++ " [" ++ show ss ++ "\n]"
            mb <- solveCstrs l msg mode
            --liftIO $ putStrLn $ "solved " ++ show msg ++ " " ++ ppr l
            --updateHeadTCstrs $ \d -> return ((),Graph.nfilter (`elem` Graph.nodes gr) d)
            debugTc $ do
                ppl <- ppr l
                ppmb <- ppr (isJust mb)
                liftIO $ putStrLn $ "solvedMb " ++ msg ++ " " ++ ppl ++ ppmb
            return mb

priorityRoots :: ProverK Position m => (x,LocIOCstr) -> (x,LocIOCstr) -> TcM m Ordering
priorityRoots x y = priorityTCstr (kCstr $ unLoc $ snd x) (kCstr $ unLoc $ snd y)

solveCstrs :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m (Maybe SecrecError)
solveCstrs l msg mode = do
    dicts <- liftM tDict State.get
    let dict = head dicts
    debugTc $ do
        ss <- ppConstraints (tCstrs dict)
        ppl <- ppr l
        liftIO $ putStrLn $ (concat $ replicate (length dicts) ">") ++ "solveCstrs " ++ show msg ++ " " ++ show mode ++ " " ++ ppl ++ " [" ++ show ss ++ "\n]"
        forM (tail dicts) $ \d -> do
          ssd <- ppConstraints (tCstrs d)
          liftIO $ putStrLn $ "\n[" ++ show ssd ++ "\n]"
        doc <- ppTSubsts =<< getTSubsts l
        liftIO $ putStrLn $ show doc
    gr <- liftM (tCstrs . head . tDict) State.get
    if (Graph.isEmpty gr)
        then do
            debugTc $ liftIO $ putStrLn $ "solvesCstrs " ++ msg ++ " empty "
            return Nothing
        else do
            roots <- sortByM priorityRoots $ rootsGr gr -- sort by constraint priority
            when (List.null roots) $ do
                ppl <- ppr l
                ppgr <- ppr gr
                ppedges <- mapM pp $ Graph.edges gr
                error $ "solveCstrs: no root constraints to proceed " ++ ppl ++ " " ++ ppgr ++ "\n\n" ++ show (sepBy comma ppedges)
            debugTc $ do
                pproots <- mapM (pp . ioCstrId . unLoc . snd) roots
                liftIO $ putStrLn $ "solveCstrsG " ++ msg ++ " [" ++ show (sepBy space pproots) ++ "\n]"
            go <- trySolveSomeCstrs mode $ map snd roots
            case go of
                -- no constraint left to solve
                Left False -> error $ "solveCstrs hiatus"
                -- at least one constraint solved
                Left True -> do
                    solveCstrs l msg mode
                -- no constraint solved because of errors
                Right errs -> do
                    mb <- solveErrors l mode errs
                    debugTc $ do
                        ppmb <- ppr mb
                        liftIO $ putStrLn $ "solvesCstrs " ++ msg ++ " exit " ++ ppmb
                    return mb

-- Left True = one constraint solved
-- Left False = no remaining unsolved constraints
-- Right err = failed
type SolveRes = Either Bool [(LocIOCstr,SecrecError)]

mergeSolveRes :: SolveRes -> SolveRes -> SolveRes
mergeSolveRes (Left True) b = Left True
mergeSolveRes (Left False) b = b
mergeSolveRes a (Left True) = Left True
mergeSolveRes a (Left False) = a
mergeSolveRes (Right a) (Right b) = Right (a ++ b)

isErrorSolveRes :: Bool -> SolveRes -> Bool
isErrorSolveRes haltFail (Left _) = False
isErrorSolveRes False (Right es) = any (not . isHaltError . snd) es
isErrorSolveRes True (Right es) = not $ null es

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (ProverK Position m) => SolveMode -> [LocIOCstr] -> TcM m SolveRes
trySolveSomeCstrs mode = foldlM solveBound (Left False)
    where
    solveBound b x = case solveFail mode of
        FirstFail haltFail -> if isErrorSolveRes False b -- we don't fail on halting errors during constraint resolution
            then return b
            else find b x
        otherwise -> find b x
    find b x = do
        found <- findCstr x
        if found
            then do
                ok <- trySolveCstr mode x
                return (mergeSolveRes b ok)
            else do
                debugTc $ do
                    ppx <- ppr (ioCstrId $ unLoc x)
                    liftIO $ putStrLn $ "didn't find queued constraint " ++ ppx
                return b

-- since templates are only resolved at instantiation time, we prevent solving of overloadable constraints
trySolveCstr :: (ProverK Position m) => SolveMode -> LocIOCstr -> TcM m SolveRes
trySolveCstr mode (Loc l iok) = do
    isMul <- isMultipleSubstsCstr (kCstr iok)
    if solveScope mode < SolveAll && isMul
        then return $ Right [(Loc l iok,TypecheckerError (locpos l) $ Halt $ GenTcError (text "Unsolved multiple substitutions constraint") Nothing)]
        else if solveScope mode < SolveGlobal && isGlobalCstr (kCstr iok)
            then return $ Right [(Loc l iok,TypecheckerError (locpos l) $ Halt $ GenTcError (text "Unsolved global constraint") Nothing)]
            else catchError
                (do
                    opens <- getOpensSet
                    if Set.member (ioCstrId iok) opens
                        then do
                            debugTc $ do
                                ppx <- ppr (ioCstrId iok)
                                liftIO $ putStrLn $ "found opened or promoted constraint " ++ ppx
                            return (Left False)
                        else solveIOCstr_ l "trySolveCstr" mode iok >> return (Left True)
                )
                (\e -> return $ Right [(Loc l iok,e)])

findCstr :: Monad m => LocIOCstr -> TcM m Bool
findCstr x = do
    ks <- State.gets (flattenIOCstrGraphSet . tCstrs . head . tDict)
--    ks <- State.gets (mconcat . map (flattenIOCstrGraphSet . tCstrs) . tDict)
    return $ Set.member x ks

getErrors :: [(LocIOCstr,SecrecError)] -> [SecrecError]
getErrors = map snd . flattenErrors
    
flattenErrors :: [(LocIOCstr,SecrecError)] -> [(LocIOCstr,SecrecError)]
flattenErrors [] = []
flattenErrors ((y,MultipleErrors errs):xs) = flattenErrors (map (\e -> (y,e)) errs ++ xs)
flattenErrors (err:xs) = err : flattenErrors xs

-- we let multiple substitution constraints go through if we are not solving the last dictionary, since these constraints can always be resolved at a later time
filterScopeErrors :: ProverK Position m => SolveScope -> [(LocIOCstr,SecrecError)] -> TcM m [(LocIOCstr,SecrecError)]
filterScopeErrors scope xs = flip filterM xs $ \x -> do
    s <- cstrScope (kCstr $ unLoc $ fst x)
    return (s <= scope)

filterFailErrors :: SolveFail -> [(LocIOCstr,SecrecError)] -> [(LocIOCstr,SecrecError)]
filterFailErrors (FirstFail haltFail) xs = if haltFail then xs else filter (not . isHaltError . snd) xs
filterFailErrors (AllFail haltFail) xs = if haltFail then xs else filter (not . isHaltError . snd) xs
filterFailErrors NoFail xs = []

filterErrors :: (ProverK loc m) => loc -> SolveMode -> [(LocIOCstr,SecrecError)] -> TcM m ([(LocIOCstr,SecrecError)])
filterErrors l mode errs = do
    errs2 <- filterWarnings l errs
    errs3 <- filterScopeErrors (solveScope mode) errs2
    let errs4 = filterFailErrors (solveFail mode) errs3
    return errs4

filterWarnings :: (ProverK loc m) => loc -> [(LocIOCstr,SecrecError)] -> TcM m [(LocIOCstr,SecrecError)]
filterWarnings l = filterM $ \(k,err) -> if isOrWarnError err
    then do
        errWarn err
        removeCstr l $ ioCstrUnique $ unLoc k
        return False
    else return True

filterCstrSetScope :: VarsGTcM m => SolveScope -> Set LocIOCstr -> TcM m (Set LocIOCstr)
filterCstrSetScope scope = filterSetM $ \x -> do
    s <- cstrScope (kCstr $ unLoc x)
    return (s <= scope)

solveErrors :: (ProverK loc m) => loc -> SolveMode -> [(LocIOCstr,SecrecError)] -> TcM m (Maybe SecrecError)
solveErrors l mode errs = do
    errs' <- filterErrors l mode (flattenErrors errs)
    if null errs'
        then return Nothing
        -- in case there are unsolved constraints that depend on multiple substitutions, solve one
        else do
            if solveScope mode >= SolveGlobal
                then do
                    mb <- guessCstr $ filter (isHaltError . snd) errs
                    case mb of
                        -- solve the multiple substitutions constraint (it always succeeds and solves the remaining dictionary)
                        Just (Loc l iok,ks) -> do
                            --liftIO $ putStrLn $ "guessCstr " ++ ppr doAll ++ " " ++ ppr iok ++ " " ++ show (sepBy space (map pp ks))
                            catchError (solveIOCstr_ l "solveErrors" mode iok >> return Nothing) (return . Just)
                        Nothing -> return $ Just (MultipleErrors $ getErrors errs')
                else return $ Just (MultipleErrors $ getErrors errs')

guessCstr :: ProverK Position m => [(LocIOCstr,SecrecError)] -> TcM m (Maybe (LocIOCstr,[LocIOCstr]))
guessCstr errs = do
    opens <- getOpensSet
    search $ filter (\(Loc l iok,err) -> not $ Set.member (ioCstrId iok) opens) errs
  where
    search [] = return Nothing
    search (x:xs) = do
        is <- isSubst x
        if is
            then do
                let xs' = List.deleteBy (\x y -> fst x == fst y) x errs
                return $ Just (fst x,map fst xs')
            else search xs
    isSubst (Loc l iok,err) = isMultipleSubstsCstr (kCstr iok)

solveIOCstr_ :: (ProverK loc m) => loc -> String -> SolveMode -> IOCstr -> TcM m ()
solveIOCstr_ l msg mode iok = do
    catchError solve (\err -> do
        debugTc $ do
            ppiok <- ppr (ioCstrId iok)
            pperr <- ppr err
            liftIO $ putStrLn $ "nonsolvedIOCstr " ++ ppiok ++ " " ++ pperr
        throwError err)
  where
    solve = newErrorM $ resolveIOCstr_ l iok $ \k gr ctx -> do
        --olds <- State.gets (mconcat . map (mapSet (ioCstrId . unLoc) . flattenIOCstrGraphSet . tCstrs) . tDict)
        ppiok <- ppr iok
        let (ins,_,_,outs) = fromJustNote ("solveCstrNodeCtx " ++ ppiok) ctx
        --let ins'  = map (fromJustNote "ins" . Graph.lab gr . snd) ins
        --let outs' = map (fromJustNote "outs" . Graph.lab gr . snd) outs
        debugTc $ do
            ppins <- mapM (pp . snd) ins
            ppiok <- ppr (ioCstrId iok)
            ppouts <- mapM (pp . snd) outs
            liftIO $ putStrLn $ "solveIOCstr " ++ show (sepBy space ppins) ++" --> "++ ppiok ++" --> "++ show (sepBy space ppouts)
        ppiok <- ppr (ioCstrId iok)
        (res,rest) <- tcWith (locpos l) (msg ++ " solveIOCstr " ++ ppiok) $ resolveTCstr l mode (ioCstrId iok) k
        addHeadTDict l (msg++ " solveIOCstr_ " ++ ppiok) $ rest { tCstrs = Graph.empty }
        debugTc $ do
            doc <- ppConstraints $ tCstrs rest
            ion <- ppr (ioCstrId iok)
            liftIO $ putStrLn $ "solvedIOCstr " ++ ion -- ++ " -->" ++ show doc
        unless (Graph.isEmpty $ tCstrs rest) $ do
            top <- buildCstrGraph l (Set.insert (ioCstrId iok) (Set.fromList $ map snd $ ins ++ outs))
            let ins' = map (fromJustNote "ins" . Graph.lab top . snd) ins
            let outs' = map (fromJustNote "outs" . Graph.lab top . snd) outs
            let rest' = tCstrs rest
            --let rest' = Graph.nfilter (\n -> not $ Set.member n olds) $ tCstrs rest
            debugTc $ do
                doc <- ppConstraints rest'
                doc1 <- ppTSubsts (tSubsts rest)
                liftIO $ putStrLn $ "solvedIOCstr rest" ++ show doc1 ++ "\n" ++ show doc
            replaceCstrWithGraph l False (ioCstrId iok) (Set.fromList ins') rest' (Set.fromList outs')
        dicts <- State.gets tDict
        debugTc $ forM_ dicts $ \d -> do
            ssd <- ppConstraints (tCstrs d)
            liftIO $ putStrLn $ "\n[" ++ show ssd ++ "\n]"
        return res

solveNewCstr_ :: ProverK loc m => loc -> SolveMode -> IOCstr -> TcM m ()
solveNewCstr_ l mode iok = newErrorM $ resolveIOCstr_ l iok (\k gr ctx -> resolveTCstr l mode (ioCstrId iok) k)

-- * Throwing Constraints

tCstrM_ :: ProverK loc m => loc -> TCstr -> TcM m ()
tCstrM_ l (TcK c st) = withCstrState l st $ tcCstrM_ l c
tCstrM_ l (CheckK c st) = withCstrState l st $ checkCstrM_ l Set.empty c
tCstrM_ l (HypK c st) = withCstrState l st $ hypCstrM_ l c

checkCstrM_ :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m ()
checkCstrM_ l deps k = checkCstrM l deps k >> return ()

checkCstrM :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m (Maybe IOCstr)
checkCstrM l deps k | isTrivialCheckCstr k = return Nothing
checkCstrM l deps k = withDeps LocalScope $ do
    addDeps LocalScope deps
    st <- getCstrState
    newTCstr l $ CheckK k st

topCheckCstrM_ :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m ()
topCheckCstrM_ l deps k = newErrorM $ checkCstrM_ l deps k

topCheckCstrM :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m (Maybe IOCstr)
topCheckCstrM l deps k = newErrorM $ checkCstrM l deps k

hypCstrM_ :: (ProverK loc m) => loc -> HypCstr -> TcM m ()
hypCstrM_ l k = hypCstrM l k >> return ()

hypCstrM :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IOCstr)
hypCstrM l k | isTrivialHypCstr k = return Nothing
hypCstrM l k = do
    st <- getCstrState
    newTCstr l $ HypK k st

topHypCstrM_ :: (ProverK loc m) => loc -> HypCstr -> TcM m ()
topHypCstrM_ l k = newErrorM $ hypCstrM_ l k

topHypCstrM :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IOCstr)
topHypCstrM l k = newErrorM $ hypCstrM l k

tcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
tcCstrM_ l k = tcCstrM l k >> return ()

tcCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM m (Maybe IOCstr)
tcCstrM l k | isTrivialTcCstr k = return Nothing
tcCstrM l k = do
    debugTc $ do
        ppl <- ppr l
        ppk <- ppr k
        liftIO $ putStrLn $ "tcCstrM " ++ ppl ++ " " ++ ppk
    st <- getCstrState
    k <- newTCstr l $ TcK k st
    --gr <- liftM (tCstrs . head . tDict) State.get
    --doc <- ppConstraints gr
    --liftIO $ putStrLn $ "tcCstrMexit " ++ ppr (maybe (-1) ioCstrId k) ++" " ++ show doc
    return k

topTcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
topTcCstrM_ l k = newErrorM $ tcCstrM_ l k
    
newTCstr :: (ProverK loc m) => loc -> TCstr -> TcM m (Maybe IOCstr)
newTCstr l k = do
    deps <- getDeps
    iok <- newTemplateConstraint l k
    addIOCstrDependenciesM l True deps (Loc (locpos l) iok) Set.empty
    
    if (isGlobalCstr k)
        then return Nothing
        else catchError
            (defaultSolveMode >>= \mode -> solveNewCstr_ l mode iok >> return Nothing)
            (\e -> if (isHaltError e) then return (Just iok) else throwError e)
                
resolveTCstr :: (ProverK loc m) => loc -> SolveMode -> Int -> TCstr -> TcM m ShowOrdDyn
resolveTCstr l mode kid (TcK k st) = liftM ShowOrdDyn $ withDeps GlobalScope $ withCstrState l st $ do
    resolveTcCstr l mode kid k
resolveTCstr l mode kid (HypK h st) = liftM ShowOrdDyn $ withDeps GlobalScope $ withCstrState l st $ do
    resolveHypCstr l mode h
resolveTCstr l mode kid (CheckK c st) = liftM ShowOrdDyn $ withDeps GlobalScope $ withCstrState l st $ do
    resolveCheckCstr l mode c

-- tests if a constraint is only used as part of an hypothesis
--isHypInGraph :: Int -> IOCstrGraph loc -> Bool
--isHypInGraph kid gr = case Graph.match kid gr of
--    (Nothing,gr') -> False
--    (Just (_,_,(kCstr . unLoc) -> HypK {},_),gr') -> True
--    (Just (_,_,_,outs),gr') -> all (flip isHypInGraph gr' . snd) outs

resolveTcCstr :: (ProverK loc m) => loc -> SolveMode -> Int -> TcCstr -> TcM m ()
resolveTcCstr l mode kid k = do
--    gr <- liftM (tCstrs . headNe . tDict) State.get
--    let warn = isHypInGraph kid gr
--    liftIO $ putStrLn $ "resolve " ++ show warn ++ " " ++ ppr k
--    if warn then newErrorM $ orWarn_ $ resolveTcCstr' k else 
    resolveTcCstr' kid k
  where
    resolveTcCstr' kid k@(TDec isTplt n@(TIden tn) args x) = do
        ppn <- pp n
        ppargs <- mapM pp args
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (ppn <+> parens (sepBy comma ppargs)))) $ do
            isAnn <- getAnn
            isLeak <- getLeak
            let check = if isTplt then checkTemplateType else checkNonTemplateType
            res <- matchTemplate l kid True (TIden tn) (Just args) Nothing Nothing [] (check isAnn isLeak $ fmap (const l) $ TypeName () tn)
            unifiesDec l x res
    resolveTcCstr' kid k@(PDec n@(PIden pn) specs args r x doCoerce xs) = do
        ppr <- pp r
        ppn <- pp n
        ppargs <- mapM pp args
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (ppr <+> ppn <+> parens (sepBy comma ppargs)))) $ do
            isAnn <- getAnn
            isLeak <- getLeak
            kind <- getKind
            res <- matchTemplate l kid doCoerce (PIden pn) specs (Just args) (Just r) xs (checkProcedureFunctionLemma isAnn isLeak kind $ ProcedureName l $ PIden pn)
            --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate " ++ ppr n ++ " " ++ show doc
            unifiesDec l x res
            --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate2 " ++ ppr n ++ " " ++ show doc
    resolveTcCstr' kid k@(PDec o@(OIden on) specs args r x doCoerce xs) = do
        ppr <- pp r
        ppo <- pp o
        ppargs <- mapM pp args
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (ppr <+> ppo <+> parens (sepBy comma ppargs)))) $ do
            isAnn <- getAnn
            isLeak <- getLeak
            k <- getKind
            res <- matchTemplate l kid doCoerce o specs (Just args) (Just r) xs (checkOperator isAnn isLeak k $ fmap (const l) on)
            --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate " ++ ppr o ++ " " ++ show doc
            unifiesDec l x res
            --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate2 " ++ ppr o ++ " " ++ show doc
    resolveTcCstr' kid k@(Equals t1 t2) = do
        equals l t1 t2
    resolveTcCstr' kid k@(Coerces e1 x2) = do
        opts <- askOpts
        if implicitCoercions opts
            then coerces l e1 x2 else
                unifiesExpr l True (varExpr x2) e1
    resolveTcCstr' kid k@(CoercesN exs) = do
        opts <- askOpts
        if implicitCoercions opts
            then coercesN l exs
            else do
                unifiesN l $ map (loc . fst) exs
                assignsExprTys l exs
    resolveTcCstr' kid k@(CoercesLit e) = do
        coercesLit l e
    resolveTcCstr' kid k@(CoercesSecDimSizes e1 x2) = do
        opts <- askOpts
        if implicitCoercions opts
            then coercesSecDimSizes l e1 x2
            else unifiesExpr l True (varExpr x2) e1
    resolveTcCstr' kid k@(CoercesNSecDimSizes exs) = do
        opts <- askOpts
        if implicitCoercions opts
            then coercesNSecDimSizes l exs
            else do
                unifiesN l $ map (loc . fst) exs
                assignsExprTys l exs
    resolveTcCstr' kid k@(Unifies t1 t2) = do
        unifies l t1 t2
    resolveTcCstr' kid k@(Assigns t1 t2) = do
        assigns l t1 t2
    resolveTcCstr' kid k@(TypeBase t x) = do
        BaseT b <- typeBase l t
        unifiesBase l x b
    resolveTcCstr' kid k@(SupportedPrint t xs) = do
        isSupportedPrint l t xs
    resolveTcCstr' kid k@(ProjectStruct t a x) = do
        ppt <- pp t
        ppa <- pp a
        ppx <- pp x
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedFieldProjection (ppt) (ppa <+> char '=' <+> ppx))
            (do
                res <- projectStructField l t a
                unifies l x (ComplexT res)
            )
    resolveTcCstr' kid k@(ProjectMatrix ct rngs x) = do
        ct' <- ppM l ct
        rngs' <- ppArrayRangesM l rngs
        x' <- ppM l x
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedMatrixProjection ct' (brackets rngs' <+> char '=' <+> x'))
            (do
                res <- projectMatrixType l ct rngs
                unifies l x res
            )
    resolveTcCstr' kid (MultipleSubstitutions v s) = do
        let mkSubst (x,y,z) = do
            ppx <- pp x
            ppy <- pp y
            return ((mapM_ (tCstrM_ l) x,ppx),(\b -> mapM_ (tCstrM_ l) y,ppy),(const $ return (),PP.empty),z)
        s' <- mapM mkSubst s
        multipleSubstitutions l kid SolveGlobal v s'
    resolveTcCstr' kid (MatchTypeDimension t d) = matchTypeDimension l t d
    resolveTcCstr' kid (IsValid c) = do
        x <- ppM l c
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid x) $ do
            ic <- prove l "resolve isValid" $ expr2IExpr $ fmap (Typed l) c
            isValid l ic
    resolveTcCstr' kid (NotEqual e1 e2) = do
        x <- ppM l e1
        y <- ppM l e2
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid (x <+> text "!=" <+> y)) $ do
            i1 <- prove l "resolve notEqual" $ expr2IExpr $ fmap (Typed l) e1
            i2 <- prove l "resolve notEqual" $ expr2IExpr $ fmap (Typed l) e2
            isValid l $ IBinOp INeq i1 i2
    resolveTcCstr' kid (IsPublic b t) = do
        isPublic l b t
    resolveTcCstr' kid (IsPrivate b t) = do
        isPrivate l b t
    resolveTcCstr' kid (ToMultiset t x) = do
        ct <- toMultisetType l t
        unifiesComplex l x ct
    resolveTcCstr' kid (Resolve t) = do
        resolve l t
    resolveTcCstr' kid (Default szs e) = do
        ppl <- pp (loc e)
        pps <- pp szs
        let msg = text "failed to resolve default expression for" <+> ppl <+> pps
        addErrorM l (TypecheckerError (locpos l) . GenTcError msg . Just) $ do
            let t = loc e
            res <- defaultExpr l t szs
            unifiesExpr l True e res
    resolveTcCstr' kid k = do
        ppkid <- ppr kid
        ppk <- ppr k
        error $ "resolveTcCstr: " ++ ppkid ++ " " ++ ppk

resolve :: ProverK loc m => loc -> Type -> TcM m ()
resolve l (KindT s) = resolveKind l s
resolve l t = do
    ppt <- pp t
    genTcError (locpos l) $ text "failed to resolve" <+> ppt

resolveKind :: ProverK loc m => loc -> KindType -> TcM m ()
resolveKind l PublicK = return ()
resolveKind l (PrivateK {}) = return ()
resolveKind l k@(KVar v@(nonTok -> True) isPriv) = do
    mb <- tryResolveKVar l v
    case mb of
        Just k' -> resolveKind l k'
        Nothing -> do
            ppk <- pp k
            throwTcError (locpos l) $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "failed to resolve kind" <+> ppk) Nothing
resolveKind l (KVar v@(nonTok -> False) isPriv) = return ()

resolveHypCstr :: (ProverK loc m) => loc -> SolveMode -> HypCstr -> TcM m (Maybe IExpr)
resolveHypCstr l mode hyp = do
    if solveScope mode < SolveAll -- if we don't need to solve all constraints we accept no less than solving the hypothesis
        then do
            pph <- pp hyp
            newErrorM $ addErrorM l (TypecheckerError (locpos l) . FailAddHypothesis (pph)) $ orWarn $ resolveHypCstr' hyp
        else liftM Just $ resolveHypCstr' hyp
  where
    resolveHypCstr' (HypCondition c) = expr2IExpr $ fmap (Typed l) c
    resolveHypCstr' (HypNotCondition c) = liftM (IUnOp INot) $ expr2IExpr $ fmap (Typed l) c
    resolveHypCstr' (HypEqual e1 e2) = do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return $ IBinOp (IEq) i1 i2
    
resolveCheckCstr :: (ProverK loc m) => loc -> SolveMode -> CheckCstr -> TcM m ()
resolveCheckCstr l mode k = do
    ppk <- pp k
    addErrorM l (OrWarn . TypecheckerError (locpos l) . StaticAssertionFailure (ppk)) $ do
        resolveCheckCstr' k
  where
    resolveCheckCstr' (CheckAssertion c) = checkAssertion l c

ioCstrResult :: (Hashable a,IsScVar (TcM m) a,MonadIO m,Location loc) => loc -> IOCstr -> Proxy a -> TcM m (Maybe a)
ioCstrResult l iok proxy = do
    st <- readCstrStatus (locpos l) iok
    case st of
        Evaluated rest t -> liftM Just $ cstrResult l (kCstr iok) proxy t
        Erroneous err -> return Nothing
        Unevaluated -> return Nothing
    where
    cstrResult :: (Hashable a,IsScVar (TcM m) a,Monad m,Location loc) => loc -> TCstr -> Proxy a -> ShowOrdDyn -> TcM m a
    cstrResult l k (Proxy::Proxy t) dyn = case fromShowOrdDyn dyn of
        Nothing -> do
            ppk <- pp k
            genError (locpos l) $ text "Wrong IOCstr output type" <+> text (show dyn) <+> text "::" <+> text (show $     applyShowOrdDyn Generics.typeOf dyn) <+> text "with type" <+> text (show $ Generics.typeOf (error "applyShowOrdDyn"::t)) <+> ppk
        Just x -> return x

tcProve :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)
tcProve l msg m = do
    mode <- defaultSolveMode
    tcProveWith l msg mode m

tcProveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m (a,TDict)
tcProveWith l msg mode m = do
    newDict l $ "tcProve " ++ msg
    x <- m
    solveWith l msg mode
    d <- liftM (head . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (x:xs) = xs

tcProveTop :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)
tcProveTop l msg m = do
    newDict l $ "tcProve " ++ msg
    x <- m
    solveTop l msg
    d <- liftM (head . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (x:xs) = xs

proveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m (a,TDict)
proveWith l msg mode proof = tcProveWith l msg mode proof

orError :: ProverK Position m => TcM m a -> TcM m (Either SecrecError a)
orError m = liftM Right m `catchError` (return . Left)

proveWithMode :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m a
proveWithMode l msg mode m = do
    (a,dict) <- tcProveWith l msg mode m
    addHeadTDict l (msg++" proveWithMode") dict
    return a
    
prove :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a
prove l msg m = do
    mode <- defaultSolveMode
    proveWithMode l msg mode m

-- * Solving constraints

-- labels = variables, edges = maybe constraints
type VarGr = Graph.Gr VarIdentifier (Maybe LocIOCstr)

buildVarGr :: ProverK loc m => loc -> State.StateT (Int,Map VarIdentifier Int) (TcM m) VarGr
buildVarGr l = do
    ds <- lift $ State.gets tDict
    let addSubsts g (TSubsts ss) = foldM addSubst g $ Map.toList ss
        addSubst g (key,val) = do
            vals <- lift $ liftM (videns . Map.keysSet) $ fvs val
            addEdges g Nothing (key:Set.toList vals)
        addCstrs g ks = foldM addCstr g $ Set.toList $ flattenIOCstrGraphSet ks
        addCstr g iok@(Loc l k) = do
            vals <- lift $ liftM (videns . Map.keysSet) $ fvs $ kCstr k
            addEdges g (Just iok) (Set.toList vals)
        addEdges g mb [] = return g
        addEdges g mb [x] = addEdge g mb x x
        addEdges g mb (x:y:zs) = do
            g' <- addEdge g mb x y
            addEdges g' mb (y:zs)
        addEdge g mb x y = do
            (g1,nx) <- newNode g x
            (g2,ny) <- newNode g1 y
            return $ Graph.insEdge (nx,ny,mb) g2
        newNode g x = do
            (i,st) <- State.get
            case Map.lookup x st of
                Just n -> return (g,n)
                Nothing -> do
                    State.put (succ i,Map.insert x i st)
                    return (Graph.insNode (i,x) g,i)
        mk g d = do
            g' <- addCstrs g (tCstrs d)
            addSubsts g' (tSubsts d)
    foldM mk Graph.empty ds

reachableVarGr :: Map VarIdentifier Int -> VarGr -> Set LocIOCstr
reachableVarGr cs g = mconcat $ Graph.preorderF (Graph.udffWith getCstrs (Map.elems cs) g)
    where
    getCstrs (froms,n,v,tos) = Set.fromList $ (catMaybes $ map fst froms) ++ (catMaybes $ map fst tos)

relatedCstrs :: ProverK loc m => loc -> [Int] -> Set VarIdentifier -> (Set LocIOCstr -> TcM m (Set LocIOCstr)) -> TcM m (Set LocIOCstr)
relatedCstrs l kids vs filter = do
    (vgr,(_,st)) <- State.runStateT (buildVarGr l) (0,Map.empty)
    -- note: we don't need to solve nested multiplesubstitutions, since they are guaranteed to succeed later
    dependents <- dependentCstrs l kids
    filtered <- (filter $ reachableVarGr (Map.intersection st $ Map.fromSet (const "msubsts") vs) vgr)
    return $ Set.difference filtered dependents
    
multipleSubstitutions :: (ProverK loc m,Vars GIdentifier (TcM m) a) => loc -> Int -> SolveScope -> a -> [((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier)] -> TcM m d
multipleSubstitutions l kid scope bv ss = do
    opts <- askOpts
    bvs <- liftM (videns . Map.keysSet) $ fvs bv -- variables bound by the multiple substitutions
    debugTc $ do
        ppbvs <- ppr bvs
        liftIO $ putStrLn $ "multipleSubstitutions bounds: " ++ ppbvs
    cs <- relatedCstrs l [kid] bvs (filterCstrSetScope scope)
    debugTc $ do
        ppcs <- liftM (sepBy space) $ mapM (pp . ioCstrId . unLoc) $ Set.toList cs
        liftIO $ putStrLn $ "multipleSubstitutions constraints: " ++ show ppcs
    --liftIO $ putStrLn $ ppr l ++ " multiple substitutions "++show kid ++" "++ ppr (sepBy comma $ map (pp . fst3) ss)
    let removes = do
        let fs = Set.unions $ map fou4 ss
        forM_ fs removeFree
    if backtrack opts
        then do
            ok <- newErrorM $ matchAll l kid scope cs ss (matchOne l kid scope cs) []
            case ok of
                Left d -> removes >> return d
                Right errs -> tcError (locpos l) $ MultipleTypeSubstitutions errs
        else do
            ok <- newErrorM $ matchAll l kid scope cs ss (matchHead l kid scope cs) []
            case ok of
                Left y -> matchBody l kid scope cs y >>= \d -> removes >> return d
                Right errs -> tcError (locpos l) $ MultipleTypeSubstitutions errs
    
matchAll :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> [((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier)] -> (((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier) -> TcM m x) -> [(Doc,SecrecError)] -> TcM m (Either x [(Doc,SecrecError)])
matchAll l kid scope cs [] match errs = return $ Right errs
matchAll l kid scope cs (x:xs) match errs = catchError
    -- match and solve all remaining constraints
    (liftM Left $ match x)
    -- backtrack and try another match
    (\e -> do
        debugTc $ do
            pe <- ppr e
            liftIO $ putStrLn $ "failed " ++ show (snd (fst4 x)) ++ " " ++ pe
        matchAll l kid scope cs xs match (errs++[(snd (fst4 x),e)])
        --throwError e
    )

matchOne :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> ((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier) -> TcM m d
matchOne l kid scope cs (match,deps,post,frees) = do
    res <- matchHead l kid scope cs (match,deps,post,frees)
    matchBody l kid scope cs res

matchHead :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> ((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier) -> TcM m ((b,Set LocIOCstr),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier)
matchHead l kid scope cs (match,deps,post,frees) = do
--    forSetM_ cs $ \(Loc _ iok) -> liftIO $ readIdRef (kStatus iok) >>= \st -> case st of
--            Erroneous _ -> writeIdRef (kStatus iok) Unevaluated
--            otherwise -> return ()
    debugTc $ do
        ppl <- ppr l
        liftIO $ putStrLn $ ppl ++ " trying to match head"++show kid ++ " " ++ show (snd match)
    mode <- defaultSolveMode
    (b,ks) <- proveWithMode l ("matchOneHead"++show kid) (mode { solveScope = scope }) $ tcWithCstrs l ("matchOneHead"++show kid) (fst match)
    return ((b,ks),deps,post,frees)

matchBody :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> ((b,Set LocIOCstr),(b -> TcM m c,Doc),(c -> TcM m d,Doc),Set VarIdentifier) -> TcM m d
matchBody l kid scope cs ((b,ks),deps,post,_) = do
    debugTc $ do
        ppl <- ppr l
        liftIO $ putStrLn $ ppl ++ " trying to match "++show kid
    mode <- defaultSolveMode
    c <- proveWithMode l ("matchOneHead"++show kid) (mode { solveScope = scope }) $ withDependencies ks ((fst deps) b)
    
    -- solve all other dependencies
    --liftIO $ putStrLn $ "matchOne solved head" ++ show kid ++ " " ++ ppr match
    solveSelectionWith l ("matchone"++show kid) (mode { solveFail = FirstFail True, solveScope = scope }) cs
    debugTc $ liftIO $ putStrLn $ "matchOne solved " ++ show kid
    (fst post) c

tryCstr :: (ProverK loc m) => loc -> TcM m a -> TcM m (Either SecrecError a)
tryCstr l m = (liftM Right $ prove l "tryCstr" $ m) `catchError` (return . Left)

tryCstrBool :: (ProverK loc m) => loc -> TcM m a -> TcM m Bool
tryCstrBool l m = liftM (maybe False (const True)) $ tryCstrMaybe l m

tryCstrMaybe :: (ProverK loc m) => loc -> TcM m a -> TcM m (Maybe a)
tryCstrMaybe l m = do
    mb <- tryCstr l m
    case mb of
        Right x -> return $ Just x
        Left err -> if isHaltError err
            then throwError err
            else do
--                liftIO $ putStrLn $ "tryCstrMaybe " ++ ppr err
                return Nothing

-- can the second argument be given the first type?
isTyOf :: (ProverK loc m) => loc -> Type -> Type -> TcM m Bool
isTyOf l tt t = tryCstrBool l $ unifies l (tyOf t) tt

--tryNot :: ProverK loc m => loc -> [TCstr] -> TcM m (Either SecrecError SecrecError)
--tryNot = undefined

--tryNotUnifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m (Either Doc SecrecError)
--tryNotUnifies l t1 t2 = (prove l True (unifies l t1 t2) >> return (Right err)) `catchError` handleErr
--    where
--    err = GenericError (locpos l) $ text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "should not unify."
--    ok = text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "unify."
--    handleErr e = if isHaltError e
--        then throwError e
--        else return $ Left ok

-- checks if two types are equal, without using coercions, not performing substitutions
equals :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()
equals l (NoType _) (NoType _) = return ()
equals l (IdxT e1) (IdxT e2) = do
    equalsExpr l True e1 e2
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
equals l (TType isNotVoid1) (TType isNotVoid2) = return ()
equals l DType DType = return ()
equals l BType BType = return ()
equals l (KType _) (KType _) = return ()
equals l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM_ l $ Equals b1 b2
    equalsExprTy l True sz1 sz2
equals l (KindT k1) (KindT k2) = equalsKind l k1 k2
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
equals l (CondType t1 c1) (CondType t2 c2) = do
    equals l t1 t2
    equalsExprTy l False c1 c2
equals l (VArrayT a1) (VArrayT a2) = equalsArray l a1 a2
equals l t1 t2 = constraintError (EqualityException "type") l t1 pp t2 pp Nothing

equalsKind :: (ProverK loc m) => loc -> KindType -> KindType -> TcM m ()
equalsKind l PublicK PublicK = return ()
equalsKind l (KVar k1 priv1) (KVar k2 priv2) | k1 == k2 = return ()
equalsKind l (KVar k1@(nonTok -> True) priv1) k2 = do
    k1' <- resolveKVar l k1
    tcCstrM_ l $ Equals (KindT k1') (KindT k2)
equalsKind l k1 (KVar k2@(nonTok -> True) priv2) = do
    k2' <- resolveKVar l k2
    tcCstrM_ l $ Equals (KindT k1) (KindT k2')
equalsKind l (PrivateK k1) (PrivateK k2) | k1 == k2 = return ()
equalsKind l k1 k2 = constraintError (EqualityException "kind") l k1 pp k2 pp Nothing

equalsArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m ()
equalsArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    equalsList l ts1 ts2
    tcCstrM_ l $ Equals b1 b2
equalsArray l (VAVar v1 b1 sz1) (VAVar v2 b2 sz2) | v1 == v2 = do
    tcCstrM_ l $ Equals b1 b2
    equalsExprTy l True sz1 sz2
equalsArray l t1 t2 = constraintError (EqualityException "array") l t1 pp t2 pp Nothing

equalsSys :: (ProverK loc m) => loc -> SysType -> SysType -> TcM m ()
equalsSys l (SysPush t1) (SysPush t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysRet t1) (SysRet t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysRef t1) (SysRef t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysCRef t1) (SysCRef t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l t1 t2 = constraintError (EqualityException "syscall type") l t1 pp t2 pp Nothing

equalsSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()
equalsSec l Public Public = return ()
equalsSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
equalsSec l (SVar v1 k1) (SVar v2 k2) | v1 == v2 = equalsKind l k1 k2
equalsSec l (SVar v@(nonTok -> True) _) s2 = do
    s1 <- resolveSVar l v
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 (SVar v@(nonTok -> True) _) = do
    s2 <- resolveSVar l v
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 s2 = constraintError (EqualityException "security type") l s1 pp s2 pp Nothing

equalsDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m ()
equalsDec l (DVar v1) (DVar v2) | v1 == v2 = return ()
equalsDec l (DVar v1@(nonTok -> True)) d2 = do
    d1 <- resolveDVar l v1
    tcCstrM_ l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 (DVar v2@(nonTok -> True)) = do
    d2 <- resolveDVar l v2
    tcCstrM_ l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 d2 | isJust (decTypeTyVarId d1) && decTypeTyVarId d1 == decTypeTyVarId d2 = return ()
equalsDec l d1 d2 = do
    p1 <- ppr (decTypeTyVarId d1)
    p2 <- ppr (decTypeTyVarId d2)
    constraintError (EqualityException ("declaration type " ++ p1 ++ " " ++ p2)) l d1 pp d2 pp Nothing

equalsComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m ()
--equalsComplex l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
--equalsComplex l (ArrayLit es1) (ArrayLit es2) = do
--    constraintList (EqualityException "size") (equalsExprTy l) l es1 es2
--    return ()
equalsComplex l (CType s1 t1 d1) (CType s2 t2 d2) = do
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
    equalsExprTy l True d1 d2
equalsComplex l (CVar v1 _) (CVar v2 _) | v1 == v2 = return ()
equalsComplex l (CVar v@(nonTok -> True) _) c2 = do
    c1 <- resolveCVar l v
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l c1 (CVar v@(nonTok -> True) _) = do
    c2 <- resolveCVar l v
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l Void Void = return ()
equalsComplex l c1 c2 = constraintError (EqualityException "complex type") l c1 pp c2 pp Nothing

equalsBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m ()
equalsBase l (BVar v1) (BVar v2) | v1 == v2 = return ()
equalsBase l (BVar v@(nonTok -> True)) t2 = do
    t1 <- resolveBVar l v
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l t1 (BVar v@(nonTok -> True)) = do
    t2 <- resolveBVar l v
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l (TApp (TIden n1) ts1 d1) (TApp (TIden n2) ts2 d2) = do
    equalsTIdentifier l (TIden n1) (TIden n2)
    equalsTpltArgs l ts1 ts2
    --equalsDec l d1 d2
equalsBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
equalsBase l (MSet b1) (MSet b2) = equalsBase l b1 b2
equalsBase l b1 b2 = constraintError (EqualityException "base type") l b1 pp b2 pp Nothing

equalsFoldable :: (ProverK loc m,Foldable t) => loc -> t Type -> t Type -> TcM m ()
equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)

equalsList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()
equalsList l [] [] = return ()
equalsList l (x:xs) (y:ys) = do
    tcCstrM_ l $ Equals x y
    equalsList l xs ys
equalsList l xs ys = constraintError (EqualityException "type") l xs pp ys pp Nothing

equalsPrim :: (ProverK loc m) => loc -> PrimitiveDatatype () -> PrimitiveDatatype () -> TcM m ()
equalsPrim l p1 p2 | p1 == p2 = return ()
equalsPrim l t1 t2 = constraintError (EqualityException "primitive type") l t1 pp t2 pp Nothing

expandCTypeVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType
expandCTypeVar l v = do
    k <- newKindVar "k" False False Nothing
    d <- newDomainTyVar "d" k False Nothing
    t <- newBaseTyVar False Nothing
    dim <- newDimVar False Nothing
    let ct = CType d t dim 
    addSubstM l (SubstMode NoFailS True) (VarName (TType True) $ VIden v) $ ComplexT ct
    return ct

-- | Non-directed coercion for a list of expressions.
-- Returns the unified type.
-- applies substitutions
coercesN :: ProverK loc m => loc -> [(Expr,Var)] -> TcM m ()
coercesN l exs | all (isComplex . loc . fst) exs = do
    exs' <- forM exs $ \(e,x) -> do
        ct <- typeToComplexType l (loc e)
        let e' = updLoc e (ComplexT ct)
        return (e',x)
    coercesNComplex l exs'
coercesN l exs = do
    ppexs <- mapM (ppExprTy . fst) exs
    addErrorM l (TypecheckerError (locpos l) . NCoercionException "type" Nothing (ppexs) . Just) $ do
        unifiesN l $ map (loc . fst) exs
        assignsExprTys l exs

coercesNComplex :: ProverK loc m => loc -> [(Expr,Var)] -> TcM m ()
coercesNComplex l exs | any (isVoid . unComplexT . loc . fst) exs = do
    ppexs <- mapM (ppExprTy . fst) exs
    addErrorM l (TypecheckerError (locpos l) . NCoercionException "complex type" Nothing (ppexs) . Just) $ do
        unifiesN l $ map (loc . fst) exs
        assignsExprTys l exs
coercesNComplex l exs | any (isCVar . unComplexT . loc . fst) exs = do
    exs' <- forM exs $ \(e,x) -> case loc e of
        ComplexT (CVar v@(nonTok -> True) isNotVoid) -> do
            mb <- tryResolveCVar l v
            t' <- case mb of
                Nothing -> if isNotVoid
                    then expandCTypeVar l v
                    else do
                        ppexs <- mapM (ppExprTy . fst) exs
                        tcError (locpos l) $ Halt $ NCoercionException "complex type" Nothing (ppexs) Nothing
                Just t' -> return t'
            return (updLoc e $ ComplexT t',x)
        otherwise -> return (e,x)
    coercesNComplex l exs'
coercesNComplex l exs | all (isCType . unComplexT . loc . fst) exs = do
    ppexs <- mapM (ppExprTy . fst) exs
    addErrorM l (TypecheckerError (locpos l) . (NCoercionException "complex type") Nothing (ppexs) . Just) $ do
        -- we unify base types, no coercions here
        unifiesN l $ map (BaseT . baseCType . unComplexT . loc . fst) exs
        -- coerce security and dimension types
        tcCstrM_ l $ CoercesNSecDimSizes exs
coercesNComplex l exs = do
    ppexs <- mapM (ppExprTy . fst) exs
    tcError (locpos l) $ NCoercionException "complex type" Nothing (ppexs) Nothing

coercesNSecDimSizes :: (ProverK loc m) => loc -> [(Expr,Var)] -> TcM m ()
coercesNSecDimSizes l [] = return ()
coercesNSecDimSizes l exs = do
    let cts = map (unComplexT . loc . fst) exs
    s3 <- maxSec l $ map secCType cts
    let b3 = baseCType $ head cts
    d3 <- maxDim l $ map dimCType cts
    let t3 = ComplexT $ CType s3 b3 d3
    -- coerce each expression individually
    forM_ exs $ \(e,x) -> do
        tcCstrM_ l $ Unifies (loc x) t3
        coercesSecDimSizes l e x

maxSec :: ProverK loc m => loc -> [SecType] -> TcM m SecType
maxSec l ss = do
    maxs <- maximumsSec l ss []
    case maxs of
        [s] -> return s
        (SVar v k:_) -> newDomainTyVar "smax" k False Nothing
        (s:_) -> return s

maximumsSec :: ProverK loc m => loc -> [SecType] -> [SecType] -> TcM m [SecType]
maximumsSec l [] maxs = return maxs
maximumsSec l (s:ss) [] = maximumsSec l ss [s]
maximumsSec l (s:ss) maxs@(max:_) = do
    cmp <- tcBlock $ comparesSec l True s max
    case compOrdering cmp of
        (LT,isLat) -> maximumsSec l ss maxs
        (EQ,isLat) -> maximumsSec l ss (s:maxs)
        (GT,isLat) -> maximumsSec l ss [s]

maxDim :: ProverK loc m => loc -> [Expr] -> TcM m Expr
maxDim l ds = do
    maxs <- maximumsDim l ds []
    case maxs of
        [d] -> return d
        otherwise -> newDimVar False Nothing 

maximumsDim :: ProverK loc m => loc -> [Expr] -> [Expr] -> TcM m [Expr]
maximumsDim l [] maxs = return maxs
maximumsDim l (s:ss) [] = maximumsDim l ss [s]
maximumsDim l (s:ss) maxs@(max:_) = do
    cmp <- tcBlock $ comparesDim l True s max
    case compOrdering cmp of
        (LT,isLat) -> maximumsDim l ss maxs
        (EQ,isLat) -> maximumsDim l ss (s:maxs)
        (GT,isLat) -> maximumsDim l ss [s]

coercesE :: (ProverK loc m) => loc -> Expr -> Type -> TcM m Expr
coercesE l e1 t2 = do
    pp1 <- pp e1
    x2 <- newTypedVar "coerces" t2 False $ Just $ pp1
    tcCstrM_ l $ Coerces e1 x2
    return $ varExpr x2

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coerces l e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(BaseT b2)) = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "base type") pp1 pp2 . Just) $ do
        assignsExprTy l x2 e1
coerces l e1@(loc -> t1@(ComplexT ct1)) x2@(loc -> t2@(ComplexT ct2)) = coercesComplex l e1 x2
coerces l e1@(loc -> t1@(ComplexT c1)) x2@(loc -> t2@(BaseT b2)) = coercesComplex l e1 (updLoc x2 $ ComplexT $ defCType b2)
coerces l e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(ComplexT c2)) = coercesComplex l (updLoc e1 $ ComplexT $ defCType b1) x2
coerces l e1 x2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "type") pp1 pp2 . Just) $ do
        assignsExprTy l x2 e1

coercesComplexE :: (ProverK loc m) => loc -> Expr -> ComplexType -> TcM m Expr
coercesComplexE l e1 ct2 = do
    pp1 <- pp e1
    x2 <- newTypedVar "coerces_complex" (ComplexT ct2) False $ Just $ pp1
    coercesComplex l e1 x2
    return $ varExpr x2

coercesComplex :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesComplex l e1@(loc -> ComplexT t1) x2@(loc -> ComplexT t2) | isVoid t1 || isVoid t2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppExprTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") pp1 pp2 . Just) $ do
        assignsExprTy l x2 e1
coercesComplex l e1@(loc -> ComplexT ct1@(CType s1 t1 d1)) x2@(loc -> ComplexT ct2@(CType s2 t2 d2)) = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") pp1 pp2 . Just) $ do
        tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
        tcCstrM_ l $ CoercesSecDimSizes e1 x2
coercesComplex l e1@(loc -> ComplexT ct1@(CVar v1@(nonTok -> True) _)) x2@(loc -> ComplexT ct2@(CVar v2@(nonTok -> True) _)) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just ct1',Just ct2') -> do
            tcCstrM_ l $ Coerces (updLoc e1 $ ComplexT ct1') (updLoc x2 $ ComplexT ct2')
        (Just ct1',Nothing) -> do
            tcCstrM_ l $ Coerces (updLoc e1 $ ComplexT ct1') x2
        (Nothing,Just ct2') -> do
            tcCstrM_ l $ Coerces e1 (updLoc x2 $ ComplexT ct2')
        (Nothing,Nothing) -> constraintError (\x y err -> Halt $ CoercionException "complex type" x y err) l e1 ppExprTy x2 ppVarTy Nothing
coercesComplex l e1@(loc -> ct1@(ComplexT (CVar v@(nonTok -> True) isNotVoid1))) x2@(loc -> ComplexT ct2) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct1' -> coercesComplex l (updLoc e1 $ ComplexT ct1') x2
        Nothing -> if isNotVoid1 || isNotVoid ct2
            then do
                ct1' <- expandCTypeVar l v
                tcCstrM_ l $ Coerces (updLoc e1 $ ComplexT ct1') x2
            else constraintError (\x y err -> Halt $ CoercionException "complex type" x y err) l e1 ppExprTy x2 ppVarTy Nothing
coercesComplex l e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT (CVar v@(nonTok -> True) isNotVoid2)) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct2' -> coercesComplex l e1 (updLoc x2 $ ComplexT ct2')
        Nothing -> if isNotVoid2 || isNotVoid ct1
            then do
                ct2' <- expandCTypeVar l v
                tcCstrM_ l $ Coerces e1 (updLoc x2 $ ComplexT ct2')
            else  constraintError (\x y err -> Halt $ CoercionException "complex type" x y err) l e1 ppExprTy x2 ppVarTy Nothing
coercesComplex l e1 x2 = constraintError (CoercionException "complex type") l e1 ppExprTy x2 ppVarTy Nothing

cSec :: ComplexType -> Maybe SecType
cSec (CType s _ _) = Just s
cSec ct = Nothing

cSecM :: ProverK loc m => loc -> ComplexType -> TcM m SecType
cSecM l (CType s _ _) = return s
cSecM l (CVar v@(nonTok -> True) _) = resolveCVar l v >>= cSecM l
cSecM l Void = genTcError (locpos l) $ text "no security type for void"

coercesSecDimSizes :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesSecDimSizes l e1@(loc -> ComplexT (CVar v1@(nonTok -> True) _)) x2 = do
    ct1 <- resolveCVar l v1
    coercesSecDimSizes l (updLoc e1 $ ComplexT ct1) x2
coercesSecDimSizes l e1 x2@(loc -> ComplexT (CVar v2@(nonTok -> True) _)) = do
    ct2 <- resolveCVar l v2
    coercesSecDimSizes l e1 (updLoc x2 $ ComplexT ct2)
coercesSecDimSizes l e1@(loc -> ComplexT (CType s1 b1 d1)) x2@(loc -> ComplexT (CType s2 b2 d2)) = do
    let t3 = ComplexT $ CType s1 b2 d2 -- intermediate type
    pp1 <- pp e1
    x3 <- newTypedVar "e" t3 False $ Just $ pp1
--    liftIO $ putStrLn $ "coercesSecDimSizes: " ++ ppr l ++ " " ++ ppr e1 ++ " " ++ ppr x2 ++ " " ++ ppr x3
    coercesDimSizes l e1 x3
    coercesSec l (varExpr x3) x2
coercesSecDimSizes l e1 x2 = constraintError (CoercionException "complex type security dimension") l e1 ppExprTy x2 ppVarTy Nothing

isZeroIdxExpr :: ProverK loc m => loc -> Expr -> TcM m ()
isZeroIdxExpr l e = do
    i <- evaluateIndexExpr l e
    case i of
        0 -> return ()
        otherwise -> genTcError (locpos l) $ text "non-zero index expression"

coercesDimSizes :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesDimSizes l e1@(loc -> ComplexT ct1@(CType s1 b1 d1)) x2@(loc -> ComplexT ct2@(CType s2 b2 d2)) = do
    opts <- askOpts
    mb1 <- tryError $ evaluateIndexExpr l d1
    mb2 <- tryError $ evaluateIndexExpr l d2
    case (mb1,mb2) of
        (_,Right 0) -> assignsExprTy l x2 e1
        (Right ((>0) -> True),_) -> assignsExprTy l x2 e1
        (Right 0,Right ((>0) -> True)) -> if implicitCoercions opts
            then do
                e2 <- repeatExpr l False e1 Nothing ct2
                assignsExprTy l x2 e2
            else assignsExprTy l x2 e1
        (Right 0,_) -> if implicitCoercions opts
            then do
                (ks,fs) <- repeatsCstrs l e1 ct1 x2 d2
                st <- getCstrState
                let choice1 = ([TcK (match (backtrack opts) (IdxT d2) (IdxT $ indexExpr 0)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                let choice2 = ([TcK (NotEqual d2 (indexExpr 0)) st],ks,fs)
                tcCstrM_ l $ MultipleSubstitutions [IdxT d2] [choice1,choice2]
            else assignsExprTy l x2 e1
        (_,Right ((>0) -> True)) -> if implicitCoercions opts
            then do
                (ks,fs) <- repeatsCstrs l e1 ct1 x2 d2
                st <- getCstrState
                let choice1 = ([TcK (match (backtrack opts) (IdxT d1) (IdxT d2)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                let choice2 = ([TcK (match (backtrack opts) (IdxT d1) (IdxT $ indexExpr 0)) st],ks,fs)
                tcCstrM_ l $ MultipleSubstitutions [IdxT d1] [choice1,choice2]
            else assignsExprTy l x2 e1
        otherwise -> if implicitCoercions opts
            then do
                (ks,fs) <- repeatsCstrs l e1 ct1 x2 d2
                st <- getCstrState
                -- 0 --> 0
                let choice1 = ([TcK (match (backtrack opts) (IdxT d1) (IdxT $ indexExpr 0)) st,TcK (match (backtrack opts) (IdxT d2) (IdxT $ indexExpr 0)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                -- 0 --> n
                let choice2 = ([TcK (match (backtrack opts) (IdxT d1) (IdxT $ indexExpr 0)) st,TcK (NotEqual d2 (indexExpr 0)) st],ks,fs)
                -- n --> n
                let choice3 = ([TcK (NotEqual d1 (indexExpr 0)) st,TcK (NotEqual d2 (indexExpr 0)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                tcCstrM_ l $ MultipleSubstitutions [IdxT d1,IdxT d2] [choice1,choice2,choice3]
            else assignsExprTy l x2 e1
coercesDimSizes l e1 x2 = constraintError (CoercionException "complex type dimension") l e1 ppExprTy x2 ppVarTy Nothing

coercesSec :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesSec l e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT t2) = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "security type") pp1 pp2 . Just) $ do
        s2 <- cSecM l t2
        opts <- askOpts
        --if implicitCoercions opts
        --    then do
        coercesSec' l e1 ct1 x2 s2
        --    else assignsExprTy l x2 e1

-- a token security type variable is seen as a private domain
coercesSec' :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> SecType -> TcM m ()
coercesSec' l e1 (cSec -> Just (SVar v1 k1)) x2 (SVar v2 k2) | v1 == v2 = do
    unifiesKind l k1 k2
    assignsExprTy l x2 e1
coercesSec' l e1 (cSec -> Just Public) x2 Public = do
    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@Public) x2 s2@(SVar v PublicK) = do
    unifiesSec l s1 s2
    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@Public) x2 s2@(SVar v@(nonTok -> True) k2) | isPrivateKind k2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2' -> coercesSec' l e1 ct1 x2 s2'
        Nothing -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    (ks,_) <- classifiesCstrs l e1 ct1 x2 s2
                    st <- getCstrState
                    let choice2 = TcK (IsPrivate True (SecT s2)) st
                    mapM_ (tCstrM_ l) (choice2:ks)
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@Public) x2 s2@(SVar v@(nonTok -> True) k2) | not (isPrivateKind k2) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2' -> coercesSec' l e1 ct1 x2 s2'
        Nothing -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    (ks,fs) <- classifiesCstrs l e1 ct1 x2 s2
                    st <- getCstrState
                    let choice1 = ([TcK (IsPublic (backtrack opts) (SecT s2)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                    let choice2 = ([TcK (IsPrivate (backtrack opts) (SecT s2)) st],ks,fs)
                    tcCstrM_ l $ MultipleSubstitutions [SecT s2] [choice1,choice2]
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v _)) x2 s2@(Public) = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1) x2 s2 | isPrivateKind (secTypeKind s1) = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1 PublicK)) x2 s2@(Private d2 k2) = do
    unifiesSec l s1 Public
    coercesSec' l e1 ct1 x2 s2
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1@(nonTok -> True) k1)) x2 s2@(Private d2 k2) | not (isPrivateKind k1) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> do
            let ct1' = setCSec ct1 s1'
            coercesSec' l (updLoc e1 $ ComplexT ct1') ct1' x2 s2
        Nothing -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    (ks,fs) <- classifiesCstrs l e1 ct1 x2 s2
                    st <- getCstrState
                    let choice1 = ([TcK (IsPublic (backtrack opts) (SecT s1)) st],ks,fs)
                    let choice2 = ([TcK (match (backtrack opts) (SecT s1) (SecT s2)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                    tcCstrM_ l $ MultipleSubstitutions [SecT s1] [choice1,choice2]
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1 k1)) x2 s2@(SVar v2 k2) | v1 == v2 = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1@(nonTok -> True) k1)) x2 s2@(SVar v2@(nonTok -> True) k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just s1',Just s2') -> do
            let ct1' = setCSec ct1 s1'
            coercesSec' l (updLoc e1 $ ComplexT ct1') ct1' x2 s2'
        (Just s1',Nothing) -> do
            let ct1' = setCSec ct1 s1'
            coercesSec' l (updLoc e1 $ ComplexT ct1') ct1' x2 s2
        (Nothing,Just s2') -> coercesSec' l e1 ct1 x2 s2'
        (Nothing,Nothing) -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    (ks,fs) <- classifiesCstrs l e1 ct1 x2 s2
                    st <- getCstrState
                    -- public --> public
                    let choice1 = ([TcK (IsPublic (backtrack opts) (SecT s1)) st,TcK (IsPublic (backtrack opts) (SecT s2)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                    -- public --> private
                    let choice2 = ([TcK (IsPublic (backtrack opts) (SecT s1)) st,TcK (IsPrivate (backtrack opts) (SecT s2)) st],ks,fs)
                    -- private --> private
                    let choice3 = ([TcK (IsPrivate (backtrack opts) (SecT s1)) st,TcK (IsPrivate (backtrack opts) (SecT s2)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                    tcCstrM_ l $ MultipleSubstitutions [SecT s1,SecT s2] [choice1,choice2,choice3]
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just Public) x2 s2@(Private d2 k2) = do
    opts <- askOpts
    if implicitCoercions opts
        then do
            (ks,_) <- classifiesCstrs l e1 ct1 x2 s2
            forM_ ks $ tCstrM_ l
        else constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing
coercesSec' l e1 (cSec -> Just (SVar v1@(nonTok -> False) k1)) x2 s2 = do
    unifiesKind l k1 $ secTypeKind s2
    assignsExprTy l x2 e1
coercesSec' l e1 ct1@(cSec -> Just Public) x2 s2@(SVar v2@(nonTok -> False) k2) = do
    opts <- askOpts
    if implicitCoercions opts
        then do
            (ks,_) <- classifiesCstrs l e1 ct1 x2 s2
            forM_ ks $ tCstrM_ l
        else constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1@(nonTok -> True) k1)) x2 s2@(SVar v2@(nonTok -> False) k2) | not (isPrivateKind k1) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> do
            let ct1' = setCSec ct1 s1'
            coercesSec' l (updLoc e1 $ ComplexT ct1') ct1' x2 s2
        Nothing -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    (ks,fs) <- classifiesCstrs l e1 ct1 x2 s2
                    st <- getCstrState
                    let choice1 = ([TcK (IsPublic (backtrack opts) (SecT s1)) st],ks,fs)
                    let choice2 = ([TcK (match (backtrack opts) (SecT s1) (SecT s2)) st],[TcK (Unifies (loc x2) (loc e1)) st,TcK (Assigns (IdxT $ varExpr x2) (IdxT e1)) st],Set.empty)
                    tcCstrM_ l $ MultipleSubstitutions [SecT s1] [choice1,choice2]
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    assignsExprTy l x2 e1
coercesSec' l e1 t1 x2 t2 = constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing

classifiesCstrs :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> SecType -> TcM m ([TCstr],Set VarIdentifier)
classifiesCstrs l e1 ct1 x2 s2 = do
    st <- getCstrState
    let ct2 = setCSec ct1 s2
    dec@(DVar dv) <- newDecVar False Nothing
    let classify' = ProcedureName (DecT dec) $ mkVarId "classify"
    ppe1 <- pp e1
    v1@(VarName _ (VIden vn1)) <- newTypedVar "cl" (loc e1) False $ Just $ ppe1
    let k1 = TcK (PDec (PIden $ procedureNameId classify') Nothing [(e1,False)] (ComplexT ct2) dec False [v1]) st
    let k2 = TcK (Unifies (loc x2) (ComplexT ct2)) st
    let k3 = TcK (Assigns (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) (bimap PIden id classify') Nothing [(e1,False)])) st
    return ([k1,k2,k3],Set.fromList [dv,vn1])

repeatsCstrs :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> Expr -> TcM m ([TCstr],Set VarIdentifier)
repeatsCstrs l e1 ct1 x2 d2 = do
    st <- getCstrState
    let ct2 = setCBase ct1 d2
    dec@(DVar dv) <- newDecVar False Nothing
    let repeat' = ProcedureName (DecT dec) $ mkVarId "repeat"
    ppe1 <- pp e1
    v1@(VarName _ (VIden vn1)) <- newTypedVar "rp" (loc e1) False $ Just $ ppe1
    let k1 = TcK (PDec (PIden $ procedureNameId repeat') Nothing [(e1,False)] (ComplexT ct2) dec False [v1]) st
    let k2 = TcK (Unifies (loc x2) (ComplexT ct2)) st
    let k3 = TcK (Assigns (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) (bimap PIden id repeat') Nothing [(e1,False)])) st
    return ([k1,k2,k3],Set.fromList [dv,vn1])

coercesLit :: (ProverK loc m) => loc -> Expr -> TcM m ()
coercesLit l e@(LitPExpr t lit) = do
    b <- typeToBaseType l t
    coercesLitBase l (funit lit) b
coercesLit l (ArrayConstructorPExpr (ComplexT ct@(CType s t d)) es) = do
    -- coerce each element
    let et = ComplexT $ CType s t $ indexExpr 0
    xs <- forM (zip [1..] es) $ \(i,e) -> pp e >>= \ppe -> newTypedVar ("ael"++show i) et False $ Just $ ppe
    tcCstrM_ l $ CoercesN (zip es xs)
    -- match the array's dimension
    tcCstrM_ l $ Unifies (IdxT d) (IdxT $ indexExpr 1) -- dimension 1
coercesLit l (MultisetConstructorPExpr (ComplexT ct@(CType s (MSet b) d)) es) = do
    -- coerce each element
    let et = ComplexT $ CType s b $ indexExpr 0
    xs <- forM (zip [1..] es) $ \(i,e) -> pp e >>= \ppe -> newTypedVar ("mel"++show i) et False $ Just $ ppe
    tcCstrM_ l $ CoercesN (zip es xs)
    -- match the array's dimension
    tcCstrM_ l $ Unifies (IdxT d) (IdxT $ indexExpr 0) -- dimension 0
coercesLit l e = constraintError (CoercionException "literal") l e pp (loc e) pp Nothing  

equalsLit :: (ProverK loc m) => loc -> Literal () -> Literal () -> TcM m ()
equalsLit l lit1 lit2 | lit1 == lit2 = return ()
equalsLit l (IntLit _ i1) (IntLit _ i2) | i1 == i2 = return ()
equalsLit l (IntLit _ i1) (FloatLit _ f2) | fromInteger i1 == f2 = return ()
equalsLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
equalsLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
equalsLit l lit1 lit2 = constraintError (EqualityException "literal type") l lit1 pp lit2 pp Nothing  

-- coerces a literal into a base type
coercesLitBase :: (ProverK loc m) => loc -> Literal () -> BaseType -> TcM m ()
coercesLitBase l lit t2@(BVar v@(nonTok -> True)) = do
    mb <- tryResolveBVar l v
    case mb of
       Just t2' -> coercesLitBase l lit t2'
       Nothing -> do
           b <- case lit of
                StringLit _ s -> return $ TyPrim $ DatatypeString ()
                BoolLit _ b -> return $ TyPrim $ DatatypeBool ()
                otherwise -> constraintError (\x y e -> Halt $ CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
           addSubstM l (SubstMode CheckS True) (tyToVar $ BaseT t2) (BaseT b)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primIntBounds -> Just (min,max)))) = do
    unless (min <= i && i <= max) $ do
        ppt <- pp t
        tcWarn (locpos l) $ LiteralOutOfRange (show i) (ppt) (show min) (show max)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primFloatBounds -> Just (min,max)))) = do
    unless (min <= fromInteger i && fromInteger i <= max) $ do
        ppt <- pp t
        tcWarn (locpos l) $ LiteralOutOfRange (show i) (ppt) (show min) (show max)
coercesLitBase l (FloatLit _ f) (TyPrim (t@(primFloatBounds -> Just (min,max)))) | isPrimFloat t = do
    unless (min <= f && f <= max) $ do
        ppt <- pp t
        tcWarn (locpos l) $ LiteralOutOfRange (show f) (ppt) (show min) (show max)
coercesLitBase l (BoolLit _ b) (TyPrim (DatatypeBool _)) = return ()
coercesLitBase l (StringLit _ s) (TyPrim (DatatypeString _)) = return ()
coercesLitBase l l1 t2 = constraintError (CoercionException "literal base type") l l1 pp t2 pp Nothing  

decToken :: MonadIO m => TcM m DecType
decToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "dtok" (Just mn) (Just i) True Nothing
    return $ DVar v

kindToken :: MonadIO m => TcM m KindType
kindToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "ktok" (Just mn) (Just i) True Nothing
    return $ KVar v False

secToken :: MonadIO m => TcM m SecType
secToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "stok" (Just mn) (Just i) True Nothing
    k <- newKindVar "k" False False Nothing
    return $ SVar v k
    
baseToken :: MonadIO m => TcM m BaseType
baseToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "btok" (Just mn) (Just i) True Nothing
    return $ BVar v

arrayToken :: MonadIO m => Type -> Expr -> TcM m VArrayType
arrayToken b sz = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "atok" (Just mn) (Just i) True Nothing
    return $ VAVar v b sz

complexToken :: MonadIO m => TcM m ComplexType
complexToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "ctok" (Just mn) (Just i) True Nothing
    return $ CVar v False

exprToken :: MonadIO m => TcM m Expr
exprToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "etok" (Just mn) (Just i) True Nothing
    let t = BaseT $ BVar v
    return $ RVariablePExpr t (VarName t $ VIden v)

-- | Checks if a type is more specific than another, performing substitutions
compares :: (ProverK loc m) => loc -> Bool -> Type -> Type -> TcM m (Comparison (TcM m))
compares l isLattice (IdxT e1) (IdxT e2) = comparesExpr l True e1 e2
compares l isLattice (BaseT b1) (BaseT b2) = do
    comparesBase l isLattice b1 b2
compares l isLattice (ComplexT c1) (ComplexT c2) = do
    comparesComplex l isLattice c1 c2
compares l isLattice (BaseT b1) (ComplexT c2) = do
    comparesComplex l isLattice (defCType b1) c2
compares l isLattice (ComplexT c1) (BaseT b2) = do
    comparesComplex l isLattice c1 (defCType b2)
compares l isLattice (SecT s1) (SecT s2) = do
    comparesSec l isLattice s1 s2
compares l isLattice (KindT k1) (KindT k2) = do
    comparesKind l isLattice k1 k2
compares l isLattice (SysT t1) (SysT t2) = do
    comparesSys l isLattice t1 t2
compares l isLattice (DecT d1) (DecT d2) = do
    comparesDec l d1 d2
compares l isLattice (VArrayT a1) (VArrayT a2) = do
    comparesArray l isLattice a1 a2
compares l isLattice (VAType b1 sz1) (VAType b2 sz2) = do
    o1 <- compares l isLattice b1 b2
    o2 <- compares l isLattice (IdxT sz1) (IdxT sz2)
    appendComparisons l [o1,o2]
--compares l (CondType t1 c1) (CondType t2 c2) = do
--    o1 <- compares l t1 t2
--    o2 <- comparesCondExpression l c1 c2
--    return $ o1 `mappend` o2
--compares l (CondType t1 c1) t2 = do
--    o1 <- compares l t1 t2
--    o2 <- comparesCondExpression l c1 trueExpr
--    return $ o1 `mappend` o2
--compares l t1 (CondType t2 c2) = do
--    o1 <- compares l t1 t2
--    o2 <- comparesCondExpression l trueExpr c2
--    return $ o1 `mappend` o2
compares l isLattice t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (ComparisonException "type") (pp1) (pp2) . Just)
        (equals l t1 t2 >> return (Comparison t1 t2 EQ EQ))

comparesDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m (Comparison (TcM m))
comparesDec l t1@(DVar v1@(nonTok -> True)) t2@(DVar v2@(nonTok -> True)) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- decToken
            addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t1) $ DecT x
            addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t2) $ DecT x
            return (Comparison t1 t2 EQ EQ)
        (Just t1',Nothing) -> comparesDec l t1' t2
        (Nothing,Just t2') -> comparesDec l t1 t2'
        (Just t1',Just t2') -> comparesDec l t1' t2'        
comparesDec l t1 t2@(DVar v@(nonTok -> True)) = do
    mb <- tryResolveDVar l v
    case mb of
        Just t2 -> comparesDec l t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t2) $ DecT t1
            return (Comparison t1 t2 LT EQ)
comparesDec l t1@(DVar v@(nonTok -> True)) t2 = do
    mb <- tryResolveDVar l v
    case mb of
        Just t1 -> comparesDec l t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t1) $ DecT t2
            return (Comparison t1 t2 GT EQ)
comparesDec l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (ComparisonException "declaration type") (pp1) (pp2) . Just)
        (equalsDec l t1 t2 >> return (Comparison t1 t2 EQ EQ))

comparesArray :: (ProverK loc m) => loc -> Bool -> VArrayType -> VArrayType -> TcM m (Comparison (TcM m))
comparesArray l isLattice a1@(VAVal ts1 _) a2@(VAVal ts2 _) = do
    comparesList l isLattice ts1 ts2
comparesArray l isLattice a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) | v1 == v2 = return (Comparison a1 a2 EQ EQ)
comparesArray l isLattice a1@(VAVar v1@(nonTok -> True) b1 sz1) a2@(VAVar v2@(nonTok -> True) b2 sz2) = do
    mb1 <- tryResolveVAVar l v1 sz1
    mb2 <- tryResolveVAVar l v2 sz2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- arrayToken b1 sz1
            addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a1) $ VArrayT x
            addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a2) $ VArrayT x
            return $ Comparison a1 a2 EQ EQ
        (Just a1',Nothing) -> comparesArray l isLattice a1' a2
        (Nothing,Just a2') -> comparesArray l isLattice a1 a2'
        (Just a1',Just a2') -> comparesArray l isLattice a1' a2'        
comparesArray l isLattice a1 a2@(VAVar v2@(nonTok -> True) b2 sz2) = do
    mb <- tryResolveVAVar l v2 sz2
    case mb of
        Just a2 -> comparesArray l isLattice a1 a2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a2) $ VArrayT a2
            return $ Comparison a1 a2 LT EQ
comparesArray l isLattice a1@(VAVar v1@(nonTok -> True) b1 sz1) a2 = do
    mb <- tryResolveVAVar l v1 sz1
    case mb of
        Just t1 -> comparesArray l isLattice a1 a2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a1) $ VArrayT a2
            return $ Comparison a1 a2 GT EQ
--comparesArray l a1 a2 = constraintError (ComparisonException "array type") l a1 pp a2 pp Nothing

comparesSec :: (ProverK loc m) => loc -> Bool -> SecType -> SecType -> TcM m (Comparison (TcM m))
comparesSec l isLattice t1@Public t2@Public = return (Comparison t1 t2 EQ EQ)
comparesSec l isLattice t1@(Private d1 k1) t2@(Private d2 k2) | d1 == d2 && k1 == k2 = do
    return (Comparison t1 t2 EQ EQ)
comparesSec l True t1@Public t2@(Private {}) = return (Comparison t1 t2 EQ LT) -- public computations are preferrable (because of coercions)
comparesSec l True t1@(Private {}) t2@Public = return (Comparison t1 t2 EQ GT) -- public computations are preferrable (because of coercions)
comparesSec l isLattice t1@(SVar v1 k1) t2@(SVar v2 k2) | v1 == v2 = do
    equalsKind l k1 k2
    return (Comparison t1 t2 EQ EQ)
comparesSec l isLattice t1@(SVar v1@(nonTok -> True) k1) t2@(SVar v2@(nonTok -> True) k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            cmpk <- comparesKind l isLattice k1 k2 >>= compOrderingM l
            case cmpk of
                LT -> return $ Comparison t1 t2 EQ LT
                GT -> return $ Comparison t1 t2 EQ GT
                EQ -> do
                    x <- secToken
                    addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t1) $ SecT x
                    addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t2) $ SecT x
                    return $ Comparison t1 t2 EQ EQ
        (Just t1',Nothing) -> comparesSec l isLattice t1' t2
        (Nothing,Just t2') -> comparesSec l isLattice t1 t2'
        (Just t1',Just t2') -> comparesSec l isLattice t1' t2'        
comparesSec l isLattice t1 t2@(SVar v@(nonTok -> True) _) = do
    mb <- tryResolveSVar l v
    case mb of
        Just t2 -> comparesSec l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t2) $ SecT t1
            return $ Comparison t1 t2 EQ LT
comparesSec l isLattice t1@(SVar v@(nonTok -> True) _) t2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just t1 -> comparesSec l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t1) $ SecT t2
            return $ Comparison t1 t2 EQ GT
comparesSec l isLattice t1 t2 = constraintError (ComparisonException $ show isLattice ++ " security type") l t1 pp t2 pp Nothing

comparesKind :: (ProverK loc m) => loc -> Bool -> KindType -> KindType -> TcM m (Comparison (TcM m))
comparesKind l isLattice t1@PublicK t2@PublicK = return (Comparison t1 t2 EQ EQ)
comparesKind l isLattice t1@(PrivateK k1) t2@(PrivateK k2) | k1 == k2 = return (Comparison t1 t2 EQ EQ)
comparesKind l True t1@PublicK t2@(PrivateK {}) = return (Comparison t1 t2 EQ LT) -- public computations are preferrable (because of coercions)
comparesKind l True t1@(PrivateK {}) t2@PublicK = return (Comparison t1 t2 EQ GT) -- public computations are preferrable (because of coercions)
comparesKind l isLattice t1@(KVar k1 priv1) t2@(KVar k2 priv2) | k1 == k2 = return (Comparison t1 t2 EQ EQ)
comparesKind l isLattice t1@(KVar v1@(nonTok -> True) priv1) t2@(KVar v2@(nonTok -> True) priv2) = do
    mb1 <- tryResolveKVar l v1
    mb2 <- tryResolveKVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- kindToken
            addSubstM l (SubstMode CheckS False) (VarName (KType priv1) $ VIden v1) $ KindT x
            addSubstM l (SubstMode CheckS False) (VarName (KType priv2) $ VIden v2) $ KindT x
            return $ Comparison t1 t2 EQ EQ
        (Just t1',Nothing) -> comparesKind l isLattice t1' t2
        (Nothing,Just t2') -> comparesKind l isLattice t1 t2'
        (Just t1',Just t2') -> comparesKind l isLattice t1' t2'        
comparesKind l isLattice t1 t2@(KVar v@(nonTok -> True) priv) = do
    mb <- tryResolveKVar l v
    case mb of
        Just t2 -> comparesKind l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (VarName (KType priv) $ VIden v) $ KindT t1
            return $ Comparison t1 t2 EQ LT
comparesKind l isLattice t1@(KVar v@(nonTok -> True) priv) t2 = do
    mb <- tryResolveKVar l v
    case mb of
        Just t1 -> comparesKind l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (VarName (KType priv) $ VIden v) $ KindT t2
            return $ Comparison t1 t2 EQ GT
comparesKind l isLattice t1 t2 = constraintError (ComparisonException "kind type") l t1 pp t2 pp Nothing

comparesSys :: (ProverK loc m) => loc -> Bool -> SysType -> SysType -> TcM m (Comparison (TcM m))
comparesSys l isLattice (SysPush t1) (SysPush t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice (SysRet t1) (SysRet t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice (SysRef t1) (SysRef t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice (SysCRef t1) (SysCRef t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice t1 t2 = constraintError (ComparisonException "syscall type") l t1 pp t2 pp Nothing

comparesBase :: (ProverK loc m) => loc -> Bool -> BaseType -> BaseType -> TcM m (Comparison (TcM m))
comparesBase l isLattice t1@(TApp (TIden n1) ts1 d1) t2@(TApp (TIden n2) ts2 d2) = do
    equalsTIdentifier l (TIden n1) (TIden n2)
    comparesTpltArgs l isLattice ts1 ts2
    --comparesDec l d1 d2
comparesBase l isLattice t1@(TyPrim p1) t2@(TyPrim p2) = equalsPrim l p1 p2 >> return (Comparison t1 t2 EQ EQ)
comparesBase l isLattice t1@(MSet b1) t2@(MSet b2) = comparesBase l isLattice b1 b2
comparesBase l isLattice t1@(BVar v1) t2@(BVar v2) | v1 == v2 = return (Comparison t1 t2 EQ EQ)
comparesBase l isLattice t1@(BVar v1@(nonTok -> True)) t2@(BVar v2@(nonTok -> True)) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- baseToken
            addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t1) $ BaseT x
            addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t2) $ BaseT x
            return $ Comparison t1 t2 EQ EQ
        (Just t1',Nothing) -> comparesBase l isLattice t1' t2
        (Nothing,Just t2') -> comparesBase l isLattice t1 t2'
        (Just t1',Just t2') -> comparesBase l isLattice t1' t2'        
comparesBase l isLattice t1 t2@(BVar v@(nonTok -> True)) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> comparesBase l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t2) $ BaseT t1
            return $ Comparison t1 t2 LT EQ
comparesBase l isLattice t1@(BVar v@(nonTok -> True)) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> comparesBase l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t1) $ BaseT t2
            return $ Comparison t1 t2 GT EQ
comparesBase l isLattice t1 t2 = constraintError (ComparisonException "base type") l t1 pp t2 pp Nothing

comparesComplex :: (ProverK loc m) => loc -> Bool -> ComplexType -> ComplexType -> TcM m (Comparison (TcM m))
comparesComplex l isLattice t1@Void t2@Void = return $ Comparison t1 t2 EQ EQ
comparesComplex l isLattice ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = do -- we don't compare sizes
    o1 <- comparesSec l isLattice s1 s2
    o2 <- comparesBase l isLattice t1 t2
    o3 <- comparesDim l isLattice d1 d2
    appendComparisons l [o1,o2,o3]
comparesComplex l isLattice t1@(CVar v1 _) t2@(CVar v2 _) | v1 == v2 = return (Comparison t1 t2 EQ EQ)
comparesComplex l isLattice t1@(CVar v1@(nonTok -> True) _) t2@(CVar v2@(nonTok -> True) _) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- complexToken
            addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t1) $ ComplexT x
            addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t2) $ ComplexT x
            return $ Comparison t1 t2 EQ EQ
        (Just t1',Nothing) -> comparesComplex l isLattice t1' t2
        (Nothing,Just t2') -> comparesComplex l isLattice t1 t2'
        (Just t1',Just t2') -> comparesComplex l isLattice t1' t2'        
comparesComplex l isLattice t1 t2@(CVar v@(nonTok -> True) _) = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2 -> comparesComplex l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t2) $ ComplexT t1
            return $ Comparison t1 t2 LT EQ
comparesComplex l isLattice t1@(CVar v@(nonTok -> True) _) t2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1 -> comparesComplex l isLattice t1 t2
        Nothing -> do
            addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t1) $ ComplexT t2
            return $ Comparison t1 t2 GT EQ
comparesComplex l isLattice t1 t2 = constraintError (ComparisonException "complex type") l t1 pp t2 pp Nothing
    
comparesFoldable :: (ProverK loc m,Foldable t) => loc -> Bool -> t Type -> t Type -> TcM m (Comparison (TcM m))
comparesFoldable l isLattice xs ys = comparesList l isLattice (toList xs) (toList ys)

data Comparison m where
    Comparison :: VarsG m a => a -> a -> Ordering -> Ordering -> Comparison m
  deriving (Typeable)
    
instance Typeable m => Data (Comparison m) where
    gfoldl k z (Comparison x y o b) = z Comparison `k` x `k` y `k` o `k` b
    gunfold k z c = error "gunfold Comparison"
    toConstr (Comparison {}) = con_Comparison
    dataTypeOf _ = ty_Comparison

con_Comparison = mkConstr ty_Comparison "Comparison" [] Prefix
ty_Comparison   = mkDataType "Language.SecreC.TypeChecker.Constraint.Comparison" [con_Comparison]
    
instance Eq (Comparison m) where
    (Comparison x1 y1 o1 b1) == (Comparison x2 y2 o2 b2) = o1 == o2 && b1 == b2
instance Ord (Comparison m) where
    compare (Comparison _ _ o1 b1) (Comparison _ _ o2 b2) = compare o1 o2 `mappend` compare b1 b2
        
deriving instance Show (Comparison m)

instance Monad m => PP m (Comparison m) where
    pp (Comparison x y o b) = do
        ppx <- pp x
        ppo <- pp o
        ppb <- pp b
        ppy <- pp y
        return $ ppx <+> ppo <+> ppb <+> ppy
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m,Typeable m) => Vars GIdentifier m (Comparison m) where
    traverseVars f (Comparison x y o b) = do
        x' <- f x
        y' <- f y
        o' <- f o
        b' <- f b
        return $ Comparison x' y' o' b'

compOrdering :: Comparison m -> (Ordering,Ordering)
compOrdering (Comparison _ _ o b) = (o,b)
compOrderingM :: ProverK loc m => loc -> Comparison (TcM m) -> TcM m Ordering
compOrderingM l (Comparison _ _ o b) = appendOrdering l o b
ppCompares x y o = ppid x <+> ppid o <+> ppid y

comparesList :: (ProverK loc m) => loc -> Bool -> [Type] -> [Type] -> TcM m (Comparison (TcM m))
comparesList l isLattice a@[] b@[] = return $ Comparison a b EQ EQ
comparesList l isLattice a@(x:xs) b@(y:ys) = do
    f <- compares l isLattice x y
    g <- comparesList l isLattice xs ys
    appendComparison l f g
comparesList l isLattice xs ys = constraintError (ComparisonException "type") l xs pp ys pp Nothing
    
appendComparison :: (ProverK loc m) => loc -> Comparison (TcM m) -> Comparison (TcM m) -> TcM m (Comparison (TcM m))
appendComparison l c1@(Comparison x1 x2 o1 b1) c2@(Comparison y1 y2 o2 b2) = do
    o' <- appendOrdering l o1 o2
    b' <- appendOrdering l b1 b2
    appendOrdering l o' b'
    return $ Comparison y1 y2 o' b'

appendOrdering :: ProverK loc m => loc -> Ordering -> Ordering -> TcM m Ordering
appendOrdering l EQ y = return y
appendOrdering l x EQ = return x
appendOrdering l LT LT = return LT
appendOrdering l GT GT = return GT
appendOrdering l x y = constraintError (ComparisonException "comparison") l x pp y pp Nothing

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM m)] -> TcM m (Comparison (TcM m))
appendComparisons l xs = foldr0M (Comparison () () EQ EQ) (appendComparison l) xs

assigns :: ProverK loc m => loc -> Type -> Type -> TcM m ()
assigns l (IdxT (RVariablePExpr _ v1)) (IdxT e2) = assignsExpr l v1 e2
assigns l (SecT (SVar v1 k1)) (SecT s2) = assignsSec l v1 k1 s2
assigns l (BaseT (BVar v1)) (BaseT b2) = assignsBase l v1 b2
assigns l (ComplexT (CVar v1 _)) (ComplexT ct2) = assignsComplex l v1 ct2
assigns l (ComplexT (CVar v1 _)) (BaseT b2) = assignsComplex l v1 (defCType b2)
assigns l (DecT (DVar v1)) (DecT d2) = assignsDec l v1 d2
assigns l (VArrayT (VAVar v1 b1 sz1)) (VArrayT a2) = assignsArray l v1 b1 sz1 a2
assigns l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    tcError (locpos l) $ UnificationException "type assignment" (pp1) (pp2) Nothing

unifiesN :: ProverK loc m => loc -> [Type] -> TcM m ()
unifiesN l ts = foldr0M_ (\t1 t2 -> tcCstrM_ l (Unifies t1 t2) >> return t2) ts

-- | Non-directed unification, without implicit security coercions.
-- applies substitutions
unifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()
unifies l (KindT k1) (KindT k2) = unifiesKind l k1 k2
unifies l (IdxT e1) (IdxT e2) = unifiesExpr l True e1 e2
unifies l (SecT s1) (SecT s2) = unifiesSec l s1 s2
unifies l (SysT s1) (SysT s2) = unifiesSys l s1 s2
unifies l (BaseT b1) (BaseT b2) = unifiesBase l b1 b2
unifies l (BaseT b1) (ComplexT c2) = unifiesComplex l (defCType b1) c2
unifies l (ComplexT c1) (BaseT b2) = unifiesComplex l c1 (defCType b2)
unifies l (ComplexT c1) (ComplexT c2) = unifiesComplex l c1 c2
unifies l (DecT d1) (DecT d2) = unifiesDec l d1 d2
unifies l (VArrayT a1) (VArrayT a2) = unifiesArray l a1 a2
unifies l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM_ l $ Unifies b1 b2
    unifiesExprTy l True sz1 sz2
unifies l t1@(CondType t1' c1) t2@(CondType t2' c2) = do
    unifies l t1' t2'
    unifiesCondExpression l c1 c2
unifies l t1@(CondType t1' c1) t2 = do
    unifies l t1' t2
    unifiesCondExpression l c1 trueExpr
unifies l t1 t2@(CondType t2' c2) = do
    unifies l t1 t2'
    unifiesCondExpression l trueExpr c2
unifies l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "type") (pp1) (pp2) . Just)
        (equals l t1 t2)

assignsArray :: ProverK loc m => loc -> VarIdentifier -> Type -> Expr -> VArrayType -> TcM m ()
assignsArray l v1@(nonTok -> True) b1 sz1 a2 = do
    unifiesExprTy l True sz1 (vArraySize a2)
    mb1 <- tryResolveVAVar l v1 sz1
    case mb1 of
        Nothing -> addSubstM l (SubstMode NoFailS True) (VarName (VAType b1 sz1) $ VIden v1) (VArrayT a2)
        Just a1' -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2)

unifiesArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m ()
unifiesArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    unifiesList l ts1 ts2
    tcCstrM_ l $ Unifies b1 b2
unifiesArray l a1@(VAVar v1@(nonTok -> True) b1 sz1) a2@(VAVar v2@(nonTok -> True) b2 sz2) = do
    tcCstrM_ l $ Unifies b1 b2
    unifiesExprTy l True sz1 sz2
    mb1 <- tryResolveVAVar l v1 sz1
    mb2 <- tryResolveVAVar l v2 sz2
    case (mb1,mb2) of
        (Just a1',Just a2') -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2')
        (Just a1',Nothing) -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2)
        (Nothing,Just a2') -> tcCstrM_ l $ Unifies (VArrayT a1) (VArrayT a2')
        (Nothing,Nothing) -> do
            o <- chooseVar l v1 v2
            case o of
                GT -> addSubstM l (SubstMode CheckS True) (VarName (VAType b1 sz1) $ VIden v1) (VArrayT a2) 
                otherwise -> addSubstM l (SubstMode CheckS True) (VarName (VAType b2 sz2) $ VIden v2) (VArrayT a1)
unifiesArray l a1@(VAVar v1@(nonTok -> True) b1 sz1) a2 = do
    unifiesExprTy l True sz1 (vArraySize a2)
    mb1 <- tryResolveVAVar l v1 sz1
    case mb1 of
        Just a1' -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName (VAType b1 sz1) $ VIden v1) (VArrayT a2)
unifiesArray l a1 a2@(VAVar v2@(nonTok -> True) b2 sz2) = do
    unifiesExprTy l True (vArraySize a1) (vArraySize a2)
    mb2 <- tryResolveVAVar l v2 sz2
    case mb2 of
        Just a2' -> tcCstrM_ l $ Unifies (VArrayT a1) (VArrayT a2')
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName (VAType b2 sz2) $ VIden v2) (VArrayT a1)
unifiesArray l a1 a2 = do
    pp1 <- pp a1
    pp2 <- pp a2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "array") (pp1) (pp2) . Just)
        (equalsArray l a1 a2)

assignsDec :: ProverK loc m => loc -> VarIdentifier -> DecType -> TcM m ()
assignsDec l v1@(nonTok -> True) d2 = do
    mb1 <- tryResolveDVar l v1
    case mb1 of
        Nothing -> addSubstM l (SubstMode NoFailS True) (VarName DType $ VIden v1) (DecT d2)
        Just d1' -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2)

unifiesDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m ()
unifiesDec l d1@(DVar v1@(nonTok -> True)) d2@(DVar v2@(nonTok -> True)) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (DecT d1) (DecT d2')
        (Nothing,Nothing) -> do
            o <- chooseVar l v1 v2
            case o of
                GT -> addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v2) (DecT d1)
                otherwise -> addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v1) (DecT d2)
unifiesDec l d1@(DVar v1@(nonTok -> True)) d2 = do
    mb <- tryResolveDVar l v1
    case mb of
        Just d1' -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v1) (DecT d2)
unifiesDec l d1 (DVar v2@(nonTok -> True)) = do
    mb <- tryResolveDVar l v2
    case mb of
        Just d2' -> tcCstrM_ l $ Unifies (DecT d1) (DecT d2')
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v2) (DecT d1)
unifiesDec l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "declaration type") (pp1) (pp2) . Just)
        (equalsDec l t1 t2)

assignsComplex :: ProverK loc m => loc -> VarIdentifier -> ComplexType -> TcM m ()
assignsComplex l v1@(nonTok -> True) d2 = do
    mb1 <- tryResolveCVar l v1
    case mb1 of
        Nothing -> addSubstM l (SubstMode NoFailS True) (VarName (TType $ isNotVoid d2) $ VIden v1) (ComplexT d2)
        Just d1' -> tcCstrM_ l $ Unifies (ComplexT d1') (ComplexT d2)

unifiesComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m ()
unifiesComplex l Void Void = return ()
unifiesComplex l ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = do
    pp1 <- pp ct1
    pp2 <- pp ct2
    addErrorM l (TypecheckerError (locpos l) . (UnificationException "complex") (pp1) (pp2) . Just) $ do
        tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        unifiesExprTy l True d1 d2
unifiesComplex l d1@(CVar v1@(nonTok -> True) isNotVoid1) d2@(CVar v2@(nonTok -> True) isNotVoid2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (ComplexT d1') (ComplexT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (ComplexT d1') (ComplexT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (ComplexT d1) (ComplexT d2')
        (Nothing,Nothing) -> do
            o <- chooseVar l v1 v2
            case o of
                GT -> addSubstM l (SubstMode CheckS True) (VarName (TType $ isNotVoid1 || isNotVoid2) $ VIden v2) (ComplexT d1)
                otherwise -> addSubstM l (SubstMode CheckS True) (VarName (TType $ isNotVoid1 || isNotVoid2) $ VIden v1) (ComplexT d2)
unifiesComplex l (CVar v@(nonTok -> True) isNotVoid1) c2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just c1 -> tcCstrM_ l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName (TType $ isNotVoid1 || isNotVoid c2) $ VIden v) (ComplexT c2)
unifiesComplex l c1 (CVar v@(nonTok -> True) isNotVoid2) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> tcCstrM_ l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName (TType $ isNotVoid2 || isNotVoid c1) $ VIden v) (ComplexT c1)
unifiesComplex l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "complex type") (pp1) (pp2) . Just)
        (equalsComplex l t1 t2)

unifiesSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()
unifiesSec l Public Public = return ()
unifiesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = do
    return ()
unifiesSec l d1@(SVar v1@(nonTok -> True) k1) d2@(SVar v2@(nonTok -> True) k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (SecT d1') (SecT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (SecT d1') (SecT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (SecT d1) (SecT d2')
        (Nothing,Nothing) -> do
            tcCstrM_ l $ Unifies (KindT k1) (KindT k2)
            o <- chooseVar l v1 v2
            case o of
                LT -> addSVarSubstM l CheckS v1 d2
                GT -> addSVarSubstM l CheckS v2 d1
                EQ -> addSVarSubstM l CheckS v1 d2 
unifiesSec l (SVar v@(nonTok -> True) k) s2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just s1 -> tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        Nothing -> do
            tcCstrM_ l $ Unifies (KindT k) (KindT $ secTypeKind s2)
            addSVarSubstM l CheckS v s2
unifiesSec l s1 (SVar v@(nonTok -> True) k) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        Nothing -> do
            tcCstrM_ l $ Unifies (KindT $ secTypeKind s1) (KindT k)
            addSVarSubstM l CheckS v s1
unifiesSec l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "security type") (pp1) (pp2) . Just)
        (equalsSec l t1 t2)

addSVarSubstM l mode v s = addSubstM l (SubstMode mode True) (VarName (KindT $ secTypeKind s) $ VIden v) (SecT s)

unifiesKind :: ProverK loc m => loc -> KindType -> KindType -> TcM m ()
unifiesKind l PublicK PublicK = return ()
unifiesKind l (PrivateK k1) (PrivateK k2) | k1 == k2 = return ()
unifiesKind l k1@(KVar v1@(nonTok -> True) priv1) k2@(KVar v2@(nonTok -> True) priv2) = do
    let priv = max priv1 priv2
    mb1 <- tryResolveKVar l v1
    mb2 <- tryResolveKVar l v2
    case (mb1,mb2) of
        (Just k1',Just k2') -> tcCstrM_ l $ Unifies (KindT k1') (KindT k2')
        (Nothing,Just k2') -> tcCstrM_ l $ Unifies (KindT k1) (KindT k2')
        (Just k1',Nothing) -> tcCstrM_ l $ Unifies (KindT k1') (KindT k2)
        (Nothing,Nothing) -> case compare priv1 priv2 of
            LT -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v1) (KindT k2)
            GT -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v2) (KindT k1)
            EQ -> do
                o <- chooseVar l v1 v2
                case o of
                    GT -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v2) (KindT k1)
                    otherwise -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v1) (KindT k2)
unifiesKind l (KVar v1@(nonTok -> True) priv1) k2 = do
    let priv2 = isPrivateKind k2
    let priv = max priv1 priv2
    mb1 <- tryResolveKVar l v1
    case mb1 of
        Just k1 -> tcCstrM_ l $ Unifies (KindT k1) (KindT k2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v1) (KindT k2)
unifiesKind l k1 (KVar v2@(nonTok -> True) priv2) = do
    let priv1 = isPrivateKind k1
    let priv = max priv1 priv2
    mb2 <- tryResolveKVar l v2
    case mb2 of
        Just k2 -> tcCstrM_ l $ Unifies (KindT k1) (KindT k2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v2) (KindT k1)
unifiesKind l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "kind type") (pp1) (pp2) . Just)
        (equalsKind l t1 t2)

assignsSec :: ProverK loc m => loc -> VarIdentifier -> KindType -> SecType -> TcM m ()
assignsSec l v1@(nonTok -> True) k1 s2 = do
    mb1 <- tryResolveSVar l v1
    case mb1 of
        Nothing ->  addSVarSubstM l NoFailS v1 s2
        Just s1' -> tcCstrM_ l $ Unifies (SecT s1') (SecT s2)

unifiesSys :: (ProverK loc m) => loc -> SysType -> SysType -> TcM m ()
unifiesSys l (SysPush t1) (SysPush t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRet t1) (SysRet t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRef t1) (SysRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysCRef t1) (SysCRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "system type") (pp1) (pp2) . Just)
        (equalsSys l t1 t2)

assignsBase :: ProverK loc m => loc -> VarIdentifier -> BaseType -> TcM m ()
assignsBase l v1@(nonTok -> True) d2 = do
    mb1 <- tryResolveBVar l v1
    case mb1 of
        Nothing -> addSubstM l (SubstMode NoFailS True) (VarName BType $ VIden v1) (BaseT d2)
        Just d1' -> tcCstrM_ l $ Unifies (BaseT d1') (BaseT d2)

unifiesBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m ()
unifiesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
unifiesBase l (MSet b1) (MSet b2) = unifiesBase l b1 b2
unifiesBase l d1@(BVar v1@(nonTok -> True)) d2@(BVar v2@(nonTok -> True)) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (BaseT d1') (BaseT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (BaseT d1') (BaseT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (BaseT d1) (BaseT d2')
        (Nothing,Nothing) -> do
            o <- chooseVar l v1 v2
            case o of
                GT -> addSubstM l (SubstMode CheckS True) (VarName BType $ VIden v2) (BaseT d1)
                otherwise -> addSubstM l (SubstMode CheckS True) (VarName BType $ VIden v1) (BaseT d2)
unifiesBase l (BVar v@(nonTok -> True)) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName BType $ VIden v) (BaseT t2)
unifiesBase l t1 (BVar v@(nonTok -> True)) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (SubstMode CheckS True) (VarName BType $ VIden v) (BaseT t1)
unifiesBase l (TApp (TIden n1) ts1 d1) (TApp (TIden n2) ts2 d2) = do
    unifiesTIdentifier l (TIden n1) (TIden n2)
    unifiesTpltArgs l ts1 ts2
    --unifiesDec l d1 d2
unifiesBase l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "base type") (pp1) (pp2) . Just)
        (equalsBase l t1 t2)

unifiesTpltArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
unifiesTpltArgs l ts1 ts2 = do
    matchTpltArgs l UnificationException (\x y -> tcCstrM_ l $ Unifies x y) ts1 ts2
    return ()

equalsTpltArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
equalsTpltArgs l ts1 ts2 = do
    matchTpltArgs l EqualityException (\x y -> tcCstrM_ l $ Equals x y) ts1 ts2
    return ()

matchTpltArgs :: (ProverK loc m) => loc -> (String -> Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> (Type -> Type -> TcM m r) -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m [r]
matchTpltArgs l ex match ts1 ts2 = do
    pp1 <- pp ts1
    pp2 <- pp ts2
    addErrorM l (TypecheckerError (locpos l) . (ex "template arguments") (pp1) (pp2) . Just) $ matchTpltArgs' ts1 ts2
  where
    matchTpltArgs' ts1@(all (not . snd) -> True) [(t2,True)] = do
        let tt = tyOf t2
        b <- typeBase l tt
        r <- match t2 (VArrayT $ VAVal (map fst ts1) b)
        return [r]
    matchTpltArgs' [(t1,True)] ts2@(all (not . snd) -> True) = do
        let tt = tyOf t1
        b <- typeBase l tt
        r <- match t1 (VArrayT $ VAVal (map fst ts2) b)
        return [r]
    matchTpltArgs' [(t1,True)] [(t2,True)] = do
        r <- match t1 t2
        return [r]
    matchTpltArgs' ts1 ts2 = do
        ts1' <- concatMapM (expandVariadicType l) ts1
        ts2' <- concatMapM (expandVariadicType l) ts2
        constraintList (ex "template arguments") match l ts1' ts2'

equalsSizes :: (ProverK loc m) => loc -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
equalsSizes l szs1 szs2 = matchSizes l EqualityException (equalsExprTy l False) szs1 szs2

unifiesSizes :: (ProverK loc m) => loc -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
unifiesSizes l szs1 szs2 = matchSizes l UnificationException (unifiesExprTy l False) szs1 szs2

matchSizes :: (ProverK loc m) => loc -> (String -> Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> (Expr -> Expr -> TcM m ()) -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
matchSizes l ex match szs1 szs2 = do
    pp1 <- (ppOpt szs1 pp)
    pp2 <- (ppOpt szs2 pp)
    addErrorM l (TypecheckerError (locpos l) . (ex "sizes") pp1 pp2 . Just) $ matchSizes' szs1 szs2
  where
    matchSizes' (Just szs1@(all (not . snd) -> True)) (Just [(e2,True)]) = do
        match e2 (ArrayConstructorPExpr (loc e2) $ map fst szs1)
    matchSizes' (Just [(e1,True)]) (Just szs2@(all (not . snd) -> True)) = do
        match e1 (ArrayConstructorPExpr (loc e1) $ map fst szs2)
    matchSizes' (Just [(e1,True)]) (Just [(e2,True)]) = do
        match e1 e2
    matchSizes' (Just szs1) (Just szs2) = do
        szs1' <- concatMapM (expandVariadicExpr l False) szs1
        szs2' <- concatMapM (expandVariadicExpr l False) szs2
        constraintList (ex "sizes") match l szs1' szs2'
        return ()
    matchSizes' sz1 sz2 = return () -- ignore if both sizes are not known

expandVariadicExpr :: (ProverK loc m) => loc -> IsConst -> (Expr,IsVariadic) -> TcM m [Expr]
expandVariadicExpr l isConst (e,False) = case loc e of
    VAType {} -> do
        ppe <- pp e
        genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (ppe)
    VArrayT {} -> do
        ppe <- pp e
        genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (ppe)
    otherwise -> return [e]
expandVariadicExpr l isConst (ArrayConstructorPExpr t es,True) = case t of
    VAType {} -> return es
    VArrayT {} -> return es
    otherwise -> do
        ppt <- pp t
        genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (ppt)
expandVariadicExpr l isConst (e,True) = do
    let t = loc e
    case t of
        VAType b sz -> if isConst
            then do
                sz' <- evaluateIndexExpr l sz
                vs <- forM [0..pred (fromEnum sz')] $ \i -> newTypedVar ("vex"++show i) b False Nothing
                let evs = map varExpr vs
                tcCstrM_ l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t evs)
                return evs
            else do
                ArrayConstructorPExpr t' es' <- expandArrayExpr l e
                return es'
        VArrayT a -> if isConst
            then do
                ts <- expandVariadicType l (VArrayT a,True)
                vs <- forM ts $ \t -> newTypedVar "vext" t False Nothing
                let es = map varExpr vs
                tcCstrM_ l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t es)
                return es
            else do
                ArrayConstructorPExpr t' es' <- expandArrayExpr l e
                return es'
        otherwise -> do
            ppt <- pp t
            genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (ppt)
    
expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM m [Type]
expandVariadicType l (t,False) = case tyOf t of
    VAType {} -> do
        ppt <- pp t
        genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (ppt)
    otherwise -> return [t]
expandVariadicType l (VArrayT (VAVal ts _),True) = return ts
expandVariadicType l (t@(VArrayT a),True) = do
    let tt = tyOf t
    sz <- evaluateIndexExpr l =<< typeSize l tt
    b <- typeBase l tt
    vs <- forM [0..pred (fromEnum sz)] $ \i -> newVarOf ("varr"++show i) b False Nothing
    tcCstrM_ l $ Unifies t (VArrayT $ VAVal vs b)
    return vs
expandVariadicType l (t,True) = do
    ppt <- pp t
    genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (ppt)

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM_ l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError (UnificationException "type") l xs pp ys pp Nothing

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType
resolveCVar l v = resolveTVar l v >>= typeToComplexType l

resolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m SecType
resolveSVar l v = resolveTVar l v >>= typeToSecType l

resolveKVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m KindType
resolveKVar l v = resolveTVar l v >>= typeToKindType l

resolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Expr -> TcM m VArrayType
resolveVAVar l v sz = resolveTVar l v >>= \t -> typeToVArrayType l t sz

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m DecType
resolveDVar l v = resolveTVar l v >>= typeToDecType l

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m BaseType
resolveBVar l v = resolveTVar l v >>= typeToBaseType l

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable (ppv)
        Just t -> return t

tryResolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe SecType)
tryResolveSVar l v = tryResolveTVar l v >>= mapM (typeToSecType l)

tryResolveKVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe KindType)
tryResolveKVar l v = tryResolveTVar l v >>= mapM (typeToKindType l)

tryResolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Expr -> TcM m (Maybe VArrayType)
tryResolveVAVar l v sz = tryResolveTVar l v >>= mapM (\t -> typeToVArrayType l t sz)

tryResolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe BaseType)
tryResolveBVar l v = tryResolveTVar l v >>= mapM (typeToBaseType l)

tryResolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe ComplexType)
tryResolveCVar l v = tryResolveTVar l v >>= mapM (typeToComplexType l)

tryResolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe DecType)
tryResolveDVar l v = tryResolveTVar l v >>= mapM (typeToDecType l)

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe Type)
tryResolveTVar l v | varIdTok v = return Nothing
tryResolveTVar l v = do
--    liftIO $ putStrLn $ "resolvingTVar " ++ ppr v
    addGDependencies $ VIden v
    -- lookup in the substitution environment
    s <- getTSubsts l
    mb <- substsFromMap (Map.mapKeys VIden $ unTSubsts s) (VIden v::GIdentifier)
    return $ mb

-- | tries to resolve an expression
tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM m (Maybe (Expression GIdentifier (Typed loc)))
tryResolveEVar l v t | varIdTok v = return Nothing
tryResolveEVar l v t = do
--    liftIO $ putStrLn $ "resolvingEVar " ++ ppr v
    addGDependencies $ VIden v
    ss <- getTSubsts l
    case Map.lookup v (unTSubsts ss) of
        Just (IdxT e) -> do
            tcCstrM_ l $ Unifies t (loc e)
            return $ Just (fmap (Typed l) e)
        Just a@(VArrayT (VAVal (unIdxs -> Just es) _)) -> do
            tcCstrM_ l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ ArrayConstructorPExpr (tyOf a) es
        Just a@(VArrayT (VAVar v _ _)) -> do
            tcCstrM_ l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ RVariablePExpr (tyOf a) (VarName (tyOf a) $ VIden v)
        otherwise -> return Nothing

unIdx :: Type -> Maybe Expr
unIdx (IdxT e) = Just e
unIdx _ = Nothing

unIdxs :: [Type] -> Maybe [Expr]
unIdxs [] = Just []
unIdxs (x:xs) = case (unIdx x,unIdxs xs) of
    (Just x,Just xs) -> Just (x:xs)
    otherwise -> Nothing

setCSec (CType _ t d) s = CType s t d
setCBase (CType s t _) d = CType s t d

isSupportedPrint :: (ProverK loc m) => loc -> [(Expr,IsVariadic)] -> [Var] -> TcM m ()
isSupportedPrint l es xs = forM_ (zip es xs) $ \(e,x) -> do
    (dec,[(y,_)]) <- pDecCstrM l False True (PIden $ mkVarId "tostring") Nothing [e] (BaseT string)
    assignsExprTy l x y
    return ()

unifiesCondExpression :: (ProverK loc m) => loc -> Cond -> Cond -> TcM m ()
unifiesCondExpression l e1 e2 = unifiesExprTy l False e1 e2 `mplus` satisfiesCondExpressions l [e1,e2]

satisfiesCondExpressions :: (ProverK loc m) => loc -> [Cond] -> TcM m ()
satisfiesCondExpressions l is = do
    cs <- prove l "satisfiesCondExpressions" $ mapM (expr2IExpr . fmap (Typed l)) is
    isValid l $ iAnd cs

assignsExpr :: ProverK loc m => loc -> Var -> Expr -> TcM m ()
assignsExpr l v1@(VarName _ (VIden n1@(nonTok -> True))) e2 = do
    --liftIO $ putStrLn $ "assignsExpr " ++ ppr l ++ " " ++ ppr v1 ++ " " ++ ppr e2
    mb <- tryResolveEVar l n1 (loc v1)
    case mb of
        Nothing -> addValueM l (SubstMode NoFailS True) v1 e2
        Just e1' -> do
            pp2 <- pp e2
            pp1 <- pp v1
            pp1' <- pp e1'
            genTcError (locpos l) $ text "cannot assign expression" <+> pp2 <+> text "to bound variable" <+> pp1 <+> text "=" <+> pp1'

unifiesExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
unifiesExpr l doStatic e1@(RVariablePExpr t1 v1@(VarName _ (VIden n1@(nonTok -> True)))) e2@(RVariablePExpr t2 v2@(VarName _ (VIden n2@(nonTok -> True)))) = do
    mb1 <- tryResolveEVar l n1 t1
    mb2 <- tryResolveEVar l n2 t2
    case (mb1,mb2) of
        (Just e1',Just e2') -> unifiesExpr l doStatic (fmap typed e1') (fmap typed e2')
        (Just e1',Nothing) -> unifiesExpr l doStatic (fmap typed e1') e2
        (Nothing,Just e2') -> unifiesExpr l doStatic e1 (fmap typed e2')
        (Nothing,Nothing) -> do
            o <- chooseVar l n1 n2
            case o of
                GT -> addValueM l (SubstMode CheckS True) v2 e1
                otherwise -> addValueM l (SubstMode CheckS True) v1 e2
unifiesExpr l doStatic e1@(RVariablePExpr t1 v1@(VarName _ (VIden n1@(nonTok -> True)))) e2 = do
    mb <- tryResolveEVar l n1 t1
    case mb of
        Nothing -> addValueM l (SubstMode CheckS True) v1 e2
        Just e1' -> unifiesExpr l doStatic (fmap typed e1') e2
unifiesExpr l doStatic e1 e2@(RVariablePExpr t2 v2@(VarName _ (VIden n2@(nonTok -> True)))) = do
    mb <- tryResolveEVar l n2 t2
    case mb of
        Nothing -> addValueM l (SubstMode CheckS True) v2 e1
        Just e2' -> unifiesExpr l doStatic e1 (fmap typed e2')
unifiesExpr l doStatic e1@(PostIndexExpr {}) e2 = do
    e1' <- projectExpr l e1
    unifiesExpr l doStatic e1' e2
unifiesExpr l doStatic e1 e2@(PostIndexExpr {}) = do
    e2' <- projectExpr l e2
    unifiesExpr l doStatic e1 e2'
unifiesExpr l doStatic (ArrayConstructorPExpr t1 es1) (ArrayConstructorPExpr t2 es2) = do
    constraintList (UnificationException "expression") (unifiesExprTy l doStatic) l es1 es2
    return ()
unifiesExpr l doStatic e1@(ArrayConstructorPExpr {}) e2 = do
    e2' <- expandArrayExpr l e2
    unifiesExpr l doStatic e1 e2'
unifiesExpr l doStatic e1 e2@(ArrayConstructorPExpr {}) = do
    e1' <- expandArrayExpr l e1
    unifiesExpr l doStatic e1' e2
unifiesExpr l doStatic e1 e2 = do
    pp1 <- pp e1
    pp2 <- pp e2
    addErrorM l (TypecheckerError (locpos l) . (UnificationException "expression") (pp1) (pp2) . Just) $ equalsExpr l doStatic e1 e2

projectExpr :: ProverK loc m => loc -> Expr -> TcM m Expr
projectExpr l (PostIndexExpr t e s) = do
    arr' <- expandArrayExpr l e
    projectArrayExpr l arr' (Foldable.toList s)

projectArrayExpr :: ProverK loc m => loc -> Expr -> [Index GIdentifier Type] -> TcM m Expr
projectArrayExpr l e [] = return e
projectArrayExpr l (ArrayConstructorPExpr t es) (IndexInt _ ie:s) = do
    i <- liftM fromEnum $ evaluateIndexExpr l ie
    checkIdx l i es
    projectArrayExpr l (es !! i) s
projectArrayExpr l (ArrayConstructorPExpr t es) (IndexSlice _ il iu:s) = do
    il' <- liftM fromEnum $ evaluateIndexExpr l $ maybe (indexExpr $ toEnum 0) id il
    iu' <- liftM fromEnum $ evaluateIndexExpr l $ maybe (indexExpr $ toEnum $ length es) id iu
    checkIdx l il' es
    checkIdx l iu' es
    projectArrayExpr l (ArrayConstructorPExpr (chgArraySize (length es) t) $ drop il' $ take iu' es) s

checkIdx :: ProverK loc m => loc -> Int -> [a] -> TcM m ()
checkIdx l i xs = unless (i >= 0 && i <= length xs) $ do
    genTcError (locpos l) $ text "failed to evaluate projection"

chgArraySize :: Int -> Type -> Type
chgArraySize sz (VAType b _) = VAType b (indexExpr $ toEnum sz)
chgArraySize sz t = t

expandArrayExpr :: ProverK loc m => loc -> Expr -> TcM m Expr
expandArrayExpr l e = do
    let t = loc e
    b <- typeBase l t
    sz <- evaluateIndexExpr l =<< typeSize l t
    es <- forM [0..pred (fromEnum sz)] $ \i -> do
        let w = indexExpr $ toEnum i
        return $ PostIndexExpr b e $ WrapNe $ IndexInt (loc w) w
    return $ ArrayConstructorPExpr t es

equalsTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()
equalsTIdentifier l (OIden (OpCast _ t1)) (OIden (OpCast _ t2)) = do
    equals l (castTypeToType t1) (castTypeToType t2)
equalsTIdentifier l (OIden op1) (OIden op2) | funit op1 == funit op2 = return ()
equalsTIdentifier l n1 n2 | n1 == n2 = return ()
equalsTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing
    
unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()
unifiesTIdentifier l (OIden (OpCast _ t1)) (OIden (OpCast _ t2)) = do
    unifies l (castTypeToType t1) (castTypeToType t2)
unifiesTIdentifier l (OIden op1) (OIden op2) | funit op1 == funit op2 = return ()
unifiesTIdentifier l n1 n2 | n1 == n2 = return ()
unifiesTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing

equalsExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
equalsExpr l doStatic e1 e2 | e1 == e2 = return ()
equalsExpr l doStatic (LitPExpr t1 lit1) (LitPExpr t2 lit2) = do
    equalsLit l (funit lit1) (funit lit2)
    tcCstrM_ l $ Unifies t1 t2
equalsExpr l True e1 e2 = do
    pp1 <- ppr e1
    pp2 <- ppr e2
    i1 <- prove l ("equalsExpr1 " ++ pp1) $ expr2IExpr $ fmap (Typed l) e1
    i2 <- prove l ("equalsExpr2 " ++ pp2) $ expr2IExpr $ fmap (Typed l) e2
    isValid l (IBinOp (IEq) i1 i2)
equalsExpr l False e1 e2 = do
    eq <- eqExprs l False e1 e2
    opts <- askOpts
    when (checkAssertions opts) $ getDeps >>= \deps -> checkCstrM_ l deps $ CheckAssertion eq

comparesTpltArgs :: (ProverK loc m)
    => loc -> Bool -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m (Comparison (TcM m))
comparesTpltArgs l isLattice ts1 ts2 = do
    os <- constraintList (ComparisonException "template arguments") comparesTpltArg l ts1 ts2
    appendComparisons l os
  where
    comparesTpltArg (t1,b1) (t2,b2) = do
        unless (b1 == b2) $ genTcError (locpos l) $ text "incomparable template arguments"
        compares l isLattice t1 t2

comparesDim :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
comparesDim l True e1 e2 = do
    z1 <- tryError $ equalsExpr l True e1 (indexExpr 0)
    z2 <- tryError $ equalsExpr l True e2 (indexExpr 0)
    case (z1,z2) of
        (Right _,Right _) -> return (Comparison e1 e2 EQ EQ)
        (Right _,Left _) -> return (Comparison e1 e2 EQ LT)
        (Left _,Right _) -> return (Comparison e1 e2 EQ GT)
        otherwise -> comparesExpr l True e1 e2
comparesDim l False e1 e2 = liftM swapComp $ comparesExpr l True e1 e2
    
swapComp :: Comparison m -> Comparison m
swapComp (Comparison x y o b) = Comparison x y b o
    
comparesExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
comparesExpr l doStatic e1 e2 = do
    pp1 <- pp e1
    pp2 <- pp e2
    addErrorM l (TypecheckerError (locpos l) . (ComparisonException "expression") (pp1) (pp2) . Just) (comparesExpr' l doStatic e1 e2)
  where
    comparesExpr' :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
    comparesExpr' l doStatic e1 e2 | e1 == e2 = return (Comparison e1 e2 EQ EQ)
    comparesExpr' l doStatic e1@(RVariablePExpr t1 v1@(VarName _ (VIden n1@(nonTok -> True)))) e2@(RVariablePExpr t2 v2@(VarName _ (VIden n2@(nonTok -> True)))) = do
        mb1 <- tryResolveEVar l n1 t1
        mb2 <- tryResolveEVar l n2 t2
        case (mb1,mb2) of
            (Nothing,Nothing) -> do
                x <- exprToken
                addValueM l (SubstMode NoCheckS False) v1 x
                addValueM l (SubstMode NoCheckS False) v2 x
                return (Comparison e1 e2 EQ EQ)
            (Just e1',Nothing) -> comparesExpr' l doStatic (fmap typed e1') e2
            (Nothing,Just e2') -> comparesExpr' l doStatic e1 (fmap typed e2')
            (Just e1',Just e2') -> comparesExpr' l doStatic (fmap typed e1') (fmap typed e2')
    comparesExpr' l doStatic e1@(RVariablePExpr t1 v1@(VarName _ (VIden n1@(nonTok -> True)))) e2 = do
        mb <- tryResolveEVar l n1 t1
        case mb of
            Nothing -> do
                addValueM l (SubstMode NoCheckS False) v1 e2
                return (Comparison e1 e2 GT EQ)
            Just e1' -> comparesExpr' l doStatic (fmap typed e1') e2
    comparesExpr' l doStatic e1 e2@(RVariablePExpr t2 v2@(VarName _ (VIden n2@(nonTok -> True)))) = do
        mb <- tryResolveEVar l n2 t2
        case mb of
            Nothing -> do
                addValueM l (SubstMode NoCheckS False) v2 e1
                return (Comparison e1 e2 LT EQ)
            Just e2' -> comparesExpr' l doStatic e1 (fmap typed e2')
    comparesExpr' l doStatic e1 e2 = do
        equalsExpr l doStatic e1 e2 >> return (Comparison e1 e2 EQ EQ)

equalsExprTy :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
equalsExprTy l doStatic e1 e2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppExprTy e2)
    addErrorM l (TypecheckerError (locpos l) . (EqualityException "typed expression") pp1 pp2 . Just) $ do
        equalsExpr l doStatic e1 e2
        tcCstrM_ l $ Equals (loc e1) (loc e2)

unifiesExprTy :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
unifiesExprTy l doStatic e1 e2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppExprTy e2)
    addErrorM l (TypecheckerError (locpos l) . (UnificationException "typed expression") pp1 pp2 . Just) $ do
        tcCstrM_ l $ Unifies (loc e1) (loc e2)
        unifiesExpr l doStatic e1 e2

assignsExprTys :: (ProverK loc m) => loc -> [(Expr,Var)] -> TcM m ()
assignsExprTys l exs = forM_ exs $ \(e,x) -> assignsExprTy l x e

assignsExprTy :: (ProverK loc m) => loc -> Var -> Expr -> TcM m ()
assignsExprTy l v1 e2 = do
    pp1 <- (ppExprTy v1)
    pp2 <- (ppExprTy e2)
    addErrorM l (TypecheckerError (locpos l) . (UnificationException "assign typed expression") pp1 pp2 . Just) $ do
        tcCstrM_ l $ Unifies (loc v1) (loc e2)
        assignsExpr l v1 e2
    
constraintError :: (ProverK loc m,VarsG (TcM m) a,VarsG (TcM m) b) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> TcM m Doc) -> b -> (b -> TcM m Doc) -> Maybe SecrecError -> TcM m res
constraintError k l e1 pp1 e2 pp2 (Just suberr) = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    p1 <- pp1 e1'
    p2 <- pp2 e2'
    tcError (locpos l) $ k p1 p2 $ Just suberr
constraintError k l e1 pp1 e2 pp2 Nothing = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    p1 <- pp1 e1'
    p2 <- pp2 e2'
    tcError (locpos l) $ k p1 p2 Nothing

constraintList :: (ProverK loc m,VarsG (TcM m) [a],VarsG (TcM m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM m x) -> loc -> [a] -> [b] -> TcM m [x]
constraintList err f l [] [] = return []
constraintList err f l (x:xs) (y:ys) = do
    r <- f x y
    rs <- constraintList err f l xs ys
    return (r:rs)
constraintList err f l xs ys = constraintError err l xs pp ys pp Nothing

checkAssertion :: (ProverK loc m) => loc -> Expr -> TcM m ()
checkAssertion l e = do
    ic <- prove l "checkassertion" $ expr2IExpr $ fmap (Typed l) e
    isValid l ic
    
checkEqual :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
checkEqual l e1 e2 = do
    (i1,i2) <- prove l "checkequal" $ do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return (i1,i2)
    isValid l $ IBinOp (IEq) i1 i2

checkIndex :: (ProverK loc m,SMTK loc) => loc -> Expr -> TcM m ()
checkIndex l e = do
    ie <- prove l "checkindex" $ expr2IExpr $ fmap (Typed l) e
    isValid l $ IBinOp (ILeq) (ILit $ IUint64 0) ie

pDecCstrM :: (ProverK loc m) => loc -> Bool -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expr,IsVariadic)] -> Type -> TcM m (DecType,[(Expr,IsVariadic)])
pDecCstrM l isTop doCoerce pid targs es tret = do
    dec <- newDecVar False Nothing
    opts <- askOpts
    let tck = if isTop then topTcCstrM_ else tcCstrM_
    if (doCoerce && implicitCoercions opts)
        then do
            xs <- forM es $ \e -> do
                tx <- newTyVar True False Nothing
                ppe <- ppVariadicArg pp e
                x <- newTypedVar "parg" tx False $ Just ppe
                return x
            tck l $ PDec pid targs es tret dec True xs
            let es' = zip (map varExpr xs) (map snd es)
            return (dec,es')
        else do
            xs <- forM es $ \e -> do
                let tx = loc $ fst e
                ppe <- ppVariadicArg pp e
                x <- newTypedVar "parg" tx False $ Just $ ppe
                return x
            tck l $ PDec pid targs es tret dec False xs
            return (dec,es)


match :: Bool -> Type -> Type -> TcCstr
match True x y = Unifies x y
match False x y = Equals x y

