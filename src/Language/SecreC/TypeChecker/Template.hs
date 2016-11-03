{-# LANGUAGE TupleSections, ImpredicativeTypes, Rank2Types, ViewPatterns, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Monad
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

import Data.List as List
import Data.Typeable
import Data.Either
import Data.Maybe
import Data.Unique
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set(..))
import Data.Map (Map(..))
import Data.Foldable as Foldable
import Data.Graph.Inductive.Graph as Graph
import Data.Generics hiding (GT)

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Control.Monad.State as State
import Control.Monad.State (StateT(..))

import Text.PrettyPrint as PP

instance (MonadIO m) => Vars GIdentifier (TcM m) [(Bool,Var,IsVariadic)] where
    traverseVars f = mapM f

instance (MonadIO m) => Vars GIdentifier (TcM m) [(IsConst,Either Expr Type,IsVariadic)] where
    traverseVars f = mapM f
    
--instance PP m VarIdentifier => PP m [(IsConst,Either Expr Type,IsVariadic)] where
--    pp xs = do
--        let f (z,x,y) = liftM (ppConst z) (ppVariadicArg pp (x,y))
--        liftM (sepBy comma) (mapM f xs)

instance PP m VarIdentifier => PP m [Either Expr Type] where
    pp xs = liftM (sepBy comma) (mapM pp xs)
    
instance (MonadIO m) => Vars GIdentifier (TcM m) [(Constrained Type,IsVariadic)] where
    traverseVars f = mapM f

instance PP m VarIdentifier => PP m [(Bool,Var,IsVariadic)] where
    pp = ppVariadicPArgs pp

ppVariadicPArgs :: Monad m => (a -> m Doc) -> [(IsConst,a,IsVariadic)] -> m Doc
ppVariadicPArgs pp xs = do
    let f (x,y,z) = do
        ppyz <- ppVariadicArg pp (y,z)
        return $ ppConst x ppyz
    liftM (sepBy comma) (mapM f xs)

instance PP m VarIdentifier => PP m [(Constrained Type,IsVariadic)] where
    pp = liftM (sepBy comma) . mapM (\(y,z) -> ppVariadicArg pp (y,z))

instance PP m VarIdentifier => PP m [(Expr,Var)] where
    pp xs = do
        let f (e,v) = do
            ppe <- ppExprTy e
            ppv <- ppVarTy v
            return $ ppe <+> text "~~>" <+> ppv
        liftM (sepBy comma) (mapM f xs)
    
instance PP m VarIdentifier => PP m [(Var,IsVariadic)] where
    pp = liftM (sepBy comma) . mapM (\(y,z) -> ppVariadicArg pp (y,z))

-- the most specific entries are preferred
sortEntries :: [EntryEnv] -> [EntryEnv]
sortEntries = sortBy sortDec
    where
    sortDec :: EntryEnv -> EntryEnv -> Ordering
    sortDec (EntryEnv _ d1) (EntryEnv _ d2) = maybe EQ id $ comparesDecIds True d1 d2

decLineage :: DecType -> [ModuleTyVarId]
decLineage (DecType i isRec _ _ _ _ _) = i : recs
    where
    recs = case isRec of
            DecTypeOriginal -> []
            DecTypeRec j -> [j]
            DecTypeCtx -> []

-- if ambiguous, discard recursive entries outside of the lineage
discardRecursiveEntries :: ProverK loc m => loc -> [EntryInst] -> TcM m [EntryInst]
discardRecursiveEntries l [] = return []
discardRecursiveEntries l [e] = return [e]
discardRecursiveEntries l es = filterM (discardRecursiveEntry l) es

discardRecursiveEntry :: ProverK loc m => loc -> EntryInst -> TcM m Bool
discardRecursiveEntry l (e,e',_,_,_,_,_) = do
    case decTypeK (unDecT $ entryType e) of
        DecTypeRec i -> do
            lin <- getLineage
            return $ List.elem i $ map snd lin
        otherwise -> return True

-- Procedure arguments are maybe provided with index expressions
-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (ProverK loc m) => loc -> Maybe [EntryEnv] -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m [EntryEnv] -> TcM m DecType
matchTemplate l oldentries kid n targs pargs ret check = do
    entries <- maybe (liftM sortEntries check) return oldentries
    opts <- askOpts
    st <- getCstrState
    let isLattice = checkCoercion (implicitCoercions opts) st
    debugTc $ do
        ppentries <- mapM (pp . entryType) entries
        liftIO $ putStrLn $ "matches " ++ show (vcat $ ppentries)
    def <- ppTpltAppM l n targs pargs ret
    (instances,_) <- instantiateTemplateEntries Set.empty l def isLattice kid n targs pargs ret entries
    let oks = rights instances
    let errs = lefts instances
    (insts0,ko) <- compMins (compareTemplateDecls def l isLattice n) [] False oks
    insts <- discardRecursiveEntries l insts0
    case insts of
        [] -> do
            defs <- forM errs $ \(e,err) -> do
                t' <- ppM l $ entryType e
                return (locpos $ entryLoc e,t',err)
            isAnn <- getAnn
            isLeak <- getLeak
            kind <- getKind
            tcError (locpos l) $ Halt $ NoMatchingTemplateOrProcedure (ppid isAnn <+> ppid isLeak <+> ppid kind <+> def) defs
        [inst] -> liftM fst $ resolveTemplateEntry False l kid n targs pargs ret inst
        -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
        otherwise -> do
            debugTc $ do
                ppkid <- ppr kid
                let ppes = show $ map (\(e,_,_,_,_,_,_) -> pprid $ decTypeTyVarId $ unDecT $ entryType e) insts
                liftIO $ putStrLn $ "matchTemplate ambiguous entries" ++ ppkid ++ " " ++ ppes
            if isNothing oldentries
                then do
                    dec <- newDecVar False Nothing
                    let insts' = map entryInstOld insts
                    case n of
                        PIden n -> tcCstrM_ l $ PDec ko (Just insts') (PIden n) targs (concat pargs) (fromJust ret) dec
                        OIden n -> tcCstrM_ l $ PDec ko (Just insts') (OIden n) targs (concat pargs) (fromJust ret) dec
                        TIden n -> tcCstrM_ l $ TDec ko (Just insts') (TIden n) (concat targs) dec
                    return dec
                else do
                    dec <- resolveTemplateEntries l kid n targs pargs ret insts ko
                    debugTc $ do
                        n <- State.gets (length . tDict)
                        ppkid <- ppr kid
                        ppdec <- ppr dec
                        ppn <- ppr n
                        liftIO $ putStrLn $ "matchedTemplate " ++ ppkid ++ " " ++ ppdec ++ " " ++ ppn
                    return dec

-- sort the templates, filtering out greater templates that do not rely on coercions
compMins :: Monad m => (a -> a -> m (Ordering,Ordering,Bool)) -> [a] -> Bool -> [a] -> m ([a],Bool)
compMins cmp mins acc [] = return (mins,acc)
compMins cmp [] acc [x] = return ([x],acc)
compMins cmp [] acc (a:b:xs) = do
    (o,is,ko) <- cmp a b
    case (o,is,ko) of
        (EQ,EQ,ko) -> compMins cmp [a,b] (acc || ko) xs -- keep both
        (EQ,LT,ko) -> compMins cmp [a,b] (acc || ko) xs -- keep both
        (EQ,GT,ko) -> compMins cmp [b,a] (acc || ko) xs -- keep both
        (LT,EQ,ko) -> compMins cmp [a] acc xs -- keep first
        (LT,LT,True) -> compMins cmp [a,b] True xs -- keep botj
        (LT,LT,False) -> compMins cmp [a] acc xs -- keep first
        (GT,EQ,ko) -> compMins cmp [b] ko xs -- keep second
        (GT,GT,True) -> compMins cmp [b,a] True xs -- keep both
        (GT,GT,False) -> compMins cmp [b] ko xs -- keep second
compMins cmp (min:mins) acc (x:xs) = do
    (o,is,ko) <- cmp x min
    case (o,is,ko) of
        (EQ,EQ,ko) -> compMins cmp (x:min:mins) (acc || ko) xs
        (EQ,LT,ko) -> compMins cmp (x:min:mins) (acc || ko) xs
        (EQ,GT,ko) -> insertByM compMin x mins >>= \mins' -> compMins cmp (min:mins') (acc || ko) xs
        (LT,EQ,ko) -> compMins cmp [x] (acc || ko) xs
        (LT,LT,True) -> compMins cmp (x:min:mins) True xs
        (LT,LT,False) -> compMins cmp [x] acc xs
        (GT,EQ,ko) -> compMins cmp (min:mins) (acc || ko) xs
        (GT,GT,True) -> insertByM compMin x mins >>= \mins' -> compMins cmp (min:mins') (acc || ko) xs
        (GT,GT,False) -> compMins cmp (min:mins) acc xs
  where compMin x y = liftM (\(x,y,b) -> mappend x y) (cmp x y)

type EntryInst = (EntryEnv,EntryEnv,TDict,TDict,Frees,Frees,CstrCache)

entryInstOld :: EntryInst -> EntryEnv
entryInstOld (e,_,_,_,_,_,_) = e

discardMatchingEntry :: ProverK Position m => EntryInst -> TcM m ()
discardMatchingEntry (e,e',dict,_,frees,_,_) = delFrees "discardMatchingEntry" frees

mkInvocationDec :: ProverK loc m => loc -> DecType -> [(Type,IsVariadic)] -> TcM m DecType
mkInvocationDec l dec@(DecType j (DecTypeRec i) targs hdict bdict specs d) targs' = return dec
mkInvocationDec l dec@(DecType j DecTypeCtx targs hdict bdict specs d) targs' = return dec
mkInvocationDec l dec@(DecType i DecTypeOriginal targs hdict bdict specs d) targs' = do
    j <- newModuleTyVarId
    ts' <- concatMapM (expandVariadicType l) targs'
    let specs' = map (,False) ts'
    return $ DecType j (DecTypeRec i) [] hdict bdict specs' d

resolveTemplateEntries :: (ProverK loc m) => loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> [EntryInst] -> Bool -> TcM m DecType
resolveTemplateEntries l kid n targs pargs ret insts ko = do
    case insts of
        [inst] -> liftM fst $ resolveTemplateEntry False l kid n targs pargs ret inst
        otherwise -> do
            let choice refresh inst@(e,_,_,_,frees,_,_) = do
                ppkid <- pp kid
                pptyid <- pp (decTypeTyVarId $ unDecT $ entryType e)
                let match = (resolveTemplateEntry refresh l kid n targs pargs ret inst,text "resolveTemplateEntry" <+> ppkid <+> pptyid)
                let post (dec,heads) = return (heads,dec)
                return $ (match,(return,PP.empty),(post,PP.empty),Map.keysSet frees)
            choices' <- mapM (choice True) (init insts)
            choice' <- choice False (last insts)
            multipleSubstitutions l kid SolveAll (n,targs,pargs,ret) (Left ko) (choices'++[choice'])

resolveTemplateEntry :: (ProverK loc m) => Bool -> loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> EntryInst -> TcM m (DecType,Set LocIOCstr)
resolveTemplateEntry solveHead p kid n targs pargs ret (olde,e,headDict,bodyDict,frees,delfrees,solved) = do
    debugTc $ do
        ppn <- ppr n
        pptargs <- ppr targs
        pppargs <- ppr pargs
        ppolde <- ppr olde
        ppe <- ppr e
        pph <- ppr headDict
        ppb <- ppr bodyDict
        liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppn ++ " " ++ pptargs ++ " " ++ pppargs ++ " " ++ ppolde ++ " --> " ++ ppe ++ "\nhead: " ++ pph ++ "\nbody: " ++ ppb
    -- add solved constraints
    addCstrCache p solved
    -- delete promoted constraints
    --buildCstrGraph p promoted promoted
    -- remove frees
    addFrees "resolveTemplateEntry" frees
    delFrees "resolveTemplateEntry" delfrees
    def <- ppTpltAppM p n targs pargs ret
    -- guarantee that the most specific template can be fully instantiated
    olddec <- typeToDecType p (entryType olde)
    dec <- typeToDecType p (entryType e)
    addFrees "resolveTemplateEntry" $ decTypeFrees dec
    --liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppr n ++ " " ++ ppr targs ++ " " ++ ppr pargs ++ " " ++ ppr dec
    -- prove the body (with a recursive declaration)
    let doWrap = isTemplateDecType olddec && decIsOriginal olddec
    (decrec,rec) <- if doWrap
        then do
            debugTc $ do
                ppd <- ppr dec
                liftIO $ putStrLn $ "mkDecEnv " ++ ppd
            rec <- mkDecEnv p dec
            return (dec,rec)
        else return (dec,mempty)
    lineage <- getLineage
    let did = fromJustNote "resolveDecId" (decTypeId decrec)
    debugTc $ do
        ppdid <- ppr did
        pplineage <- mapM pp lineage
        liftIO $ putStrLn $ "resolveTplt "
            ++ show (isTemplateDecType olddec) ++ show (decIsOriginal olddec)
            ++ " " ++ ppdid ++ " : " ++ show (sepBy comma pplineage)
    addHeadTDictDirty p "resolveTemplateEntry" $ templateCstrs (did : lineage) rec def p headDict
    let headCstrs = Set.fromList $ map (snd) $ Graph.labNodes $ tCstrs headDict
    addHeadTDict p "resolveTemplateEntry" $ templateCstrs (did : lineage) mempty def p bodyDict
    linkDependentCstrs p headDict bodyDict
    ppdecrec <- pp decrec
    case n of
        TIden _ -> return ()
        otherwise -> do
            let tycl@(DecClass isAnn isInline rs ws) = tyDecClass $ DecT decrec
            exprC <- getExprC
            let isEmpty = either not Map.null
            case exprC of
                PureExpr -> unless (isEmpty rs && isEmpty ws) $ genTcError (locpos p) $ text "procedure" <+> ppdecrec <+> text "not pure" <+> def
                ReadOnlyExpr -> unless (isEmpty ws) $ genTcError (locpos p) $ text "procedure" <+> ppdecrec <+> text "not read-only" <+> def
                ReadWriteExpr -> return ()
            chgDecClassM $ addDecClassVars rs ws
    return (decrec,headCstrs)

templateCstrs :: Location loc => Lineage -> ModuleTcEnv -> Doc -> loc -> TDict -> TDict
templateCstrs lineage rec doc p d = d { tCstrs = Graph.nmap upd (tCstrs d), tRec = tRec d `mappend` rec }
    where
    upd (Loc l k) = Loc l $ k { kCstr = updCstrState (\st -> st { cstrLineage = lineage}) (kCstr k) }

variadicDecCtx :: DecCtx -> DecCtx
variadicDecCtx (DecCtx is d fs) = DecCtx is d $ variadicFrees fs

-- removes type arguments from a template declaration, as a step of instantiation
removeTemplate :: (ProverK loc m) => loc -> DecType -> TcM m (DecType,[(Constrained Var,IsVariadic)])
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(ProcType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(FunType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(LemmaType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(AxiomType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx [] d@(StructType {})) = do
    let specs' = map (mapFst (varNameToType . unConstrained)) targs
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs' d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(StructType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs d,targs)
removeTemplate l (DVar v@(varIdRead -> True)) = resolveDVar l v >>= removeTemplate l

variadicFrees :: Frees -> Frees
variadicFrees = Map.filter (\b -> b)

ppTpltAppM :: (ProverK loc m) => loc -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m Doc
ppTpltAppM l pid args es ret = do
    ss <- getTSubsts l
    pid' <- substFromTSubsts "ppTplt" dontStop l ss False Map.empty pid
    args' <- mapM (mapM (mapFstM (substFromTSubsts "ppTplt" dontStop l ss False Map.empty))) args
    es' <- mapM (mapM (mapSnd3M (substFromTSubsts "ppTplt" dontStop l ss False Map.empty))) es
    ret' <- substFromTSubsts "ppTplt" dontStop l ss False Map.empty ret
    ppTpltApp pid' args' es' ret'

ppTpltApp :: ProverK Position m => TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m Doc
ppTpltApp (TIden n) args Nothing Nothing = do
    ppn <- pp n
    ppargs <- mapM (ppVariadicArg pp) $ concat $ args
    return $ text "struct" <+> ppn <> abrackets (sepBy comma ppargs)
ppTpltApp (PIden n) targs args (Just ret) = do
    ppret <- pp ret
    ppn <- pp n
    pptargs <- ppOpt targs pp
    ppargs <- ppOpt args pp
    return $ ppret <+> ppn <> abrackets pptargs <> parens ppargs
ppTpltApp (OIden n) targs args (Just ret) = do
    ppret <- pp ret
    ppn <- pp n
    pptargs <- ppOpt targs pp
    ppargs <- ppOpt args pp
    return $ ppret <+> ppn <> abrackets pptargs <> parens ppargs

compareTypeArgs :: ProverK loc m => loc -> Bool -> [(Constrained Type,IsVariadic)] -> [(Constrained Type,IsVariadic)] -> TcM m (Comparison (TcM m))
compareTypeArgs l isLattice xs@[] ys@[] = return (Comparison xs ys EQ EQ False)
compareTypeArgs l isLattice ((Constrained t1 c1,isVariadic1):xs) ((Constrained t2 c2,isVariadic2):ys) = do
    o1 <- compares l isLattice t1 t2
    unless (isVariadic1 == isVariadic2) $ constraintError (ComparisonException "type argument") l t1 pp t2 pp Nothing
    o2 <- compareTypeArgs l isLattice xs ys
    appendComparisons l [o1,o2]
compareTypeArgs l isLattice xs ys = constraintError (ComparisonException "type argument") l xs pp ys pp Nothing

compareProcedureArgs :: (ProverK loc m) => loc -> Bool -> [(Bool,Var,IsVariadic)] -> [(Bool,Var,IsVariadic)] -> TcM m (Comparison (TcM m))
compareProcedureArgs l isLattice xs@[] ys@[] = return (Comparison xs ys EQ EQ False)
compareProcedureArgs l isLattice ((_,v1@(VarName t1 n1),isVariadic1):xs) ((_,v2@(VarName t2 n2),isVariadic2):ys) = do
--    liftIO $ putStrLn $ "comparePArgExp " ++ ppr v1 ++ " " ++ ppr v2 ++ " "
    o0 <- comparesExpr l isLattice (varExpr v1) (varExpr v2)
--    liftIO $ putStr $ show (compOrdering o0)
    --ss <- getTSubsts l
    o1 <- compares l isLattice t1 t2
    --liftIO $ putStrLn $ "comparePArg " ++ ppr t1 ++ " " ++ ppr t2 ++ " " ++ ppr ss ++"\n= " ++ ppr o1
--    liftIO $ putStr $ show (compOrdering o1)
    unless (isVariadic1 == isVariadic2) $ constraintError (ComparisonException "procedure argument") l t1 pp t2 pp Nothing
    o2 <- compareProcedureArgs l isLattice xs ys
    appendComparisons l [o0,o1,o2]
compareProcedureArgs l isLattice xs ys = constraintError (ComparisonException "procedure argument") l xs pp ys pp Nothing

-- | Tells if one declaration is strictly more specific than another, and if not it fails.
-- Since we are unifying base types during instantiation, it may happen that the most specific match is chosen over another more generic best match. This problem does not arise though if we only resolve templates on full instantiation. If we ever change this, we should use instead a three-way comparison that also tries to minimize the number of instantiated type variables in the context.
-- An example is if we tried to match the template over a type variable T:
-- y = f ((T) x)
-- bool f (int x) { ... }     (1)
-- bool f (T x) { ... }       (2)
-- bool f (T [[N]] x) { ... } (3)
-- We would be choosing (1), even though the best match is in principle (2), that does not instantiate T.
-- doesn't take into consideration index conditions
-- compare original declarations, not instantiated ones
compareTemplateDecls :: (ProverK loc m) => Doc -> loc -> Bool -> TIdentifier -> EntryInst -> EntryInst -> TcM m (Ordering,Ordering,Bool)
compareTemplateDecls def l isLattice n (e1,e1',d1,_,_,_,_) (e2,e2',d2,_,_,_,_) = liftM fst $ tcProveTop l "compare" $ tcBlock $ do
    ord <- compareTemplateEntriesTwice def l isLattice n e1 e1' e2 e2'
    debugTc $ do
        ppo <- pp ord
        liftIO $ putStrLn $ "finished comparing decls " ++ show ppo
    return $ compOrdering ord
    
compareTwice :: (ProverK loc m,PP (TcM m) x,VarsG (TcM m) x) => loc -> x -> x -> x -> x -> (x -> x -> TcM m (Comparison (TcM m))) -> (x -> x -> TcM m (Comparison (TcM m))) -> TcM m (Comparison (TcM m))
compareTwice l x x' y y' cmp1 cmp2 = do
    o <- cmp1 x y
    --debugTc $ do
    --    ppo <- ppr o
    --    liftIO $ putStrLn $ "comparing before " ++ ppo
    case compOrdering o of
        (ord,isLat,ko) -> do
            o' <- cmp2 x' y'
            --debugTc $ do
            --    ppo' <- ppr o'
            --    liftIO $ putStrLn $ "comparing after " ++ ppo'
            case compOrdering o' of
                (ord',isLat',ko') -> do -- the initial non-coercion comparison is the one to choose from
                    appendComparison l o o' -- the pre and post comparisons should be consistent
                    return $ Comparison x y (minOrd ord ord') (minOrd isLat isLat') (min ko ko')
                otherwise -> do
                    ppo <- ppr o
                    ppo' <- ppr $ compOrdering o'
                    constraintError (\x y mb -> Halt $ ComparisonException ("comparetwice " ++ ppo ++ "\n" ++ ppo') x y mb) l x' pp y' pp Nothing

minOrd x y | x == y = x
minOrd EQ y = y
minOrd x EQ = x
    
compareTemplateEntriesTwice :: ProverK loc m => Doc -> loc -> Bool -> TIdentifier -> EntryEnv -> EntryEnv -> EntryEnv -> EntryEnv -> TcM m (Comparison (TcM m))
compareTemplateEntriesTwice def l isLattice n e1 e1' e2 e2' = do
    let f e = do
        ppe <- pp (entryType e) 
        return $ (locpos $ entryLoc e,ppe)
    defs <- mapM f [(e1),(e2)]
    ord <- compareTwice l e1 e1' e2 e2' (compareTemplateEntries def l isLattice n) (compareTemplateEntries def l isLattice n)
    let (o,isLat,ko) = compOrdering ord 
    ord' <- if (mappend o isLat == EQ) 
        then do
            let ord' = comparesDecIds True (entryType e1) (entryType e2)
            case ord' of
                Just EQ -> tcError (locpos l) $ Halt $ DuplicateTemplateInstances def defs
                Just o' -> return $ Comparison e1 e2 o' EQ ko
                Nothing -> tcError (locpos l) $ Halt $ DuplicateTemplateInstances def defs
        else return ord
    return ord'
    
compareTemplateEntries :: (ProverK loc m) => Doc -> loc -> Bool -> TIdentifier -> EntryEnv -> EntryEnv -> TcM m (Comparison (TcM m))
compareTemplateEntries def l isLattice n e1 e2 = liftM fst $ tcProveTop l "compare" $ tcBlock $ do
    debugTc $ do
        pp1 <- ppr e1
        pp2 <- ppr e2
        liftIO $ putStrLn $ "compareTemplateEntries " ++ pp1 ++ "\n" ++ pp2
    ord <- do
        let cmp = comparesDecIds False (entryType e1) (entryType e2)
        case cmp of
            Just EQ -> do
                debugTc $ liftIO $ putStrLn $ "sameEntry"
                return $ Comparison e1 e2 EQ EQ False
            otherwise -> do
                State.modify $ \env -> env { localDeps = Set.empty, globalDeps = Set.empty }
                (targs1,pargs1,ret1) <- templateArgs (entryLoc e1) n (entryType e1)
                (targs2,pargs2,ret2) <- templateArgs (entryLoc e2) n (entryType e2)
                unless (isJust ret1 == isJust ret2) $ do
                    ppe1 <- ppr e1
                    ppe2 <- ppr e2
                    error $ "declarations should have the same return type " ++ ppe1 ++ "\n" ++ ppe2
                let f e = do
                    ppe <- pp (entryType e) 
                    return $ (locpos $ entryLoc e,ppe)
                defs <- mapM f [(e1),(e2)]
                let err = TypecheckerError (locpos l) . Halt . ConflictingTemplateInstances def defs
                addErrorM l err $ do
                    ord2 <- if (isJust ret1)
                        -- for procedures, compare the procedure arguments
                        then compareProcedureArgs l isLattice (concat pargs1) (concat pargs2)
                        -- for structs, compare the specialization types
                        else compareTypeArgs l isLattice (concat targs1) (concat targs2)
                    ord3 <- comparesList l isLattice (maybeToList ret1) (maybeToList ret2)
                    appendComparisons l [ord2,ord3]
    debugTc $ liftIO $ putStrLn $ "comparedTemplateEntries " ++ show (decTypeId $ unDecT $ entryType e1) ++" "++ show (decTypeId $ unDecT $ entryType e2) ++ " " ++ show (compOrdering ord)
    return ord

-- favor specializations over the base template
comparesDecIds ::  Bool -> Type -> Type -> Maybe Ordering
comparesDecIds allowReps d1@(DecT (DecType j1 isRec1 _ _ _ _ _)) d2@(DecT (DecType j2 isRec2 _ _ _ _ _)) = do
    compareDecTypeK allowReps j1 isRec1 j2 isRec2
     
compareDecTypeK :: Bool -> ModuleTyVarId -> DecTypeK -> ModuleTyVarId -> DecTypeK -> Maybe Ordering
compareDecTypeK allowReps j1 d1 j2 d2 | j1 == j2 && d1 == d2 = if allowReps then Just LT else Just EQ
compareDecTypeK allowReps j1 (DecTypeRec i1) j2 (DecTypeRec i2) | i1 == i2 = if allowReps
    then Just LT -- choose one of them since they are instantiations of the same declaration
    else Nothing
compareDecTypeK allowReps j1 (DecTypeRec i1) j2 d2 | i1 == j2 = Just LT
compareDecTypeK allowReps j1 d1 j2 (DecTypeRec i2) | i2 == j1 = Just GT
compareDecTypeK allowReps j1 d1 j2 d2 = Nothing

-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (ProverK loc m) => Set ModuleTyVarId -> loc -> Doc -> Bool -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> [EntryEnv] -> TcM m ([Either (EntryEnv,SecrecError) EntryInst],Set ModuleTyVarId)
instantiateTemplateEntries valids l def isLattice kid n targs pargs ret [] = return ([],Set.empty)
instantiateTemplateEntries valids l def isLattice kid n targs pargs ret (e:es) = do
    let d = unDecT (entryType e)
    let did = fromJustNote "instantiate" $ decTypeTyVarId d
    if Set.member did valids
        then instantiateTemplateEntries valids l def isLattice kid n targs pargs ret es
        else do
            r <- instantiateTemplateEntry l kid n targs pargs ret e
            valids' <- case r of
                Left _ -> return valids
                Right ei -> liftM (Set.union valids) (addValidEntry l def isLattice n ei)
            (rs,valids'') <- instantiateTemplateEntries valids' l def isLattice kid n targs pargs ret es
            return (r:rs,valids'')

-- skip declarations whose instantiations have already matched
-- careful, because this only works without implicit coercion or when the instantiation is not ambiguous
addValidEntry :: ProverK loc m => loc -> Doc -> Bool -> TIdentifier -> EntryInst -> TcM m (Set ModuleTyVarId)
addValidEntry l def isLattice n (e,e',_,_,_,_,_) = do
    let d = unDecT (entryType e)
    if isLattice
        then do
            ori <- getOriginalDec l d
            o <- compareTemplateEntries def l isLattice n (EntryEnv (entryLoc e) $ DecT ori) e'
            case o of
                Comparison _ _ _ EQ _ -> return (Set.fromList $ decLineage d)
                otherwise -> return Set.empty 
        else return (Set.fromList $ decLineage d)

unifyTemplateTypeArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Constrained Type,IsVariadic)] -> TcM m ()
unifyTemplateTypeArgs l lhs rhs = do
--    liftIO $ putStrLn $ "unifyTpltTyArg " ++ ppr lhs ++ " " ++ ppr (map (\(x,y) -> (unConstrainedx,y)) rhs)
    (cs,ks) <- tcWithCstrs l "unity tplt type args" $ do
        -- expand the passed type arguments
        ts <- concatMapM (expandVariadicType l) lhs
        -- separate procedure argument types from their conditions
        let (tts,catMaybes -> tcs) = unzip $ map (\(Constrained t c,b) -> ((t,b),c)) rhs
        -- match each procedure argument type
        pptts <- pp tts
        ppts <- pp ts
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "template type arguments") (pptts) (ppts) . Just)
            (matchVariadicTypeArgs l tts ts)
        return tcs
    -- check the procedure argument conditions
    forM_ cs $ \c -> withDependencies ks $ tcCstrM_ l $ IsValid c      

matchVariadicTypeArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [Type] -> TcM m ()
matchVariadicTypeArgs l [] [] = return ()
matchVariadicTypeArgs l xs@[] ys = do
    ppxs <- pp xs
    ppys <- pp ys
    genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> ppxs <+> ppys
matchVariadicTypeArgs l (x:xs) ys = do
    ys' <- matchVariadicTypeArg l x ys
    matchVariadicTypeArgs l xs ys'

-- matches a procedure argument type with a list of types, and produces a remainder of unmatched types
matchVariadicTypeArg :: (ProverK loc m) => loc -> (Type,IsVariadic) -> [Type] -> TcM m [Type]
matchVariadicTypeArg l x@(t,False) ys@[] = do
    ppx <- pp x
    ppys <- pp ys
    genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> ppx <+> ppys
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
    unifiesExprTy l sz (indexExpr $ toEnum $ length xs1)
    return xs2      

matchVariadicPArgs :: (ProverK loc m) => loc -> [(Bool,Expr,IsVariadic)] -> [(Either Expr Type,IsVariadic)] -> TcM m ()
matchVariadicPArgs l xs ys = do
    xys <- addErrorM l (TypecheckerError (locpos l) . GenTcError (text "matching procedure argument base types") . Just) $ matchBasePArgs l xs ys
    addErrorM l (TypecheckerError (locpos l) . GenTcError (text "matching procedure argument expressions") . Just) $ forM_ xys (uncurry (matchPArgs l))

matchBasePArgs :: ProverK loc m => loc -> [(Bool,Expr,IsVariadic)] -> [(Either Expr Type,IsVariadic)] -> TcM m [([(Bool,Expr,IsVariadic)],[(Either Expr Type,IsVariadic)])]
matchBasePArgs l [] [] = return []
matchBasePArgs l (x:xs) [] | thr3 x = do
    xys <- matchBasePArgs l xs []
    return $ ([x],[]) : xys
matchBasePArgs l [] (y:ys) | snd y = do
    xys <- matchBasePArgs l [] ys
    return $ ([],[y]) : xys
matchBasePArgs l (x:xs) (y:ys) | not (thr3 x) && not (snd y) = do
    matchBasePArg l x y
    xys <- matchBasePArgs l xs ys
    return $ ([x],[y]) : xys
matchBasePArgs l xs ys = do
    (ys',ys'') <- checkHead thr3 xs $ spanRight ys xs
    (xs',xs'') <- checkHead snd ys $ spanLeft xs ys
    when (List.null xs' && List.null ys') $ do
        ppxs <- pp $ map (\(x,y,z) -> (y,z)) xs
        ppys <- liftM (sepBy comma) $ mapM (ppVariadicArg (either ppExprTy pp)) ys
        genTcError (locpos l) $ text "Procedure arguments do not match" <+> ppxs <+> text " with " <+> ppys
    xys <- matchBasePArgs l xs'' ys''
    return $ (xs',ys') : xys
  where
    spanLeft xs ys = flip spanM xs $ \x -> maybe (return False) (tryMatchBasePArg l x) (headMay ys)
    spanRight ys xs = flip spanM ys $ \y -> maybe (return False) (\x -> tryMatchBasePArg l x y) (headMay xs)
    checkHead isV (z:zs) m = if isV z then m else do
        (ls,rs) <- m
        return (take 1 ls,drop 1 ls ++ rs)
    checkHead f [] m = return ([],[])

tryMatchBasePArg :: ProverK loc m => loc -> (Bool,Expr,IsVariadic) -> (Either Expr Type,IsVariadic) -> TcM m Bool
tryMatchBasePArg l le re = liftM isRight $ tryTcError l $ matchBasePArg l le re

matchBasePArg :: ProverK loc m => loc -> (Bool,Expr,IsVariadic) -> (Either Expr Type,IsVariadic) -> TcM m ()
matchBasePArg l le re = do
    lb <- lBase l le
    rb <- rBase l re
    tcCstrM_ l $ Unifies lb rb
  where
    lBase :: ProverK loc m => loc -> (Bool,Expr,IsVariadic) -> TcM m Type
    lBase l (isConst,e,False) = return $ loc e
    lBase l (isConst,e,True) = typeBase l (loc e)
    rBase :: ProverK loc m => loc -> (Either Expr Type,IsVariadic) -> TcM m Type
    rBase l (Left e,False) = return $ loc e
    rBase l (Right t,False) = return $ t
    rBase l (Left e,True) = typeBase l (loc e)
    rBase l (Right t,True) = typeBase l t

matchPArgs :: ProverK loc m => loc -> [(Bool,Expr,IsVariadic)] -> [(Either Expr Type,IsVariadic)] -> TcM m ()
matchPArgs l [] [] = return ()
matchPArgs l ((isConst,x,False):xs) ((y,False):ys) = do
    matchPArg l isConst x y
    matchPArgs l xs ys
matchPArgs l [(isConst,x,True)] ys | all (not . snd) ys = do
    sz <- typeSize l $ loc x
    b <- typeBase l $ loc x
    unifiesExprTy l sz (indexExpr $ toEnum $ length ys)
    ys' <- forM ys $ \y -> case y of
        (Left ye,_) -> return ye
        (Right yt,_) -> liftM varExpr $ newTypedVar "vel" yt (not isConst) Nothing
    unifiesExpr l x (ArrayConstructorPExpr (loc x) ys')
matchPArgs l xs [(y,True)] | all (not . thr3) xs = do
    let ty = either loc id y
    sz <- typeSize l ty
    b <- typeBase l ty
    unifiesExprTy l sz (indexExpr $ toEnum $ length xs)
    ye <- case y of
        Left ye -> return ye
        Right yt -> liftM varExpr $ newTypedVar "vel" yt False Nothing
    unifiesExpr l ye (ArrayConstructorPExpr ty $ map snd3 xs)
matchPArgs l [(isConst,x,True)] [(y,True)] = do
    sz1 <- typeSize l $ loc x
    sz2 <- typeSize l $ either loc id y
    unifiesExprTy l sz1 sz2
    ye <- case y of
        Left ye -> return ye
        Right yt -> liftM varExpr $ newTypedVar "vel" yt False Nothing
    unifiesExprTy l x ye
matchPArgs l xs ys = do
    ppxs <- pp $ map (\(x,y,z) -> (y,z)) xs
    ppys <- liftM (sepBy comma) $ mapM (ppVariadicArg (either ppExprTy pp)) ys
    genTcError (locpos l) $ text "Procedure argument variadic mismatch" <+> ppxs <+> ppys

--matchVariadicPArg l (isConst,v,False) ((e,True):exs) = undefined
--matchVariadicPArg l (isConst,v,True) exs = do
--    let t = loc v
--    case t of
--        VArrayT (VAVal ts b) -> do
--            let (exs1,exs2) = splitAt (length ts) exs
--            vs <- expandVariadicExpr l isConst (v,True)
--            matchVariadicPArgs l (map (\v -> (isConst,v,False)) vs) exs1
--            return exs2
--        otherwise -> do
--            sz <- typeSize l t
--            b <- typeBase l t
--            (unzip -> (vs,exs1),exs2) <- flip spanMaybeM exs $ \ex -> tryCstrMaybe l $ do
--                v <- newTypedVar "vel" b (not isConst) Nothing
--                matchPArg l isConst (varExpr v) ex >> return (v,ex)
--            -- match the array size
--            unifiesExprTy l sz (indexExpr $ toEnum $ length exs1)
--            -- variadic arrays are themselves always constant
--            unifiesExprTy l v (ArrayConstructorPExpr t $ map varExpr vs)
--            return exs2

matchPArg :: (ProverK loc m) => loc -> Bool -> Expr -> Either Expr Type -> TcM m ()
matchPArg l isConst v2 (Right t) = return ()
matchPArg l isConst v2 (Left e) = do
    --liftIO $ putStrLn $ show $ text "coercePArg" <+> pp isConst <+> ppExprTy v2 <+> ppExprTy e <+> ppExprTy x2
    when isConst $ unifiesExpr l v2 e

expandPArgExpr :: (ProverK loc m) => loc -> (IsConst,Either Expr Type,IsVariadic) -> TcM m [Either Expr Type]
expandPArgExpr l (_,Left e,False) = return [Left e]
expandPArgExpr l (_,Left e,True) = do
    es <- expandVariadicExpr l False (e,True)
    return $ map Left es
expandPArgExpr l (_,Right t,True) = do
    ts <- expandVariadicType l (t,True)
    return $ map (Right) ts

tryExpandPArgExpr :: ProverK loc m => loc -> (IsConst,Either Expr Type,IsVariadic) -> TcM m [(Either Expr Type,IsVariadic)]
tryExpandPArgExpr l e@(_,a,isVariadic) = do
    mb <- tryTcError l $ expandPArgExpr l e
    case mb of
        Right xs -> return $ map (,False) xs
        Left err -> return [(a,isVariadic)]

tryExpandPArg :: ProverK loc m => loc -> (Bool,Expr,IsVariadic) -> TcM m [(Bool,Expr,IsVariadic)]
tryExpandPArg l e@(isConst,a,isVariadic) = do
    mb <- tryTcError l $ expandVariadicExpr l isConst (a,isVariadic)
    case mb of
        Right xs -> return $ map (\x -> (isConst,x,False)) xs
        Left err -> return [e]

matchProcedureArgs :: (ProverK loc m) => loc -> [(IsConst,Either Expr Type,IsVariadic)] -> [(Bool,Var,IsVariadic)] -> TcM m ()
matchProcedureArgs l lhs rhs = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "matching procedure arguments") . Just) $ do
    (_,ks) <- tcWithCstrs l "coerce proc args" $ do
        -- expand passed expressions
        exs <- concatMapM (tryExpandPArgExpr l) lhs
        -- separate procedure arguments from their conditions
        let (vs) = map (\(isConst,v,b) -> ((isConst,varExpr v,b))) rhs
        vs' <- concatMapM (tryExpandPArg l) vs
        -- match each procedure argument
        ppexs <- liftM (sepBy comma) $ mapM (ppVariadicArg (either ppExprTy pp)) exs
        ppvs' <- ppVariadicPArgs ppExprTy vs'
        addErrorM l
            (TypecheckerError (locpos l) . (CoercionException "procedure arguments") (ppexs) (ppvs') . Just)
            (matchVariadicPArgs l vs' exs)
        return ()
    return ()

mapErr :: (Either (EntryEnv,SecrecError) (EntryEnv,EntryEnv,TDict,TDict,CstrCache),Frees,Frees) -> Either (EntryEnv,SecrecError) EntryInst
mapErr (Left x,_,_) = Left x
mapErr (Right (x1,x2,x3,x4,x5),y,z) = Right (x1,x2,x3,x4,y,z,x5)

checkRecursiveDec :: ProverK loc m => loc -> DecType -> TcM m Bool
checkRecursiveDec l d@(DecType _ isRec _ _ _ _ _) = do
    case isRec of
        DecTypeOriginal -> return False
        DecTypeCtx -> return False
        DecTypeRec i -> do
            lin <- getLineage
            let did = fromJustNote "checkRecursiveDec" $ decTypeId d
            return $ List.elem did lin

--writeTpltArgs :: ProverK loc m => loc -> 
--writeTpltArgs
--
--let chg v = if isRec then v { varIdWrite = False } else v chgVarId chg

instantiateTemplateEntry :: (ProverK loc m) => loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> EntryEnv -> TcM m (Either (EntryEnv,SecrecError) EntryInst)
instantiateTemplateEntry p kid n targs pargs ret olde@(EntryEnv l t@(DecT olddec)) = limitExprC ReadOnlyExpr $ newErrorM $ liftM mapErr $ withFrees p $ do
            --doc <- liftM ppTSubsts getTSubsts
            --liftIO $ putStrLn $ "inst " ++ show doc
            isRec <- checkRecursiveDec l olddec
            debugTc $ do
                ppp <- ppr l
                ppl <- ppr l
                ppn <- ppr n
                pptargs <- ppr (fmap (map fst) targs)
                ppargs <- mapM pp pargs
                ppret <- ppr ret
                ppte <- ppr (entryType olde)
                liftIO $ putStrLn $ "instantiating " ++ ppp ++ " " ++ ppl ++ " " ++ ppn ++ " " ++ pptargs ++ " " ++ show ppargs ++ " " ++ ppret ++ " " ++ show isRec ++ "\n" ++ ppte
            -- can't instantiate recursive variables
            (tplt_targs,tplt_pargs,tplt_ret) <- templateArgs l n t -- >>= writeTpltArgs l isRec
            debugTc $ do
                pptargs <- ppr tplt_targs
                pppargs <- mapM (ppVariadicPArgs ppVarTy) tplt_pargs
                ppret <- ppr tplt_ret
                liftIO $ putStrLn $ "instance arguments " ++ pptargs ++ " ; " ++ show pppargs ++ " ; " ++ ppret
            exprC <- getExprC
            (e',hdict,bdict,bgr) <- templateTDict exprC olde
            let addDicts = do
                addHeadTDict l "instantiateTemplateEntry" hdict
                addHeadTDict l "instantiateTemplateEntry" bdict
            let matchName = unifiesTIdentifier l (templateIdentifier $ entryType e') n
            let proveHead = withoutEntry olde $ do
                -- we remove the current entry while typechecking the head constraints
                (_,ks) <- tcWithCstrs l "instantiate" $ do   
                    tcAddDeps l "tplt type args" $ do
                        ppttargs <- liftM (sepBy comma) $ mapM (pp . fst) $ concat tplt_targs
                        --debugTc $ liftIO $ putStrLn $ "tplttargs: " ++ show ppttargs
                        -- unify the explicit invocation template arguments unify with the base template
                        when (isJust targs) $ tcAddDeps l "targs" $ unifyTemplateTypeArgs l (concat targs) (concat tplt_targs)
                        -- unify the procedure return type
                        unifiesList l (maybeToList tplt_ret) (maybeToList ret)
                        -- coerce procedure arguments into the base procedure arguments
                        matchProcedureArgs l (concat pargs) (concat tplt_pargs)
                -- if there are no explicit template type arguments, we need to make sure to check the type invariants
                when (isNothing targs) $ do
                    forM_ (maybe [] (catMaybes . map (\(Constrained x c,isVariadic) -> c)) tplt_targs) $ \c -> do
                        withDependencies ks $ tcCstrM_ l $ IsValid c
                return ()
            -- try to make progress on general constraints that may be bound to bindings of this instance
            let promote = do
                vs <- usedVs (n,targs,pargs,ret)
                tops <- topCstrs l
                let tops' = mapSet (ioCstrId . unLoc) tops
                (relvs,rels) <- relatedCstrs l (Set.toList tops') vs (filterCstrSetScope SolveLocal)
                let rels' = mapSet (ioCstrId . unLoc) rels
                buildCstrGraph l rels'
                debugTc $ do
                    ppl <- ppr l
                    ppvs <- ppr vs
                    pprels' <- ppr rels'
                    liftIO $ putStrLn $ "tpltVars " ++ ppl ++ " " ++ ppvs
                    liftIO $ putStrLn $ "relVars " ++ ppl ++ " " ++ pprels'
                    dicts <- State.gets tDict
                    ss <- ppConstraints (tCstrs $ headNe dicts)
                    liftIO $ putStrLn $ (concat $ replicate (length dicts) ">") ++ "tpltCstrs " ++ ppl ++ " [" ++ show ss ++ "\n]"
                    forM_ (tail $ Foldable.toList dicts) $ \d -> do
                        ssd <- ppConstraints (tCstrs d)
                        liftIO $ putStrLn $ "\n[" ++ show ssd ++ "\n]"
                    --doc <- liftM ppTSubsts $ getTSubsts l
                    --liftIO $ putStrLn $ show doc
                return rels'
            mode <- defaultSolveMode
            ok <- orError $ tcWith (locpos p) "instantiate" $ do
                st <- getCstrState
                ppn <- ppr n
                ppp <- ppr l
                ppl <- ppr l
                addDicts >> matchName >> proveHead
                solveWith p ("instantiate with names " ++ ppn ++ " " ++ ppp ++ " " ++ ppl ++ " " ++ show mode) mode
                ((promoted,_),cache) <- withCstrState (locpos p) st $ onFrees p $ onCache $ tcProveWith l "promote" (mode { solveFail = FirstFail False }) $ promote
                return (cache)
            --ks <- ppConstraints =<< liftM (maybe Graph.empty tCstrs . headMay . tDict) State.get
            --liftIO $ putStrLn $ "instantiate with names " ++ ppr n ++ " " ++ show ks
            case ok of
                Left err -> do
                    debugTc $ do
                        ppn <- ppr n
                        pperr <- ppr err
                        liftIO $ putStrLn $ "failed to instantiate " ++ pprid kid ++ " " ++ ppn ++" "++ show (decTypeTyVarId olddec) ++ "\n" ++ pperr
                    return $ Left (olde,err)
                Right ((cache),TDict hgr _ subst recs) -> do
                        --removeIOCstrGraphFrees hgr
                        -- we don't need to rename recursive declarations, since no variables have been bound
                        (e',(subst',bgr',hgr',recs')) <- localTemplateWith l e' (subst,bgr,toPureCstrs hgr,recs)
                        hgr'' <- substFromTSubsts "instantiate tplt" dontStop l subst' False Map.empty hgr'
                        bgr'' <- substFromTSubsts "instantiate tplt" dontStop l subst' False Map.empty bgr'
                        recs'' <- substFromTSubsts "instantiate tplt" dontStop l subst' False Map.empty recs'
                        hgr1 <- fromPureCstrs hgr''
                        bgr1 <- fromPureCstrs bgr''
                        let headDict = (TDict hgr1 Set.empty subst' recs'')
                        let bodyDict = (TDict bgr1 Set.empty emptyTSubsts mempty)
                        --let headPureDict = toPureTDict headDict
                        --let bodyPureDict = toPureTDict bodyDict
                        debugTc $ do
                            pph <- ppConstraints $ tCstrs headDict
                            ppb <- ppConstraints $ tCstrs bodyDict
                            ppn <- ppr n
                            liftIO $ putStrLn $ "remainder " ++ pprid kid ++ " " ++ ppn ++" " ++ show (decTypeTyVarId olddec) ++ " " ++ show pph ++"\n"++ show ppb
                        dec1 <- typeToDecType l (entryType e')
                        (dec2,targs') <- removeTemplate l dec1 >>= substFromTSubsts "instantiate tplt" dontStop l subst' False Map.empty
                        --let dec3 = addDecDicts dec2 headPureDict bodyPureDict
                        --debugTc $ liftIO $ putStrLn $ "withTplt: " ++ ppr l ++ "\n" ++ ppr subst ++ "\n+++\n"++ppr subst' ++ "\n" ++ ppr dec2

                        let targs'' = map (mapFst (varNameToType . unConstrained)) targs'
                        let doWrap = isTemplateDecType olddec && decIsOriginal olddec
                        decrec <- if doWrap then mkInvocationDec p dec2 targs'' else return dec2
                        return $ Right (olde,e' { entryType = DecT decrec },headDict,bodyDict,cache)

-- merge two dictionaries with the second depending on the first
linkDependentCstrs :: (ProverK loc m) => loc -> TDict -> TDict -> TcM m ()
linkDependentCstrs l from to = do
    let froms = map fst $ endsGr $ tCstrs from
    let tos = map fst $ rootsGr $ tCstrs to
    let deps = [ (f,t) | f <- froms, t <- tos ]
    let upd d (f,t) = d { tCstrs = insEdge (f,t,()) (tCstrs d) } 
    updateHeadTDict l "dependentCstrs" $ \d -> return ((),foldl' upd d deps)

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (DecType _ _ _ _ _ _ t) = templateIdentifier'' t
        where
        templateIdentifier'' (ProcType _ n _ _ _ _ _) = n
        templateIdentifier'' (FunType isLeak _ n _ _ _ _ _) = n
        templateIdentifier'' (AxiomType isLeak _ _ _ _) = error "no identifier for axiom"
        templateIdentifier'' (LemmaType isLeak _ n _ _ _ _) = n
        templateIdentifier'' (StructType _ (TIden n) _ _) = TIden n
   
-- has type or procedure constrained arguments     
--hasCondsDecType :: (MonadIO m) => DecType -> TcM m Bool
--hasCondsDecType (DecType _ _ targs _ _ _ _ _ d) = do
--    b <- hasCondsDecType d
--    return $ b || (any hasConstrained $ map fst targs)
--hasCondsDecType (ProcType _ _ pargs _ _ _ _) = return $ any hasConstrained $ map snd3 pargs
--hasCondsDecType _ = return False
 
-- | Extracts a head signature from a template type declaration (template arguments,procedure arguments, procedure return type)
templateArgs :: (MonadIO m,Location loc) => loc -> TIdentifier -> Type -> TcM m (Maybe [(Constrained Type,IsVariadic)],Maybe [(Bool,Var,IsVariadic)],Maybe Type)
templateArgs l (TIden name) t = case t of
    DecT d@(DecType _ isRec args hcstrs cstrs specs body) -> do 
        return (Just $ decTypeArgs d,Nothing,Nothing)
templateArgs l name t = case t of
    DecT d@(DecType _ isRec args hcstrs cstrs specs (ProcType _ n vars ret ann stmts _)) -> do -- include the return type
        return (Just $ decTypeArgs d,Just vars,Just ret)
    DecT d@(DecType _ isRec args hcstrs cstrs specs (FunType isLeak _ n vars ret ann stmts _)) -> do -- include the return type
        return (Just $ decTypeArgs d,Just vars,Just ret)
    DecT d@(DecType _ isRec args hcstrs cstrs specs (LemmaType isLeak _ n vars ann stmts _)) -> do
        return (Just $ decTypeArgs d,Just vars,Just $ ComplexT Void)
    DecT d@(DecType _ isRec args hcstrs cstrs specs (AxiomType isLeak _ vars ann _)) -> do
        return (Just $ decTypeArgs d,Just vars,Nothing)
    otherwise -> genTcError (locpos l) $ text "Invalid type for procedure template"

tpltTyVars :: Maybe [(Constrained Type,IsVariadic)] -> Set GIdentifier
tpltTyVars Nothing = Set.empty
tpltTyVars (Just xs) = Set.fromList $ map (varNameId . fromJust . typeToVarName . unConstrained . fst) xs

--addDecDicts :: DecType -> PureTDict -> PureTDict -> DecType
--addDecDicts (DecType i isRec vars hd bd specs ss) hd' bd' = DecType i isRec vars hd' bd' specs ss

templateTDict :: (ProverK Position m) => ExprClass -> EntryEnv -> TcM m (EntryEnv,TDict,TDict,TCstrGraph)
templateTDict exprC e = case entryType e of
    DecT (DecType i isRec vars (DecCtx his hd hfrees) (DecCtx bis d bfrees) specs ss) -> do
        hd' <- fromPureTDict $ hd { pureCstrs = purify $ pureCstrs hd }
        let d' = TDict Graph.empty Set.empty (pureSubsts d) (pureRec d)
        let e' = e { entryType = DecT (DecType i isRec vars (DecCtx his emptyPureTDict hfrees) (DecCtx bis emptyPureTDict bfrees) specs ss) }
        return (e',hd',d',purify $ pureCstrs d)
    otherwise -> return (e,emptyTDict,emptyTDict,Graph.empty)
  where
    purify :: TCstrGraph -> TCstrGraph
    purify = Graph.nmap (fmap add)
    add = updCstrState (\st -> st { cstrExprC = min exprC (cstrExprC st) })

--condVarType (Constrained (VarName t n) c) = constrainedType t c
--condVar (Constrained (VarName t n) c) = VarName (constrainedType t c) n
--condT (Constrained t c) = constrainedType t c

--refreshEntryPVars :: ProverK loc m => loc -> EntryEnv -> Maybe [GIdentifier] -> TcM m EntryEnv
--refreshEntryPVars l e Nothing = return e
--refreshEntryPVars l e@(EntryEnv p t) (Just vars') = case t of
--    DecT (DecType i (Just (k,Just vars)) ts hd hfrees bd bfrees specs b) -> do
--        debugTc $ do
--            ppvars' <- ppr vars'
--            ppvars <- ppr vars
--            liftIO $ putStrLn $ "refreshEntryPVars: dropping " ++ ppvars ++ " for " ++ ppvars'
--        forM_ vars $ \(VIden v) -> removeFree v
--        let ss = emptySubstsProxy
--        let ssBounds = Map.fromList $ zip vars vars'
--        hd' <- substProxy "refreshEntryPVars" ss False ssBounds $ deleteSubsts (map unVIden vars) hd
--        hfrees' <- liftM (Map.mapKeys unVIden) $ substProxy "refreshEntryPVars" emptySubstsProxy False ssBounds $ Map.mapKeys VIden hfrees
--        return $ EntryEnv p $ DecT $ DecType i (Just (k,Just vars')) ts hd' hfrees' bd bfrees specs b
--    otherwise -> return e

deleteSubsts :: [VarIdentifier] -> PureTDict -> PureTDict
deleteSubsts vs d = d { pureSubsts = TSubsts $ deletes vs $ unTSubsts $ pureSubsts d }
    where
    deletes [] xs = xs
    deletes (v:vs) xs = Map.delete v (deletes vs xs)

-- | renames the variables in a template to local names
localTemplate :: (ProverK loc m) => loc -> EntryEnv -> TcM m EntryEnv
localTemplate l e = liftM fst $ localTemplateWith l e ()

localTemplateDec :: (ProverK loc m) => loc -> DecType -> TcM m DecType
localTemplateDec l dec = do
    t <- liftM (entryType . fst) $ localTemplateWith l (EntryEnv (locpos l) $ DecT dec) ()
    typeToDecType l t

localTemplateWith :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> EntryEnv -> a -> TcM m (EntryEnv,a)
localTemplateWith l e a = case entryType e of
    DecT t -> do
        debugTc $ do
            ppl <- ppr l
            ppt <- ppr t
            liftIO $ putStrLn $ "localTemplate: " ++ ppl ++ "\n" ++ ppt
        (t',(ss,ssBounds)) <- State.runStateT (localTemplateType (entryLoc e) t) (emptySubstsProxy,Map.empty)
        debugTc $ do
            ppl <- ppr l
            ppbounds <- ppr ssBounds
            liftIO $ putStrLn $ "localSS: " ++ ppl ++ "\n" ++ ppbounds
        debugTc $ do
            ppl <- ppr l
            ppt' <- ppr t'
            liftIO $ putStrLn $ "localTemplate': " ++ ppl ++ "\n" ++ ppt'
        a' <- substProxy "localTplt" dontStop ss False ssBounds a
        debugTc $ do
            ppl <- ppr l
            ppa' <- ppr a'
            liftIO $ putStrLn $ "localTemplateReturn: " ++ ppl ++ ppa'
        return (EntryEnv (entryLoc e) $ DecT t',a')

type LocalM m = StateT (SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier) (TcM m)

localTemplateType :: (ProverK loc m) => loc -> DecType -> LocalM m DecType
localTemplateType (l::loc) et = case et of
    DecType tpltid isrec args hctx bctx (unzip -> (specials,isVariadics2)) body -> do
        (hctx') <- localDecCtx l hctx
        (args') <- uniqueTyVars l args
        specials' <- substLocalM specials
        (bctx',body') <- localTemplateInnerType l bctx body
        return (DecType tpltid isrec args' hctx' bctx' (zip specials' isVariadics2) body')

localDecCtx :: ProverK loc m => loc -> DecCtx -> LocalM m DecCtx
localDecCtx l (DecCtx is dict frees) = do
    (frees',freelst) <- lift $ Utils.mapAndUnzipM freeVar $ Map.toList $ Map.mapKeys VIden frees
    addLocalM (substsProxyFromList freelst,Map.fromList freelst)
    dict' <- substLocalM dict
    return (DecCtx is dict' (Map.mapKeys unVIden $ Map.fromList $ frees'))

localTemplateInnerType :: (ProverK loc m) => loc -> DecCtx -> InnerDecType -> LocalM m (DecCtx,InnerDecType)
localTemplateInnerType (l::loc) bctx et = case et of
    ProcType p pid args ret ann stmts c -> do
        (args') <- uniqueProcVars l args
        pid' <- substLocalM pid
        ret' <- substLocalM ret
        (bctx') <- localDecCtx l bctx
        ann' <- substLocalM ann
        stmts' <- substLocalM stmts
        c' <- substLocalM c
        return (bctx',ProcType p pid' args' ret' ann' stmts' c')
    FunType isLeak p pid args ret ann stmts c -> do
        (args') <- uniqueProcVars l args
        pid' <- substLocalM pid
        ret' <- substLocalM ret
        (bctx') <- localDecCtx l bctx
        ann' <- substLocalM ann
        stmts' <- substLocalM stmts
        c' <- substLocalM c
        return (bctx',FunType isLeak p pid' args' ret' ann' stmts' c')
    AxiomType isLeak p args ann c -> do
        (args') <- uniqueProcVars l args
        (bctx') <- localDecCtx l bctx
        ann' <- substLocalM ann
        c' <- substLocalM c
        return (bctx',AxiomType isLeak p args' ann' c')
    LemmaType isLeak p pid args ann stmts c -> do
        (args') <- uniqueProcVars l args
        pid' <- substLocalM pid
        (bctx') <- localDecCtx l bctx
        ann' <- substLocalM ann
        stmts' <- substLocalM stmts
        c' <- substLocalM c
        return (bctx',LemmaType isLeak p pid' args' ann' stmts' c')
    StructType p sid atts c -> do
        sid' <- substLocalM sid
        (bctx') <- localDecCtx l bctx
        atts' <- substLocalM atts
        c' <- substLocalM c
        return (bctx',StructType p sid' atts' c')
       
freeVar :: ProverK Position m => (GIdentifier,IsVariadic) -> TcM m ((GIdentifier,IsVariadic),(GIdentifier,GIdentifier))
freeVar (VIden v,isVariadic) = do
    ModuleTyVarId mn j <- newModuleTyVarId
    let v' = v { varIdUniq = Just j, varIdModule = mn }
    --addFree v'
    return ((VIden v',isVariadic),(VIden v,VIden v'))
    
uniqueTyVar :: ProverK loc m => loc -> (Constrained Var,IsVariadic) -> LocalM m (Constrained Var,IsVariadic)
uniqueTyVar (l::loc) (Constrained i c,isVariadic) = do
    i' <- uniqueVar l True i
    c' <- substLocalM c
    return (Constrained i' c',isVariadic)
--uniqueTyVar (l::loc) (i,isVariadic) = return (i,isVariadic)

uniqueVar :: ProverK loc m => loc -> Bool -> Var -> LocalM m Var
uniqueVar l isConst i@(VarName t (VIden v@(varIdRead -> True))) = do
    t' <- uniqueTy l t
    mb <- getSubstVarM $ VIden v
    case mb of
        Nothing -> do
            v' <- lift $ freshVarId (varIdBase v) Nothing
            let i' = VarName t' $ VIden v'
            let ss = substsProxyFromTSubsts l (TSubsts $ Map.singleton v (varNameToType i'))
            let ssBounds = if isConst then Map.singleton (VIden v) (VIden v') else Map.empty
            addLocalM (ss,ssBounds)
            return i'
        Just v' -> return $ VarName t' v'
uniqueVar l isConst i = return i
--uniqueVar l isConst i = do
--    ppl <- lift $ ppr l
--    ppi <- lift $ ppr i
--    error $ "uniqueVar: " ++ ppl ++ ": " ++ ppi

uniqueTy :: ProverK loc m => loc -> Type -> LocalM m Type
uniqueTy l (typeToVarName -> Just v) = liftM varNameToType $ uniqueVar l True v
uniqueTy l (VAType t sz) = do
    t' <- substLocalM t
    IdxT sz' <- uniqueTy l (IdxT sz)
    return $ VAType t' sz'
uniqueTy l t = substLocalM t

uniqueTyVars :: ProverK loc m => loc -> [(Constrained Var,IsVariadic)] -> LocalM m [(Constrained Var,IsVariadic)]
uniqueTyVars l xs = mapM (uniqueTyVar l) xs

uniqueProcVar :: ProverK loc m => loc -> (Bool,Var,IsVariadic) -> LocalM m (Bool,Var,IsVariadic)
-- refresh const variables
uniqueProcVar (l::loc) (isConst,i,isVariadic) = do
    let doConst = isConst || isVariadic
    i' <- uniqueVar l doConst i
    return (isConst,i',isVariadic)
--uniqueProcVar (l::loc) (isConst,i,isVariadic) = return (isConst,i,isVariadic)

uniqueProcVars :: ProverK loc m => loc -> [(Bool,Var,IsVariadic)] -> LocalM m [(Bool,Var,IsVariadic)]
uniqueProcVars l xs = mapM (uniqueProcVar l) xs

addLocalM :: ProverK Position m => (SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier) -> LocalM m ()
addLocalM (ss,ssBounds) = State.modify $ \(x,y) -> (ss `appendSubstsProxy` x,Map.union ssBounds y)

getSubstVarM :: (ProverK Position m) => GIdentifier -> LocalM m (Maybe GIdentifier)
getSubstVarM v = do
    (_,ssBounds) <- State.get
    return $ Map.lookup v ssBounds

substLocalM :: (Vars GIdentifier (TcM m) a,ProverK Position m) => a -> LocalM m a
substLocalM x = do
    (ss,ssBounds) <- State.get
    lift $ substProxy "localTplt" dontStop ss False ssBounds x









