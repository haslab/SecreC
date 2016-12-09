{-# LANGUAGE TupleSections, UndecidableInstances, MultiParamTypeClasses, FlexibleInstances, DeriveGeneric, DeriveDataTypeable, ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.Transformation.Dafny where

import Language.SecreC.Syntax
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Template
import Language.SecreC.Prover.Base
import Language.SecreC.Utils as Utils
import Language.SecreC.Pretty as PP
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Conversion
import Language.SecreC.TypeChecker.Type
import Language.SecreC.Modules
import Language.SecreC.Prover.Semantics
import Language.SecreC.Vars
import Language.SecreC.Transformation.Simplify

import Text.PrettyPrint as PP

import Data.List as List
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data
import Data.Generics hiding (empty,Generic(..))
import Data.Maybe
import Data.Foldable as Foldable
import Data.Either

import GHC.Generics

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State

import Safe

type DafnyK m = ProverK Position m
type DafnyM m = StateT DafnySt (TcM m)

data DafnyId
    = PId POId ModuleTyVarId
    | FId POId ModuleTyVarId Bool
    | LId GIdentifier ModuleTyVarId Bool
    | SId GIdentifier ModuleTyVarId
    | AId ModuleTyVarId Bool
  deriving (Data,Typeable,Generic,Show,Eq,Ord)

isTypeDafnyId :: DafnyId -> Bool
isTypeDafnyId (SId {}) = True
isTypeDafnyId _ = False

dafnyIdLeak :: DafnyId -> Bool
dafnyIdLeak (PId _ tid) = False
dafnyIdLeak (FId _ tid b) = b
dafnyIdLeak (LId _ tid b) = b
dafnyIdLeak (SId _ tid) = False
dafnyIdLeak (AId tid b) = b

dafnyIdModuleTyVarId :: DafnyId -> ModuleTyVarId
dafnyIdModuleTyVarId (PId _ tid) = tid
dafnyIdModuleTyVarId (FId _ tid _) = tid
dafnyIdModuleTyVarId (LId _ tid _) = tid
dafnyIdModuleTyVarId (SId _ tid) = tid
dafnyIdModuleTyVarId (AId tid isLeak) = tid

putDafnyIdModuleTyVarId :: ModuleTyVarId -> DafnyId -> DafnyId
putDafnyIdModuleTyVarId tid (PId po _) = PId po tid
putDafnyIdModuleTyVarId tid (FId po _ b) = FId po tid b
putDafnyIdModuleTyVarId tid (LId g _ b) = LId g tid b
putDafnyIdModuleTyVarId tid (SId g _) = SId g tid
putDafnyIdModuleTyVarId tid (AId _ isLeak) = AId tid isLeak

dafnyIdModule :: DafnyId -> Maybe Identifier
dafnyIdModule = fmap fst . modTyName . dafnyIdModuleTyVarId

type DafnyEntry = ([Type],Position,DafnyId,Doc,DecType)

data DafnySt = DafnySt {
      dafnies :: Map (Maybe Identifier) (Map DafnyId (Map DafnyId DafnyEntry)) -- generated Dafny entries (top-level variables, types, functions, methods), grouped by module, grouped by base ids
    , imports :: Map Identifier (Set Identifier)
    , leakageMode :: Bool -- True=leakage, False=correctness
    , axiomIds :: Set DafnyId
    , inDecl :: Maybe DafnyId -- decl id
    , decResult :: Maybe Doc --result expression
    , inAnn :: Bool -- inside an annotation
    , currentModule :: Maybe Identifier
    , assumptions :: AnnsDoc
    }

getAssumptions :: DafnyK m => DafnyM m AnnsDoc
getAssumptions = State.gets assumptions

withAssumptions :: DafnyK m => DafnyM m a -> DafnyM m a
withAssumptions m = do
    anns <- getAssumptions
    x <- m
    State.modify $ \env -> env { assumptions = anns }
    return x

dropAssumptions :: DafnyK m => Set VarIdentifier -> DafnyM m a -> DafnyM m a
dropAssumptions xs m = do
    let aux (_,_,vs,_,_) = Set.null $ Set.intersection vs xs
    State.modify $ \env -> env { assumptions = filter aux $ assumptions env }
    m

getLeakMode :: DafnyK m => DafnyM m Bool
getLeakMode = State.gets leakageMode

whenLeakMode :: (Monoid x,DafnyK m) => DafnyM m x -> DafnyM m x
whenLeakMode m = do
    leakMode <- getLeakMode
    if leakMode then m else return mempty
    
withLeakMode :: DafnyK m => Bool -> DafnyM m x -> DafnyM m x
withLeakMode b m = do
    o <- getLeakMode
    State.modify $ \env -> env { leakageMode = o && b }
    x <- m
    State.modify $ \env -> env { leakageMode = o }
    return x
    
getInDecl :: DafnyK m => DafnyM m (Maybe DafnyId)
getInDecl = State.gets inDecl
    
insideDecl :: DafnyK m => DafnyId -> DafnyM m x -> DafnyM m x
insideDecl b m = do
    o <- getInDecl
    State.modify $ \env -> env { inDecl = Just (b) }
    x <- m
    State.modify $ \env -> env { inDecl = o }
    return x

getResult :: DafnyK m => DafnyM m (Maybe Doc)
getResult = State.gets decResult

withResult :: DafnyK m => Doc -> DafnyM m x -> DafnyM m x
withResult res m = do
    o <- getResult
    State.modify $ \env -> env { decResult = Just res }
    x <- m
    State.modify $ \env -> env { decResult = o }
    return x

getInAnn :: DafnyK m => DafnyM m Bool
getInAnn = State.gets inAnn
    
withInAnn :: DafnyK m => Bool -> DafnyM m x -> DafnyM m x
withInAnn b m = do
    o <- getInAnn
    State.modify $ \env -> env { inAnn = b }
    x <- m
    State.modify $ \env -> env { inAnn = o }
    return x

toDafny :: DafnyK m => FilePath -> Bool -> [DafnyId] -> TcM m (Doc,[String])
toDafny prelude leakMode entries = flip State.evalStateT (DafnySt Map.empty Map.empty leakMode Set.empty Nothing Nothing False Nothing []) $ do
    dfy <- liftIO $ readFile prelude
    loadAxioms
    mapM_ (loadDafnyId noloc) entries
    ds <- State.gets (Map.toList . dafnies)
    let modules = map fst ds
    (types,code) <- printDafnyModules ds
    let code' = text "module" <+> text "prelude" <+> vbraces (text dfy $+$ types) $+$ code
    axioms <- State.gets (Set.toList . axiomIds)
    paxioms <- mapM (boogieName modules) axioms
    return (code',paxioms)

boogieName :: DafnyK m => [Maybe Identifier] -> DafnyId -> DafnyM m String
boogieName modules did = do
    pdid <- ppDafnyIdM did
    ppmn <- lift $ ppModuleName mn
    return $ show $ text "InterModuleCall$$_" <> int mnum <> text "_" <> ppmn <> text ".__default." <> text (duplicateUnderscores $ show pdid)
  where
    mn = dafnyIdModule did
    mnum = fromJust $ List.lookup mn (zip modules [(2::Int)..])

duplicateUnderscores :: String -> String
duplicateUnderscores [] = []
duplicateUnderscores ('_':xs) = "__" ++ duplicateUnderscores xs
duplicateUnderscores (x:xs) = x : duplicateUnderscores xs

loadAxioms :: DafnyK m => DafnyM m ()
loadAxioms = do
    env <- lift $ getModuleField False (\env -> mempty { axioms = axioms env }) axioms
    let as = map (\(mid,e) -> unDecT $ entryType e) $ Map.toList env
    mapM_ (\d -> loadDafnyDec (decPos d) d) as

isAxiomDafnyId :: DafnyId -> Bool
isAxiomDafnyId (AId {}) = True
isAxiomDafnyId _ = False

entryPointsTypedModuleFile :: DafnyK m => TypedModuleFile -> TcM m [DafnyId]
entryPointsTypedModuleFile (Left (_,_,m,_)) = return $ Set.toList $ collectDafnyIds m
entryPointsTypedModuleFile (Right sci) = do
    let env = sciEnv sci
    let decE = decDafnyId . unDecT . entryType
    let filterEntries = filterAnns False False (const True)
    let ps = concat $ Map.elems $ Map.mapWithKey (\k vs -> catMaybes $ map (\(mid,e) -> decE e) $ Map.toList vs) $ filterEntries $ procedures env
    let fs = concat $ Map.elems $ Map.mapWithKey (\k vs -> catMaybes $ map (\(mid,e) -> decE e) $ Map.toList vs) $ filterEntries $ functions env
    let ls = concat $ Map.elems $ Map.mapWithKey (\k vs -> catMaybes $ map (\(mid,e) -> decE e) $ Map.toList vs) $ filterEntries $ lemmas env
    let ss = concat $ Map.elems $ Map.mapWithKey (\k vs -> catMaybes $ map (\(mid,e) -> decE e) $ Map.toList vs) $ filterEntries $ structs env
    let es = ps ++ fs ++ ls ++ ss
    debugTc $ do
        ppes <- liftM (sepBy space) $ mapM pp es
        liftIO $ putStrLn $ "entryPointsTypedModuleFile: " ++ pprid (sciFile sci) ++ " " ++ show ppes
    return es

collectDafnyIds :: Data a => a -> Set DafnyId
collectDafnyIds = everything Set.union (mkQ Set.empty aux)
    where
    aux :: DecType -> Set DafnyId
    aux = Set.fromList . maybeToList . decDafnyId

decDafnyTypes :: DecType -> [Type]
decDafnyTypes d@(DecType tid (DecTypeInst _ _) _ _ _ _ _) = map (unConstrained . fst) (decTypeArgs d)
decDafnyTypes d = []

-- (base id,instance id,base arguments)
decDafnyIds :: DecType -> Maybe (DafnyId,DafnyId,[Type])
decDafnyIds d@(DecType tid isRec _ _ _ _ (ProcType _ pn _ _ _ _ _)) | not (isTemplateDecType d) = Just (bid,did,ts)
    where
    did = pIdenToDafnyId pn tid
    bid = decDafnyRecId did isRec
    ts = decDafnyTypes d
decDafnyIds d@(DecType tid isRec _ _ _ _ (FunType isLeak _ pn _ _ _ _ _)) | not (isTemplateDecType d) = Just (bid,did,ts)
    where
    did = fIdenToDafnyId pn tid isLeak
    bid = decDafnyRecId did isRec 
    ts = decDafnyTypes d
decDafnyIds d@(DecType tid isRec _ _ _ _ (StructType _ sn _ _)) | not (isTemplateDecType d) = Just (bid,did,ts)
    where
    did = SId sn tid
    bid = decDafnyRecId did isRec
    ts = decDafnyTypes d
decDafnyIds d@(DecType tid isRec _ _ _ _ (AxiomType isLeak _ _ _ _)) = Just (did,bid,ts)
    where
    did = AId tid isLeak
    bid = decDafnyRecId did isRec
    ts = decDafnyTypes d
decDafnyIds d@(DecType tid isRec _ _ _ _ (LemmaType isLeak _ pn _ _ _ _)) | not (isTemplateDecType d) = Just (bid,did,ts)
    where
    did = LId (funit pn) tid isLeak
    bid = decDafnyRecId did isRec
    ts = decDafnyTypes d
decDafnyIds dec = Nothing

decDafnyRecId bid isRec = case isRec of
    DecTypeOri _ -> bid
    DecTypeCtx -> bid
    DecTypeInst j _ -> putDafnyIdModuleTyVarId j bid

decDafnyId :: DecType -> Maybe DafnyId
decDafnyId d = fmap snd3 $ decDafnyIds d

fromDecDafnyId :: DecType -> DafnyId
fromDecDafnyId d = fromJustNote ("fromDecDafnyId " ++ show d) (decDafnyId d)

printDafnyModules :: DafnyK m => [(Maybe Identifier,Map DafnyId (Map DafnyId DafnyEntry))] -> DafnyM m (Doc,Doc)
printDafnyModules xs = do
    is <- State.gets imports
    (types,code) <- Utils.mapAndUnzipM (\(x,y) -> printDafnyModule x (Map.unions $ Map.elems y) is) xs
    return (vcat types,vcat code)

printDafnyModule :: DafnyK m => Maybe Identifier -> Map DafnyId DafnyEntry -> Map Identifier (Set Identifier) -> DafnyM m (Doc,Doc)
printDafnyModule mn xs imports = do
    let (types,rest) = Map.partitionWithKey (\k v -> isTypeDafnyId k) xs
    let cmp (_,p1,_,_,_) (_,p2,_,_,_) = compare p1 p2
    let fourth (x,y,z,w,q) = w
    let defstypes = vcat $ map fourth $ List.sortBy cmp $ Map.elems types
    let defsrest = vcat $ map fourth $ List.sortBy cmp $ Map.elems rest
    ppmn <- lift $ ppModuleName mn
    let is = case mn of
                Nothing -> []
                Just mname -> maybe [] Set.toList $ Map.lookup mname imports
    let pis = vcat $ map (\i -> text "import opened" <+> text i) ("prelude":is)
    return (defstypes,text "module" <+> ppmn <+> vbraces (pis $+$ defsrest))

resolveEntryPoint :: ProverK Position m => Identifier -> TcM m (Maybe DafnyId)
resolveEntryPoint n = do
    let n' = mkVarId n
    env <- getModuleField False id id
    mb <- case Map.lookup (PIden n') (procedures env) of
        Just (Map.toList -> [(k,e)]) -> return $ decDafnyId $ unDecT $ entryType e
        Nothing -> case Map.lookup (TIden n') (structs env) of
            Just (Map.toList -> [(k,e)]) -> return $ decDafnyId $ unDecT $ entryType e
            Nothing -> case Map.lookup (PIden n') (functions env) of
                Just (Map.toList -> [(k,e)]) -> return $ decDafnyId $ unDecT $ entryType e
                Nothing -> case Map.lookup (PIden n') (lemmas env) of
                    Just (Map.toList -> [(k,e)]) -> return $ decDafnyId $ unDecT $ entryType e
                    Nothing -> return Nothing
            otherwise -> return Nothing
        otherwise -> return Nothing
    debugTc $ liftIO $ putStrLn $ "resolveEntryPoint " ++ show n ++ " " ++ pprid mb ++ " in\n" ++ show (Map.keys $ procedures env)
    return mb

getModule :: Monad m => DafnyM m (Maybe Identifier)
getModule = State.gets currentModule

withModule :: Monad m => Maybe Identifier -> DafnyM m a -> DafnyM m a
withModule c m = do
    oldc <- getModule
    State.modify $ \env -> env { currentModule = c }
    x <- m
    State.modify $ \env -> env { currentModule = oldc }
    return x

loadDafnyId :: DafnyK m => Position -> DafnyId -> DafnyM m (Maybe DafnyId)
loadDafnyId l n = do
    e <- lookupDafnyId l n
    let dec = unDecT $ entryType e
    mb <- loadDafnyDec l dec
    case mb of
        Nothing -> lift $ debugTc $ do
            ppd <- ppr dec
            liftIO $ putStrLn $ "loadDafnyId: did not load " ++ ppd
        otherwise -> return ()
    return mb

loadDafnyDec' :: DafnyK m => Position -> DecType -> DafnyM m DafnyId
loadDafnyDec' l dec = do
    lift $ debugTc $ do
        ppd <- ppr dec
        liftIO $ putStrLn $ "loadDafnyDec': " ++ ppd
    mb <- loadDafnyDec l dec
    case mb of
        Just dec -> return dec
        Nothing -> lift $ do
            ppd <- pp dec
            genError (locpos l) $ text "loadDafnyDec'" <+> ppd

addImport :: Maybe Identifier -> Maybe Identifier -> Map Identifier (Set Identifier) -> Map Identifier (Set Identifier)
addImport (Just current) (Just mn) = Map.insertWith Set.union current (Set.singleton mn)
addImport _ _ = id

loadDafnyDec :: DafnyK m => Position -> DecType -> DafnyM m (Maybe DafnyId)
loadDafnyDec l dec = do
    --liftIO $ putStrLn $ "loadDafnyDec: " ++ ppr dec
    current <- getModule
    case decDafnyIds dec of
        Just fid@(bid,did,targs) -> do
            let mn = dafnyIdModule did
            unless (current==mn) $ State.modify $ \env -> env { imports = addImport current mn (imports env) }
            withModule mn $ do
                leakMode <- getLeakMode
                docs <- State.gets (Map.map (Map.filterWithKey (\did v -> leakMode >= dafnyIdLeak did)) . dafnies)
                case Map.lookup mn docs of
                    Just bids -> case Map.lookup bid bids of
                        Just dids -> case Map.lookup did dids of
                            Just (_,_,did',_,_) -> return $ Just did'
                            Nothing -> do
                                lift $ debugTc $ do
                                    ppdid <- pp did
                                    ppdids <- liftM (sepBy space) $ mapM pp (Map.keys dids)
                                    liftIO $ putStrLn $ "failed to lookup dafny id " ++ show ppdid ++ " in " ++ show ppdids
                                mb <- findEntry (decPos dec) (Map.toList dids) fid dec
                                case mb of
                                    Just entry@(_,_,did',_,_) -> do
                                        State.modify $ \env -> env { dafnies = Map.update (Just . Map.update (Just . Map.insert did entry) bid) mn $ dafnies env }
                                        return $ Just did'
                                    Nothing -> newEntry l dec fid
                        Nothing -> do
                            lift $ debugTc $ do
                                ppbid <- pp bid
                                ppbids <- liftM (sepBy space) $ mapM pp (Map.keys bids)
                                liftIO $ putStrLn $ "failed to lookup base id " ++ show ppbid ++ " in " ++ show ppbids
                            newEntry l dec fid
                    Nothing -> newEntry l dec fid
        Nothing -> do
            lift $ debugTc $ liftIO $ putStrLn $ "no ids for dec"
            return Nothing
                   
findEntry :: DafnyK m => Position -> [(DafnyId,DafnyEntry)] -> (DafnyId,DafnyId,[Type]) -> DecType -> DafnyM m (Maybe DafnyEntry)
findEntry l [] fid dec = do
    lift $ debugTc $ do
        ppid <- pp fid
        liftIO $ putStrLn $ "cannot find entry for " ++ show ppid
    return Nothing
findEntry l ((did',(ts',p',uid',doc',dec')):es) fid@(bid,did,ts) dec = do
    same <- lift $ tryTcErrorBool l $ sameTemplateDecs l dec dec'
    if same
        then return $ Just (ts,p',uid',doc',dec)
        else do
            ok <- lift $ tryTcErrorBool l $ equalsList l ts' ts
            if ok
                then return $ Just (ts,p',uid',empty,dec')
                else do
                    lift $ debugTc $ do
                        ppdid' <- ppr did'
                        ppdid <- ppr did
                        liftIO $ putStrLn $ "entries do not match: " ++ ppdid' ++ ppdid
                    findEntry l es fid dec

newEntry :: DafnyK m => Position -> DecType -> (DafnyId,DafnyId,[Type]) -> DafnyM m (Maybe DafnyId)
newEntry l dec fid@(bid,did,ts) = do
    let mn = dafnyIdModule bid
    State.modify $ \env -> env { dafnies = Map.alter (Just . Map.alter (Just . Map.insert did (ts,noloc,did,empty,dec) . maybe Map.empty id) bid . maybe Map.empty id) mn $ dafnies env }
    mb <- decToDafny l dec
    case mb of
        Nothing -> do
            State.modify $ \env -> env { dafnies = Map.update (Just . Map.update (Just . Map.delete bid) bid) mn $ dafnies env }
            lift $ debugTc $ do
                ppfid <- ppr fid
                liftIO $ putStrLn $ "failed to add new entry " ++ ppfid
            return Nothing
        Just (p,doc) -> do
            State.modify $ \env -> env { dafnies = Map.update (Just . Map.update (Just . Map.insert did (ts,p,did,doc,dec)) bid) mn $ dafnies env }
            lift $ debugTc $ do
                ppfid <- ppr fid
                liftIO $ putStrLn $ "added new entry " ++ ppfid
            return $ Just did
            

lookupDafnyId :: DafnyK m => Position -> DafnyId -> DafnyM m EntryEnv
lookupDafnyId l did@(SId sn tid@(ModuleTyVarId  m _)) = do
    ss <- lift $ getEntry (Just sn) tid TKind False
    case ss of
        Nothing -> do
            ppdid <- lift $ pp did
            genError l $ text "lookupDafnyId: can't find struct" <+> ppdid
        Just e -> return e
lookupDafnyId l did@(AId tid@(ModuleTyVarId m _) isLeak) = do
    as <- lift $ getEntry Nothing tid AKind False
    case as of
        Just e -> return e
        Nothing -> do
            ppdid <- lift $ pp did
            genError l $ text "lookupDafnyId: can't find axiom" <+> ppdid
lookupDafnyId l did@(PId pn tid@(ModuleTyVarId m _)) = do
    ss <- lift $ getEntry (Just pn) tid PKind False
    case ss of
        Nothing -> do
            ppdid <- lift $ pp did
            genError l $ text "lookupDafnyId: can't find procedure" <+> ppdid
        Just e -> return e
lookupDafnyId l did@(LId pn tid@(ModuleTyVarId m _) isLeak) = do
    ss <- lift $ getEntry (Just pn) tid LKind False
    case ss of
        Nothing -> do
            ppdid <- lift $ pp did
            genError l $ text "lookupDafnyId: can't find lemma" <+> ppdid
        Just e -> return e
lookupDafnyId l did@(FId pn tid@(ModuleTyVarId m _) isLeak) = do
    ss <- lift $ getEntry (Just pn) tid FKind False
    case ss of
        Nothing -> do
            ppdid <- lift $ pp did
            genError l $ text "lookupDafnyId: can't find function" <+> ppdid
        Just e -> return e

emptyDec (DecType tid _ [] (emptyDecCtx->True) (emptyDecCtx->True) _ t) = Just (tid,t)
emptyDec d = Nothing

targsDec (DecType tid _ ts (emptyDecCtx->True) (emptyDecCtx->True) _ t) = Just (tid,ts,t)
targsDec d = Nothing

emptyDecCtx (DecCtx _ dict frees) = dict==emptyPureTDict && noNormalFrees frees

pIdenToDafnyId :: PIdentifier -> ModuleTyVarId -> DafnyId
pIdenToDafnyId (PIden n) mid = PId (PIden n) mid
pIdenToDafnyId (OIden n) mid = PId (OIden $ funit n) mid

fIdenToDafnyId :: PIdentifier -> ModuleTyVarId -> Bool -> DafnyId
fIdenToDafnyId (PIden n) mid isLeak = FId (PIden n) mid isLeak
fIdenToDafnyId (OIden n) mid isLeak = FId (OIden $ funit n) mid isLeak

addAnnsCond :: Doc -> AnnsDoc -> AnnsDoc
addAnnsCond c anns = map add anns
    where
    add ann@(ReadsK,_,_,_,_) = ann
    add (x,y,z,w,q) = (x,y,z,c <+> text "==>" <+> parens w,q)

-- to work around the fact that Dafny does not allow inputs to be mutated
newDafnyArgs :: DafnyK m => [(Bool,Var,IsVariadic)] -> DafnyM m (AnnsDoc,Doc,TSubsts)
newDafnyArgs xs = do
    (anns,xs',ss) <- Utils.mapAndUnzip3M newDafnyArg xs
    return (concat anns,vcat xs',mconcat ss)

newDafnyArg :: DafnyK m => (Bool,Var,IsVariadic) -> DafnyM m (AnnsDoc,Doc,TSubsts)
newDafnyArg (isConst,VarName t v@(VIden vv),isVariadic) = do
    (pt,ptanns) <- typeToDafny noloc StmtK t
    let (anns,ptanns') = annLines StmtK ptanns
    v'@(VIden vv') <- lift $ genVar v
    pv <- varToDafny $ VarName (Typed noloc t) v
    pv' <- varToDafny $ VarName (Typed noloc t) v'
    let pdecl = text "var" <+> pv' <+> text ":" <+> pt <> semicolon
    let pass = pv' <+> text ":=" <+> pv <> semicolon
    return (anns,pdecl $+$ ptanns' $+$ pass,TSubsts $ Map.singleton vv $ IdxT $ varExpr $ VarName t v')

decToDafny :: DafnyK m => Position -> DecType -> DafnyM m (Maybe (Position,Doc))
decToDafny l dec@(emptyDec -> Just (mid,ProcType p pn args ret anns (Just body) cl)) = withAssumptions $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    ppn <- ppDafnyIdM did
    (pargs,parganns) <- procedureArgsToDafny l False args
    (parganns',pargs',ssargs) <- newDafnyArgs args
    (pret,pretanns,anns',body') <- case ret of
        ComplexT Void -> return (empty,[],anns,body ++ [ReturnStatement (Typed l ret) Nothing])
        ComplexT ct -> do
            result <- lift $ liftM (VarName (ComplexT ct)) $ genVar (VIden $ mkVarId $ "result_"++show ppn)
            let ssres = TSubsts $ Map.singleton (mkVarId "\\result") (IdxT $ varExpr result)
            anns' <- lift $ substFromTSubstsNoDec "procedureToDafny" p ssres False Map.empty anns
            body' <- lift $ substFromTSubstsNoDec "procedureToDafny" p ssargs False Map.empty body
            (pret,pretanns) <- procedureArgsToDafny l True [(False,result,False)]
            return (text "returns" <+> pret,pretanns,anns',body')
        otherwise -> do
            ppret <- lift $ pp ret
            genError p $ text "procedureToDafny: unsupported return type" <+> ppret
    pcl <- decClassToDafny cl
    panns <- procedureAnnsToDafny anns'
    (annb,pbody) <- statementToDafny $ compoundStmt (decPos dec) body'
    let tag = text "method"
    lift $ debugTc $ do
        ppdec <- ppr dec
        ppdid <- ppDafnyId did
        liftIO $ putStrLn $ "decToDafny " ++ show ppdid ++ " " ++ ppdec
    let anns' = parganns ++ parganns' ++ pretanns ++ panns ++annb
    annframes <- propagateDafnyAssumptions p EnsureK (decClassReads cl) (decClassWrites cl)
    return $ Just (p,tag <+> ppn <+> pargs <+> pret $+$ pcl $+$ annLinesProcC annframes $+$ annLinesProcC anns' $+$ pargs' $+$ pbody)
  where did = pIdenToDafnyId pn mid
decToDafny l dec@(emptyDec -> Just (mid,FunType isLeak p pn args ret anns (Just body) cl)) = withAssumptions $ withLeakMode isLeak $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    ppn <- ppDafnyIdM did
    pvars <- liftM (parens . sepBy comma) $ mapM (varToDafny . fmap (Typed l) . snd3) args
    let result = ppn <+> pvars
    withResult result $ do
        (pargs,parganns) <- procedureArgsToDafny l False args
        (pret,pretanns) <- typeToDafny l RequireK ret
        pcl <- decClassToDafny cl
        panns <- procedureAnnsToDafny anns
        (pbodyanns,pbody) <- expressionToDafny False Nothing RequireK body
        let fanns = unfreeAnns $ pretanns ++ parganns ++ panns ++ pbodyanns
        let tag = if isLeak then text "function" else text "function method"
        return $ Just (p,tag <+> ppn <+> pargs <+> char ':' <+> pret $+$ pcl $+$ annLinesProcC fanns $+$ vbraces pbody)
  where did = fIdenToDafnyId pn mid isLeak
decToDafny l dec@(emptyDec -> Just (mid,LemmaType isLeak p pn args anns body cl)) = withAssumptions $ withLeakMode isLeak $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    ppn <- ppDafnyIdM did
    (pargs,parganns) <- procedureArgsToDafny l False args
    (parganns',pargs',ssargs) <- newDafnyArgs args
    body' <- lift $ substFromTSubstsNoDec "procedureToDafny" p ssargs False Map.empty body
    pcl <- decClassToDafny cl
    panns <- procedureAnnsToDafny anns
    (annsb,pbody) <- case body' of 
        Just ss -> do
            (annsb,pss) <- statementToDafny $ compoundStmt noloc ss
            return (annsb,vbraces pss)
        Nothing -> return ([],empty)
    let anns' = parganns++parganns'++panns++annsb
    return $ Just (p,text "lemma" <+> ppn <+> pargs $+$ annLinesProcC anns' $+$ pargs' $+$ pbody)
  where did = LId (funit pn) mid isLeak
decToDafny l (emptyDec -> Just (mid,StructType p sn (Just atts) cl)) = withLeakMode False $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    psn <- ppDafnyIdM did
    patts <- structAttsToDafny l psn atts
    return $ Just (p,text "datatype" <+> psn <+> char '=' <+> psn <> parens patts)
  where did = SId sn mid
decToDafny l d@(targsDec -> Just (mid,targs,AxiomType isLeak p args anns cl)) = withAssumptions $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    leakMode <- getLeakMode
    if (leakMode >= isLeak)
        then do
            ptargs <- typeArgsToDafny l targs
            (pargs,parganns) <- procedureArgsToDafny l False args
            panns <- procedureAnnsToDafny anns
            pn <- ppDafnyIdM did
            State.modify $ \env -> env { axiomIds = Set.insert did $ axiomIds env }
            return $ Just (p,text "lemma" <+> pn <+> ptargs <+> pargs $+$ annLinesProcC panns $+$ annLinesProcC parganns)
        else return Nothing
  where did = AId mid isLeak
decToDafny l dec = do
    lift $ debugTc $ do
        ppdec <- ppr dec
        liftIO $ putStrLn $ "decToDafny: " ++ ppdec
    return Nothing

decClassToDafny :: DafnyK m => DecClass -> DafnyM m Doc
decClassToDafny (DecClass _ _ rs ws) = do
    let ppVar (v,(t,_)) = varToDafny $ VarName (Typed noloc t) $ VIden v
    prs <- mapM ppVar $ Map.toList (Map.filter snd $ fst rs)
    pws <- mapM ppVar $ Map.toList (Map.filter snd $ fst ws)
    let pr = if null prs then empty else text "reads" <+> sepBy space prs
    let pw = if null pws then empty else text "modifies" <+> sepBy space pws
    return $ pr $+$ pw

structAttsToDafny :: DafnyK m => Position -> Doc -> [Attr] -> DafnyM m Doc
structAttsToDafny l sn = liftM (sepBy comma) . (mapM (structAttToDafny l True sn . attributeName))

structAttToDafny :: DafnyK m => Position -> Bool -> Doc -> AttributeName GIdentifier Type -> DafnyM m Doc
structAttToDafny l withType sn (AttributeName t n) = do
    pv <- varToDafny $ VarName (Typed noloc t) n
    pt <- if withType
        then liftM (char ':' <>) (liftM fst $ typeToDafny l NoK t)
        else return empty
    return $ sn <> char '_' <> pv <> pt

typeArgsToDafny :: DafnyK m => Position -> [(Constrained Var,IsVariadic)] -> DafnyM m Doc
typeArgsToDafny l xs = do
    pxs <- mapM (typeArgToDafny l) xs
    let pxs' = catMaybes pxs
    let pxs'' = if null pxs' then empty else abrackets (sepBy comma pxs')
    return pxs''

typeArgToDafny :: DafnyK m => Position -> (Constrained Var,IsVariadic) -> DafnyM m (Maybe Doc)
typeArgToDafny l cv@(Constrained v Nothing,False) = case typeClass "targ" (loc v) of
    (isType -> True) -> liftM Just $ dafnyGIdM (varNameId v) -- there is a slight mismatch here: SecreC only supports base types while Dafny supports any type
    (isKind -> True) -> return Nothing
    (isDomain -> True) -> return Nothing
    otherwise -> do
        ppcv <- lift $ pp cv
        genError l $ text "typeArgToDafny:" <+> ppcv 

procedureArgsToDafny :: DafnyK m => Position -> Bool -> [(Bool,Var,IsVariadic)] -> DafnyM m (Doc,AnnsDoc)
procedureArgsToDafny l isPost xs = do
    (vs,as) <- Utils.mapAndUnzipM (procedureArgToDafny l isPost) xs
    return (parens $ sepBy comma vs,concat as)

procedureArgToDafny :: DafnyK m => Position -> Bool -> (Bool,Var,IsVariadic) -> DafnyM m (Doc,AnnsDoc)
procedureArgToDafny l isPost (_,v,False) = do
    vs <- lift $ usedVs' v
    let annK = if isPost then EnsureK else RequireK
    pv <- varToDafny $ fmap (Typed noloc) v
    (pt,annt) <- typeToDafny l annK (loc v)
    annp <- genDafnyAssumptions l False annK vs pv (loc v)
    return (pv <> char ':' <> pt,annp ++ annt)
procedureArgToDafny l isPost (_,v,True) = do
    ppv <- lift $ pp v
    genError l $ text "procedureArgToDafny:" <+> ppv <> text "..."

dafnyUint64 :: Doc -> Doc
dafnyUint64 x = parens x <+> text "as uint64"

dafnySize n x = if n > 1
    then x <> text ".size()"
    else dafnyUint64 (char '|' <> x <> char '|') 

dafnyShape n x = if n > 1
    then x <> text ".shape()"
    else brackets (dafnyUint64 (char '|' <> x <> char '|'))

qualifiedDafny :: DafnyK m => Position -> Type -> Doc -> DafnyM m Doc
qualifiedDafny l t x = do
    (pt,annst) <- typeToDafny l NoK t
    return $ parens (parens (text "x" <> char ':' <> pt) <+> text "=>" <+> text "x") <> parens x

genDafnyAssumptions :: DafnyK m => Position -> Bool -> AnnKind -> Set VarIdentifier -> Doc -> Type -> DafnyM m AnnsDoc
genDafnyAssumptions l hasLeak annK vs pv tv = do
    anns1 <- genDafnyArrays l annK vs pv tv
    anns2 <- genDafnyPublics l hasLeak annK vs pv tv
    return (anns1++anns2)

genDafnyArrays :: DafnyK m => Position -> AnnKind -> Set VarIdentifier -> Doc -> Type -> DafnyM m AnnsDoc
genDafnyArrays l annK vs pv tv = do
    case tv of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            case mbd of
                Right n@((>1) -> True) -> do
                    inD <- getInDecl
                    readarr <- case inD of
                        Nothing -> return []
                        Just (PId {}) -> return []
                        Just (LId {}) -> return []
                        Just (AId {}) -> return []
                        otherwise -> do
                            ann1 <- annExpr (Just False) False False ReadsK vs (pv <> text "`arr" <> int (fromEnum n))
                            ann2 <- annExpr (Just False) False False ReadsK vs (pv <> text ".arr" <> int (fromEnum n))
                            return (ann1++ann2)
                    notnull <- annExpr (Just False) False False annK vs (pv <+> text "!= null &&" <+> pv <> text ".valid()")
                    return $ readarr++notnull
                otherwise -> return []
        otherwise -> return []

propagateDafnyAssumptions :: DafnyK m => Position -> AnnKind -> DecClassVars -> DecClassVars -> DafnyM m AnnsDoc
propagateDafnyAssumptions p annK (rs,_) (ws,_) = do
    let untouched = Map.toList $ Map.map fst $ Map.difference rs ws
    frames <- genDafnyFrames p annK untouched
    invs <- genDafnyInvariantAssumptions p annK untouched
    return (frames++invs)

-- propagate untouched asumptions into post-conditions or invariants
genDafnyInvariantAssumptions :: DafnyK m => Position -> AnnKind -> [(VarIdentifier,Type)] -> DafnyM m AnnsDoc
genDafnyInvariantAssumptions p annK xs = do
    anns <- getAssumptions
    concatMapM propagate $ filter isUntouched anns
  where
    isUntouched (_,_,vs,_,_) = Set.null $ Set.difference vs (Set.fromList $ map fst xs)
    propagate (_,_,vs,pe,isLeak) = annExpr (Just False) isLeak isLeak annK vs pe

-- generate a frame condition for every untouched variable
genDafnyFrames :: DafnyK m => Position -> AnnKind -> [(VarIdentifier,Type)] -> DafnyM m AnnsDoc
genDafnyFrames p annK xs = concatMapM (genDafnyFrame p annK) xs
    where
    genDafnyFrame p annK (v,t) = do
        pv <- varToDafny $ VarName (Typed p t) (VIden v)
        annExpr (Just False) False False annK (Set.singleton v) (pv <+> text "==" <+> text "old" <> parens pv)

genDafnyPublics :: DafnyK m => Position -> Bool -> AnnKind -> Set VarIdentifier -> Doc -> Type -> DafnyM m AnnsDoc
genDafnyPublics l True annK vs pv tv = return []
genDafnyPublics l False annK vs pv tv = whenLeakMode $ do
    d <- getInDecl
    if isLeakageInDecl d
        then do
            let publick = case annK of
                            StmtK -> "PublicMid"
                            InvariantK -> "PublicMid"
                            EnsureK -> "PublicOut"
                            RequireK -> "PublicIn"
                            NoK -> "PublicMid"
            -- only generate publics for primitive types
            let genPublic t@(BaseT {}) = annExpr (Just False) True True annK vs (text publick <> parens pv)
                genPublic t@(ComplexT (CType s b d)) | isPublicSecType s && isPrimBaseType b = annExpr (Just False) True True annK vs (text publick <> parens pv)
                genPublic t = return []
            -- only generate public sizes for private types
            let genPublicSize t@(ComplexT (CType s b d)) | not (isPublicSecType s) = do
                    mb <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
                    case mb of
                        Right 0 -> return []
                        Right 1 -> do
                            let psize = dafnySize 1 pv
                            annExpr (Just False) True True annK vs (text publick <> parens psize)
                        Right n -> do
                            let pshape = dafnyShape n pv
                            annExpr (Just False) True True annK vs (text publick <> parens pshape)
                        otherwise -> do
                            ppt <- lift $ pp t
                            genError l $ text "genPublicSize:" <+> pv <+> ppt
                genPublicSize t = return []
            ispublic <- genPublic tv
            publicsize <- genPublicSize tv
            return $ ispublic ++ publicsize
        else return []
    
isLeakageInDecl :: Maybe DafnyId -> Bool
isLeakageInDecl Nothing = False
isLeakageInDecl (Just (PId {})) = True
isLeakageInDecl (Just (AId _ isLeak)) = isLeak
isLeakageInDecl (Just (SId {})) = False
isLeakageInDecl (Just (FId _ _ isLeak)) = isLeak
isLeakageInDecl (Just (LId _ _ isLeak)) = isLeak
    
annLine :: AnnDoc -> Doc
annLine (EnsureK,isFree,vs,x,isLeak) = ppIsFree isFree (text "ensures") (ppLeakageFun isLeak x) <> semicolon
annLine (RequireK,isFree,vs,x,isLeak) = ppIsFree isFree (text "requires") (ppLeakageFun isLeak x) <> semicolon
annLine (StmtK,Just _,vs,x,isLeak) = text "assume" <+> ppLeakageAtt isLeak <+> x <> semicolon
annLine (StmtK,Nothing,vs,x,isLeak) = text "assert" <+> ppLeakageAtt isLeak <+> x <> semicolon
annLine (InvariantK,isFree,vs,x,isLeak) = ppIsFree isFree (text "invariant") (ppLeakageFun isLeak x) <> semicolon
annLine (DecreaseK,isFree,vs,x,isLeak) = text "decreases" <+> x <> semicolon
annLine (ReadsK,_,vs,x,isLeak) = text "reads" <+> x <> semicolon
annLine (NoK,isFree,vs,x,isLeak) = ppIsFree (fmap (const True) isFree) empty x

ppIsFree :: Maybe Bool -> Doc -> Doc -> Doc
ppIsFree Nothing c d = c <+> d
ppIsFree (Just False) c d = ppFree True (c <+> d)
ppIsFree (Just True) c d = c <+> (ppFreeFun True d)

ppLeakageAtt :: IsLeak -> Doc
ppLeakageAtt False = empty
ppLeakageAtt True = text "{:leakage}"

ppLeakageFun :: IsLeak -> Doc -> Doc
ppLeakageFun False d = d
ppLeakageFun True d = text "Leakage" <> parens d

ppFreeFun :: IsLeak -> Doc -> Doc
ppFreeFun False d = d
ppFreeFun True d = text "Free" <> parens d

unfreeAnn :: AnnDoc -> AnnDoc
unfreeAnn (k,isFree,vs,x,isLeak) = (k,fmap (const True) isFree,vs,x,isLeak)

unfreeAnns :: AnnsDoc -> AnnsDoc
unfreeAnns = map unfreeAnn

data AnnKindClass = ExprKC | StmtKC | ProcKC
  deriving (Eq,Ord,Show)

annKindClass :: AnnKind -> AnnKindClass
annKindClass EnsureK = ProcKC
annKindClass RequireK = ProcKC
annKindClass StmtK = StmtKC
annKindClass InvariantK = StmtKC
annKindClass DecreaseK = ProcKC
annKindClass ReadsK = ProcKC
annKindClass NoK = ExprKC

annLines :: AnnKind -> AnnsDoc -> (AnnsDoc,Doc)
annLines c anns = annLinesC (annKindClass c) anns

-- the input boolean determines if we are in a procedure context or not
-- if not in a procedure context, we postpone procedure annotations
annLinesC :: AnnKindClass -> AnnsDoc -> (AnnsDoc,Doc)
annLinesC cl anns = (anns',vcat $ map annLine xs)
    where (anns',xs) = List.partition ((>cl) . annKindClass . fst5) anns

annLinesProcC :: AnnsDoc -> Doc
annLinesProcC anns = d
    where
    (reads,anns') = List.partition ((==ReadsK) . fst5) anns
    anns'' = List.nub anns'
    reads' = Set.fromList $ map fou5 reads
    readk = case Set.toList reads' of
                [] -> []
                xs -> [(ReadsK,Just False,Set.empty,PP.sepBy PP.comma xs,False)]
    ([],d) = annLinesC ProcKC (readk++anns'')

procedureAnnsToDafny :: DafnyK m => [ProcedureAnnotation GIdentifier (Typed Position)] -> DafnyM m AnnsDoc
procedureAnnsToDafny xs = liftM concat $ mapM (procedureAnnToDafny) xs

procedureAnnToDafny :: DafnyK m => ProcedureAnnotation GIdentifier (Typed Position) -> DafnyM m AnnsDoc
procedureAnnToDafny (RequiresAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing RequireK e
        req <- annExpr (boolIsFree isFree) isLeak leakMode RequireK vs pe
        return $ anne ++ req
procedureAnnToDafny (EnsuresAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing EnsureK e
        ens <- annExpr (boolIsFree isFree) isLeak leakMode EnsureK vs pe
        return $ anne ++ ens
procedureAnnToDafny (InlineAnn l isInline) = withInAnn True $ return []
procedureAnnToDafny (PDecreasesAnn l e) = withInAnn True $ do
    leakMode <- getLeakMode
    vs <- lift $ usedVs' e
    (anne,pe) <- expressionToDafny False Nothing EnsureK e
    decr <- annExpr Nothing False leakMode DecreaseK vs pe
    return $ anne ++ decr

statementsToDafny :: DafnyK m => [Statement GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,Doc)
statementsToDafny ss = do
    (anns,docs) <- Utils.mapAndUnzipM statementToDafny ss
    return (concat anns,vcat docs)

addAnnsC :: DafnyK m => AnnKindClass -> AnnsDoc -> Doc -> DafnyM m (AnnsDoc,Doc)
addAnnsC c anns doc = do
    let (anns1,anns2) = annLinesC c anns
    return (anns1,anns2 $+$ doc)

statementToDafny :: DafnyK m => Statement GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,Doc)
statementToDafny (CompoundStatement _ ss) = do
    (anns,pss) <- statementsToDafny ss
    return (anns,vbraces pss)
statementToDafny (IfStatement _ c s1 s2) = do
    (ann1,pc) <- expressionToDafny False Nothing StmtK c
    (annthen,ps1) <- withAssumptions $ statementToDafny s1
    (concat -> annelse,ps2) <- withAssumptions $ Utils.mapAndUnzipM statementToDafny s2
    let annthen' = addAnnsCond pc annthen
    let annelse' = addAnnsCond (char '!' <> parens pc) annelse
    ppo <- ppOpt ps2 (return . (text "else" <+>))
    addAnnsC StmtKC (ann1++annthen'++annelse') $ text "if" <+> pc <+> ps1 $+$ ppo
statementToDafny (BreakStatement l) = return ([],text "break" <> semicolon)
statementToDafny (ContinueStatement l) = return ([],text "continue" <> semicolon)
statementToDafny (ReturnStatement l e) = do
    (anne,pe) <- mapExpressionToDafny False Nothing StmtK e
    addAnnsC StmtKC anne $ text "return" <+> ppid pe <> semicolon
statementToDafny (ExpressionStatement _ (BinaryAssign l le (BinaryAssignEqual _) re)) = do
    (pres,pre) <- expressionToDafny False Nothing StmtK re
    leftvs <- lift $ usedVs' le    
    (post,pass) <- dropAssumptions leftvs $ assignmentToDafny StmtK le (Left pre)
    let (anns1,pres') = annLinesC StmtKC pres
    let (anns2,post') = annLinesC StmtKC post
    return (anns1++anns2,pres' $+$ pass <> semicolon $+$ post')
statementToDafny es@(ExpressionStatement (Typed l _) e) = do
    let t = typed $ loc e
    case t of
        ComplexT Void -> do
            (anne,pe) <- expressionToDafny False Nothing StmtK e
            let ppe = if (pe==empty) then pe else pe <> semicolon
            addAnnsC StmtKC anne ppe
        otherwise -> do
            let tl = Typed l (StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void)
            eres <- lift $ liftM (VarName (Typed l t)) $ genVar (VIden $ mkVarId "eres")
            t' <- lift $ type2TypeSpecifierNonVoid l t
            let edef = VarStatement tl $ VariableDeclaration tl False True t' $ WrapNe $ VariableInitialization tl eres Nothing (Just e)
            statementToDafny edef
statementToDafny (AssertStatement l e) = do
    leakMode <- getLeakMode
    vs <- lift $ usedVs' e
    (anne,pe) <- expressionToDafny False Nothing StmtK e
    assert <- annExpr Nothing False leakMode StmtK vs pe
    addAnnsC StmtKC (anne++assert) empty
statementToDafny (AnnStatement l ss) = withInAnn True $ do
    anns <- concatMapM statementAnnToDafny ss
    addAnnsC StmtKC anns empty
statementToDafny (VarStatement l (VariableDeclaration _ isConst isHavoc t vs)) = do
    (t',annst) <- typeToDafny (unTyped $ loc t) StmtK (typed $ loc t)
    (concat -> anns,vcat -> pvd) <- Utils.mapAndUnzipM (varInitToDafny isConst isHavoc t') $ Foldable.toList vs
    addAnnsC StmtKC (annst++anns) pvd
statementToDafny (WhileStatement (Typed l (WhileT rs ws)) e anns s) = withAssumptions $ do
    annframes <- propagateDafnyAssumptions l InvariantK rs ws
    (anne,pe) <- expressionToDafny False Nothing InvariantK e
    annl <- loopAnnsToDafny anns
    let (annw,annl') = annLinesC StmtKC annl
    (ann2,ps) <- statementToDafny s
    (anns,pw) <- addAnnsC StmtKC (anne++annw++ann2) $ annl' $+$ vbraces ps
    return (anns,text "while" <+> pe $+$ annLinesProcC annframes $+$ pw)
statementToDafny (SyscallStatement l n params) = do
    (concat -> ss,concat -> params') <- lift $ runSimplify $ Utils.mapAndUnzipM simplifySyscallParameter params
    (anns1,pss) <- statementsToDafny ss
    (anns2,psys) <- syscallToDafny (unTyped l) n params'
    addAnnsC StmtKC (anns1++anns2) (pss $+$ psys)
statementToDafny s = do
    pps <- lift $ pp s
    genError (unTyped $ loc s) $ text "statementToDafny:" <+> pps

loopAnnsToDafny :: DafnyK m => [LoopAnnotation GIdentifier (Typed Position)] -> DafnyM m AnnsDoc
loopAnnsToDafny xs = withInAnn True $ liftM concat $ mapM loopAnnToDafny xs

--supersedesAssumption :: AnnDoc -> AnnDoc -> Bool
--supersedesAssumption (annK1,isFree1,vs1,e1,isLeak1) (annK2,isFree2,vs2,e2,isLeak2) =
--    e1 == e2 && supersedesAnnKind annK1 annK2
--supersedesAnnKind :: AnnKind -> AnnKind -> Bool
--supersedesAnnKind _ InvariantK = False
--supersedesAnnKind _ EnsureK = False
--supersedesAnnKind x y = x == y

addAssumptions :: DafnyK m => DafnyM m AnnsDoc -> DafnyM m AnnsDoc
addAssumptions m = do
--    ass <- getAssumptions
    anns <- m
    -- if there is any assumption bigger than @x@, drop x
    --let (rest,anns') = List.partition (\x -> any (flip supersedesAssumption x) ass) anns
    --lift $ debugTc $ liftIO $ putStrLn $ show $ text "dropped assumptions" <+> annLinesProcC rest $+$ text "because of" <> annLinesProcC anns
    State.modify $ \env -> env { assumptions = assumptions env ++ anns }
    return anns

annExpr :: DafnyK m => Maybe Bool -> Bool -> Bool -> AnnKind -> Set VarIdentifier -> Doc -> DafnyM m AnnsDoc
annExpr isFree isLeak leakMode annK vs e = addAssumptions $ do
    case (leakMode,isLeak) of
        (True,True) -> return [(annK,isFree,vs,e,isLeak)]
        (True,False) -> return [(annK,Just False,vs,e,isLeak)]
        (False,True) -> return []
        (False,False) -> return [(annK,isFree,vs,e,isLeak)]
    
loopAnnToDafny :: DafnyK m => LoopAnnotation GIdentifier (Typed Position) -> DafnyM m AnnsDoc
loopAnnToDafny (DecreasesAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing InvariantK e
        decrease <- annExpr Nothing isLeak leakMode DecreaseK vs pe
        return $ anne ++ decrease
loopAnnToDafny (InvariantAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing InvariantK e
        inv <- annExpr (boolIsFree isFree) isLeak leakMode InvariantK vs pe
        return $ anne ++ inv

boolIsFree :: Bool -> Maybe Bool
boolIsFree False = Nothing
boolIsFree True = Just False

statementAnnToDafny :: DafnyK m => StatementAnnotation GIdentifier (Typed Position) -> DafnyM m AnnsDoc
statementAnnToDafny (AssumeAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing StmtK e
        assume <- annExpr (Just False) isLeak leakMode StmtK vs pe
        return (anne++assume)
statementAnnToDafny (AssertAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing StmtK e
        assert <- annExpr Nothing isLeak leakMode StmtK vs pe
        return (anne++assert)
statementAnnToDafny (EmbedAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift $ usedVs' e
        (anns,ann) <- statementToDafny e
        call <- annExpr Nothing isLeak leakMode NoK vs ann
        return $ anns++call

-- checks that a dafny expression has a given shape
checkDafnyShape :: DafnyK m => Position -> Maybe Bool -> Set VarIdentifier -> Sizes GIdentifier (Typed Position) -> Doc -> DafnyM m AnnsDoc
checkDafnyShape l isFree vs (Sizes szs) e = case Foldable.toList szs of
    [] -> return []
    (ds@(all (not . snd) -> True)) -> do
        (anns,des) <- Utils.mapAndUnzipM (expressionToDafny False Nothing StmtK) (map fst ds)
        let check = case des of
                        [de] -> dafnySize 0 e <+> text "==" <+> de
                        des -> e <> text ".shape()" <+> text "==" <+> brackets (sepBy comma des)
        return $ concat anns ++ [(StmtK,isFree,vs,check,False)]
    otherwise -> do
        ppszs <- lift $ pp (Sizes szs)
        ppe <- lift $ pp e
        genError l $ text "checkDafnyShape: unsupported array size" <+> ppszs <+> text "for" <+> ppe
    
varInitToDafny :: DafnyK m => Bool -> Bool -> Doc -> VariableInitialization GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,Doc)
varInitToDafny isConst False pty vd@(VariableInitialization l v sz (Just e)) = do
    ppvd <- lift $ pp vd
    genError (unTyped l) $ text "varInitToDafny: cannot convert default expression at" <+> ppvd
varInitToDafny isConst isHavoc pty (VariableInitialization l v sz ini) = do
    vs <- lift $ usedVs' (v,sz)
    vvs <- lift $ usedVs' v
    pv <- varToDafny v
    let def = text "var" <+> pv <> char ':' <> pty <> semicolon
    annp <- genDafnyAssumptions (unTyped $ loc v) False StmtK vvs pv (typed $ loc v)
    (annsini,pini) <- mapExpressionToDafny False Nothing StmtK ini
    annsize <- case (sz) of
        (Just szs) -> do
            let isFree = if isJust ini then Nothing else Just False
            checkDafnyShape (unTyped l) isFree vs szs pv
        otherwise -> return []
    assign <- ppOpt pini (\e -> return $ pv <+> text ":=" <+> e <+> semicolon)
    let (anns1,annsini') = annLinesC StmtKC annsini
    let (anns2,annsize') = annLinesC StmtKC $ annp ++ annsize
    lift $ debugTc $ liftIO $ putStrLn $ "varInitToDafny: " ++ show annsini' ++ "\n" ++ show pv ++ "\n" ++ show annsize'
    return (anns1++anns2,def $+$ annsini' $+$ assign $+$ annsize')

typeToDafny :: DafnyK m => Position -> AnnKind -> Type -> DafnyM m (Doc,AnnsDoc)
typeToDafny l annK (BaseT b) = baseTypeToDafny l annK b
typeToDafny l annK (ComplexT t) = complexTypeToDafny l annK t
typeToDafny l annK t = do
    ppt <- lift $ pp t
    genError l $ text "typeToDafny:" <+> ppt

baseTypeToDafny :: DafnyK m => Position -> AnnKind -> BaseType -> DafnyM m (Doc,AnnsDoc)
baseTypeToDafny l annK (BVar v _) = liftM (,[]) $ dafnyGIdM $ VIden v
baseTypeToDafny l annK (TyPrim prim) = liftM (,[]) $ lift $ pp prim
baseTypeToDafny l annK (MSet b) = do
    (b',anns) <- complexTypeToDafny l annK b
    return (text "multiset" <> abrackets b',anns)
baseTypeToDafny l annK (Set b) = do
    (b',anns) <- complexTypeToDafny l annK b
    return (text "set" <> abrackets b',anns)
baseTypeToDafny l annK (TApp _ args dec@(decTypeTyVarId -> Just mid)) = do
    did <- loadDafnyDec' l dec
    psn <- ppDafnyIdM did
    let ppArg (t,False) = typeToDafny l annK t
        ppArg (t,True) = do
            ppt <- lift $ pp t
            genError l $ text "baseTypeToDafny: variadic argument" <+> ppt
    (args',anns) <- Utils.mapAndUnzipM ppArg args
    let pargs = if null args' then empty else abrackets $ sepBy comma args'
    return (psn <> pargs,concat anns)
--baseTypeToDafny t = genError noloc $ text "baseTypeToDafny:" <+> pp t

complexTypeToDafny :: DafnyK m => Position -> AnnKind -> ComplexType -> DafnyM m (Doc,AnnsDoc)
complexTypeToDafny l annK t@(CType s b d) = do
    (pb,annsb) <- baseTypeToDafny l annK b
    mb <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
    case mb of
        Right 0 -> return (pb,annsb)
        -- uni-dimensional arrays as sequences
        Right 1 -> return (text "seq" <> abrackets pb,annsb)
        -- multi-dimensional arrays as Dafny's fixed-length multi-dimensional arrays wrapped inside a class
        Right n -> return (text "Array" <> int (fromEnum n) <> abrackets pb,annsb)
        Left err -> do
            ppt <- lift $ pp t
            throwError $ GenericError l (text "complexTypeToDafny:" <+> ppt) $ Just err
complexTypeToDafny l annK t = do
    ppt <- lift $ pp t
    genError l $ text "complexTypeToDafny:" <+> ppt

data AnnKind = StmtK | EnsureK | RequireK | InvariantK | DecreaseK | NoK | ReadsK
  deriving (Show,Eq)
instance Monad m => PP m AnnKind where
    pp = return . text . show

type AnnsDoc = [AnnDoc]
-- (kind,isFree (Nothing=not free,Just False=not inlined,Just True=inlined),used variables,dafny expression)
type AnnDoc = (AnnKind,Maybe Bool,Set VarIdentifier,Doc,IsLeak)

indexToDafny :: DafnyK m => Bool -> AnnKind -> Maybe Doc -> Int -> Index GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,Doc)
indexToDafny isLVal annK isClass i (IndexInt l e) = do
    (anne,pe) <- expressionToDafny isLVal Nothing annK e
    return (anne,pe)
indexToDafny isLVal annK Nothing i (IndexSlice l e1 e2) = do
    (anne1,pe1) <- mapExpressionToDafny isLVal Nothing annK e1
    (anne2,pe2) <- mapExpressionToDafny isLVal Nothing annK e2
    return (anne1++anne2,ppid pe1 <> text ".." <> ppid pe2)
indexToDafny isLVal annK (Just pe) i (IndexSlice l e1 e2) = do
    (anne1,pe1) <- mapExpressionToDafny isLVal Nothing annK e1
    let pe1' = maybe (int 0) id pe1
    (anne2,pe2) <- mapExpressionToDafny isLVal Nothing annK e2
    let pe2' = maybe (pe <> text ".Length" <> int i <> text "()") id pe2
    return (anne1++anne2,pe1' <> text "," <> pe2')

-- left = expression, right = update
assignmentToDafny :: DafnyK m => AnnKind -> Expression GIdentifier (Typed Position) -> Either Doc Doc -> DafnyM m (AnnsDoc,Doc)
assignmentToDafny annK se@(SelectionExpr l e att) (Left pre) = do
    did <- tAttDec (unTyped $ loc e) (pp se) (typed $ loc e)
    psn <- ppDafnyIdM did
    patt <- structAttToDafny (unTyped l) False psn $ fmap typed att
    (annse,_) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ char '.' <> parens (patt <+> text ":=" <+> pre))
    return (annse++ann,doc)
assignmentToDafny annK se@(SelectionExpr l e att) (Right upd) = do
    did <- tAttDec (unTyped $ loc e) (pp se) (typed $ loc e)
    psn <- ppDafnyIdM did
    patt <- structAttToDafny (unTyped l) False psn $ fmap typed att
    (annse,pse) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ char '.' <> parens (patt <+> text ":=" <+> pse <> upd))
    return (annse++ann,doc)
assignmentToDafny annK se@(PostIndexExpr l e (Foldable.toList -> [i])) (Left pre) = do
    (anni,pi) <- indexToDafny True annK Nothing 0 i
    (annse,_) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ brackets (text "int" <> parens pi <+> text ":=" <+> pre))
    return (anni++annse++ann,doc)
assignmentToDafny annK se@(PostIndexExpr l e (Foldable.toList -> [i])) (Right upd) = do
    (anni,pi) <- indexToDafny True annK Nothing 0 i
    (annse,pse) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ brackets (text "int" <> parens pi <+> text ":=" <+> pse <> upd))
    return (anni++annse++ann,doc)
assignmentToDafny annK e@(RVariablePExpr {}) (Left pre) = do
    (anne,pe) <- expressionToDafny True Nothing annK e
    return (anne,pe <+> text ":=" <+> pre)
assignmentToDafny annK e@(RVariablePExpr {}) (Right upd) = do
    (anne,pe) <- expressionToDafny True Nothing annK e
    return (anne,pe <+> text ":=" <+> pe <> upd)
assignmentToDafny annK e pre = do
    ppannK <- lift $ pp annK
    ppe <- lift $ pp e
    pppre <- lift $ pp pre
    genError (unTyped $ loc e) $ text "assignmentToDafny:" <+> ppannK <+> ppe <+> pppre

tAttDec :: DafnyK m => Position -> TcM m Doc -> Type -> DafnyM m DafnyId
tAttDec l ppe t@(BaseT (TApp _ _ d)) = do
    did <- loadDafnyDec' l d
    return did
tAttDec l ppe t@(ComplexT (CType Public b d)) = do
    mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
    case mbd of
        Right 0 -> tAttDec l ppe (BaseT b)
        otherwise -> do
            ppl <- lift $ pp l
            ppt <- lift $ pp t
            pe <- lift $ ppe
            genError l $ text "tAttDec:" <+> ppl <+> text "unsupported complex type" <+> ppt <+> text "in expression" <+> pe
tAttDec l ppe t = do
    ppl <- lift $ pp l
    ppt <- lift $ pp t
    pe <- lift $ ppe
    genError l $ text "tAttDec:" <+> ppl <+> text "unsupported type" <+> ppt <+> text "in expression" <+> pe

hasLeakExpr :: Expression GIdentifier (Typed Position) -> Bool
hasLeakExpr = everything (||) (mkQ False aux)
    where
    aux :: Expression GIdentifier (Typed Position) -> Bool
    aux (LeakExpr {}) = True
    aux _ = False

projectionToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Expression GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,Doc)
projectionToDafny isLVal isQExpr annK se@(PostIndexExpr l e (Foldable.toList -> is)) = do
    vs <- lift $ usedVs' se
    (anne,pe) <- expressionToDafny isLVal Nothing annK e
    let Typed _ t = loc e
    mbd <- lift $ tryTcError l $ typeDim l t >>= fullyEvaluateIndexExpr l
    case (mbd,is) of
        (Right 1,[i]) -> do
            (anne,pe) <- expressionToDafny isLVal Nothing annK e
            (anni,pi) <- indexToDafny isLVal annK Nothing 0 i
            let pse = pe <> brackets pi
            annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr se) annK vs pse (typed l)
            qExprToDafny isQExpr (anne++anni++annp) pse
        (Right n,is) -> do
            (anne,pe) <- expressionToDafny isLVal Nothing annK e
            (concat -> annis,pis) <- Utils.mapAndUnzipM (\(idx,i) -> indexToDafny isLVal annK (Just pe) i idx) (zip is [0..])
            let pse = pe <> text ".project" <> ppIndexIds is <> parens (sepBy comma pis)
            annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr se) annK vs pse (typed l)
            qExprToDafny isQExpr (anne++annis++annp) pse
        otherwise -> do
            ppannK <- lift $ pp annK
            ppe <- lift $ pp e
            ppis <- lift $ liftM (sepBy comma) $ mapM pp is
            genError (unTyped $ loc e) $ text "projectionToDafny:" <+> ppid isLVal <+> ppannK <+> ppe <> brackets ppis

ppIndexIds :: [Index iden loc] -> Doc
ppIndexIds [] = empty
ppIndexIds (IndexInt {}:xs) = int 0 <> ppIndexIds xs
ppIndexIds (IndexSlice {}:xs) = int 1 <> ppIndexIds xs

type IsQExpr = Maybe (Set VarIdentifier)

expressionToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Expression GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,Doc)
expressionToDafny isLVal isQExpr annK se@(PostIndexExpr {}) = do
    projectionToDafny isLVal isQExpr annK se
expressionToDafny isLVal isQExpr annK se@(SelectionExpr l e att) = do
    vs <- lift $ usedVs' se
    (anne,pe) <- expressionToDafny isLVal Nothing annK e
    did <- tAttDec (unTyped $ loc e) (pp se) (typed $ loc e)
    psn <- ppDafnyIdM did
    patt <- structAttToDafny (unTyped l) False psn $ fmap typed att
    let pse = pe <> char '.' <> patt
    annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr se) annK vs pse (typed l)
    -- always assert equality of projection, if it is a base type, since we don't do so when declaring the struct variable
    qExprToDafny isQExpr (anne++annp) pse
expressionToDafny isLVal isQExpr annK e@(RVariablePExpr l v) = do
    vs <- lift $ usedVs' e
    pv <- varToDafny v
    annp <- genDafnyAssumptions (unTyped $ loc v) (hasLeakExpr e) annK vs pv (typed $ loc v)
    qExprToDafny isQExpr annp pv
expressionToDafny isLVal isQExpr annK le@(LitPExpr l lit) = do
    (anns,pe) <- literalToDafny annK lit
    qExprToDafny isQExpr anns pe
expressionToDafny isLVal isQExpr annK le@(LeakExpr l e) = do
    (anne,pe) <- expressionToDafny False Nothing annK e
    leakMode <- getLeakMode
    if leakMode
        then qExprToDafny isQExpr anne (text "Leak" <> parens pe)
        else qExprToDafny isQExpr anne (text "true")
expressionToDafny isLVal isQExpr annK (QualExpr l e _) = do
    expressionToDafny isLVal isQExpr annK e
expressionToDafny isLVal isQExpr annK e@(MultisetConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let pme = text "multiset" <> braces (sepBy comma pes)
    pme' <- if List.null pes then qualifiedDafny (unTyped l) (typed l) pme else return pme
    qExprToDafny isQExpr annes pme'
expressionToDafny isLVal isQExpr annK e@(SetConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let pme = braces (sepBy comma pes)
    pme' <- if List.null pes then qualifiedDafny (unTyped l) (typed l) pme else return pme
    qExprToDafny isQExpr annes pme'
expressionToDafny isLVal isQExpr annK e@(ArrayConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let Typed ll arrt = l
    mbd <- lift $ tryTcError l $ typeDim l arrt >>= fullyEvaluateIndexExpr l
    case mbd of
        Right 1 -> do
            let pae = brackets (sepBy comma pes)
            pae' <- if List.null pes then qualifiedDafny ll (typed l) pae else return pae
            qExprToDafny isQExpr annes pae'
        --Right n -> do
        --    when (isLVal && isQExpr) $ genError l $ text "expressionToDafny: unsupported array constructor in an expression context" <+> ppe
        --    x <- lift $ genVar (VIden $ mkVarId "x" :: GIdentifier)
        --    px <- varToDafny $ VarName (Typed ll arrt) x
        --    let ss = px <+> text ":= new Array" <> int (fromEnum n) <> ".reshape1" <> parens ()
        --    return (annes++ss,px)
        otherwise -> do
            ppe <- lift $ pp e
            genError ll $ text "expressionToDafny: unsupported array constructor" <+> ppe
expressionToDafny isLVal isQExpr annK me@(ToMultisetExpr l e) = do
    vs <- lift $ usedVs' me
    (anne,pe) <- expressionToDafny False Nothing annK e
    let pme = text "multiset" <> parens pe
    annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr me) annK vs pme (typed l)
    qExprToDafny isQExpr (anne++annp) pme
expressionToDafny isLVal isQExpr annK me@(ToSetExpr l e) = do
    let ll = unTyped l
    vs <- lift $ usedVs' me
    let te = typed $ loc e
    case te of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ typeDim l te >>= fullyEvaluateIndexExpr l
            case mbd of
                Right 1 -> do
                    let bt = ComplexT $ CType s b $ indexExpr 0
                    (pbt,annbt) <- typeToDafny (unTyped l) annK bt
                    (anne,pe) <- expressionToDafny False Nothing annK e
                    x <- lift $ genVar (VIden $ mkVarId "xset" :: GIdentifier)
                    px <- varToDafny $ VarName (Typed ll bt) x
                    let pme = parens (text "set" <+> px <> char ':' <> pbt <+> char '|' <+> px <+> text "in" <+> pe)
                    annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr me) annK vs pme (typed l)
                    qExprToDafny isQExpr (annbt++anne++annp) pme
                Right n -> do
                    x <- lift $ genVar (VIden $ mkVarId "iset" :: GIdentifier)
                    let vx = VarName (Typed (unTyped l) $ BaseT uint64) x
                    px <- varToDafny vx
                    (anne,pe) <- expressionToDafny False Nothing annK e
                    let idxs = fromListNe [IndexInt l (varExpr vx),IndexSlice l Nothing Nothing]
                    (annproj,proje) <- projectionToDafny isLVal isQExpr annK $ PostIndexExpr l e idxs
                    let pme = parens (text "set" <+> px <> char ':' <> text "uint64" <+> char '|' <+> px <+> text "<" <+> parens (dafnyShape n pe <> brackets (int 0)) <+> text "::" <+> proje)
                    annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr me) annK vs pme (typed l)
                    qExprToDafny isQExpr (annproj++anne++annp) pme
                otherwise -> do
                    ppme <- lift $ pp me
                    genError ll $ text "expressionToDafny: unsupported set expression" <+> ppme

--projectionToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Expression GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,Doc)
--projectionToDafny isLVal isQExpr annK se@(PostIndexExpr l e (Foldable.toList -> is))
                    
expressionToDafny isLVal isQExpr annK be@(BuiltinExpr l n es) = do
    es' <- lift $ concatMapM unfoldVariadicExpr es
    builtinToDafny isLVal isQExpr annK l n es'
expressionToDafny isLVal isQExpr annK e@(ProcCallExpr l (ProcedureName (Typed _ (DecT dec)) n) targs args) = do
    vs <- lift $ usedVs' e
    -- try to inline all lemma calls
    mb <- return Nothing --lift $ tryInlineLemmaCall (unTyped l) e
    case mb of
        Nothing -> do -- do not inline normal call
            did <- loadDafnyDec' (unTyped l) dec
            (annargs,pargs) <- procCallArgsToDafny isLVal annK args
            pn <- ppDafnyIdM did
            let pe = pn <> parens (sepBy comma pargs)
            annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr e || not (isFunType $ DecT dec)) annK vs pe (typed l)
            qExprToDafny isQExpr (annargs++annp) pe
        --Just (mbdec,ss) -> do
        --    -- load the lemma separately (to check its body)
        --    mapM_ (loadDafnyDec' (unTyped l)) mbdec
        --    -- inline the lemma call without its body
        --    anns <- mapM statementAnnToDafny ss
        --    return (concat anns,empty)
expressionToDafny isLVal isQExpr annK e@(BinaryExpr l e1 op@(loc -> (Typed _ (DecT dec))) e2) = do
    vs <- lift $ usedVs' e
    did <- loadDafnyDec' (unTyped l) dec
    (annargs,pargs) <- procCallArgsToDafny isLVal annK [(e1,False),(e2,False)]
    pn <- ppDafnyIdM did
    let pe = pn <> parens (sepBy comma pargs)
    annp <- genDafnyAssumptions (unTyped l) (hasLeakExpr e || not (isFunType $ DecT dec)) annK vs pe (typed l)
    qExprToDafny isQExpr (annargs++annp) pe
expressionToDafny isLVal isQExpr annK qe@(QuantifiedExpr l q args e) = do
    let pq = quantifierToDafny q
    (annpargs,pargs) <- quantifierArgsToDafny annK args
    vs <- lift $ liftM Set.unions $ mapM usedVs' args
    (anne,pe) <- expressionToDafny isLVal (Just vs) annK e
    let (anns,pe') = annotateExpr (annpargs++anne) vs pe
    lift $ debugTc $ do
        liftIO $ putStrLn $ "quantifierExprToDafny " ++ show vs ++ "\n" ++ show pe ++ "\n --> \n" ++ show pe'
    return (anns,parens (pq <+> pargs <+> text "::" <+> pe'))
expressionToDafny isLVal isQExpr annK me@(SetComprehensionExpr l t x px fx) = do
    (annarg,parg) <- quantifierArgToDafny annK (t,x)
    vs <- lift $ usedVs' (t,x)
    (annpe,pppx) <- expressionToDafny isLVal (Just vs) annK px
    (annfe,pfx) <- mapExpressionToDafny isLVal (Just vs) annK fx
    ppfx <- ppOpt pfx (liftM (text "::" <+>) . pp)
    let (anns,pppx') = annotateExpr (annarg++annpe++annfe) vs pppx
    let pme = parens (text "set" <+> parg <+> char '|' <+> pppx' <+> ppfx)
    return (anns,pme)
expressionToDafny isLVal isQExpr annK ce@(CondExpr l econd ethen eelse) = do
    (anncond,ppcond) <- expressionToDafny isLVal isQExpr annK econd
    (annthen,ppthen) <- expressionToDafny isLVal isQExpr annK ethen
    (annelse,ppelse) <- expressionToDafny isLVal isQExpr annK eelse
    let annthen' = addAnnsCond ppcond annthen
    let annelse' = addAnnsCond (char '!' <> parens ppcond) annelse
    return (anncond++annthen'++annelse',text "if" <+> ppcond <+> text "then" <+> ppthen <+> text "else" <+> ppelse)
expressionToDafny isLVal isQExpr annK e@(ResultExpr l) = do
    mb <- getResult
    case mb of
        Just result -> return ([],result)
        otherwise -> do
            ppannK <- lift $ pp annK
            ppe <- lift $ pp e
            genError (unTyped $ loc e) $ text "expressionToDafny:" <+> ppid isLVal <+> ppannK <+> ppe
expressionToDafny isLVal isQExpr annK e = do
    ppannK <- lift $ pp annK
    ppe <- lift $ pp e
    genError (unTyped $ loc e) $ text "expressionToDafny:" <+> ppid isLVal <+> ppannK <+> ppe

qExprToDafny :: DafnyK m => IsQExpr -> AnnsDoc -> Doc -> DafnyM m (AnnsDoc,Doc)
qExprToDafny (Just vs) anne e = return $ annotateExpr anne vs e
qExprToDafny Nothing anne e = return (anne,e)

annotateExpr :: AnnsDoc -> Set VarIdentifier -> Doc -> (AnnsDoc,Doc)
annotateExpr anne vs pe = (anne',pppre (pppost pe))
    where
    pppre = maybe id (\p x -> parens (p <+> text "==>" <+> x)) (ands pre)
    pppost = maybe id (\p x -> parens (p <+> text "&&" <+> x)) (ands post)
    (deps,anne') = List.partition (\(k,_,evs,_,_) -> k /= ReadsK && not (Set.null $ Set.intersection evs vs)) anne
    (map fou5 -> pre,map fou5 -> post) = List.partition (isJust . snd5) deps
    ands [] = Nothing
    ands (x:xs) = case ands xs of
        Nothing -> Just x
        Just ys -> Just $ parens (x <+> text "&&" <+> ys)

quantifierToDafny :: Quantifier (Typed Position) -> Doc
quantifierToDafny (ForallQ _) = text "forall"
quantifierToDafny (ExistsQ _) = text "exists"

quantifierArgsToDafny :: DafnyK m => AnnKind -> [(TypeSpecifier GIdentifier (Typed Position),VarName GIdentifier (Typed Position))] -> DafnyM m (AnnsDoc,Doc)
quantifierArgsToDafny annK xs = do
    (anns,vs) <- Utils.mapAndUnzipM (quantifierArgToDafny annK) xs
    return (concat anns,sepBy comma vs)

quantifierArgToDafny :: DafnyK m => AnnKind -> (TypeSpecifier GIdentifier (Typed Position),VarName GIdentifier (Typed Position)) -> DafnyM m (AnnsDoc,Doc)
quantifierArgToDafny annK (t,v) = do
    pv <- varToDafny v
    (pt,anns) <- typeToDafny (unTyped $ loc v) annK (typed $ loc v)
    return (anns,pv <> char ':' <> pt)

expressionsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression GIdentifier (Typed Position)) -> DafnyM m (AnnsDoc,[Doc])
expressionsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (expressionToDafny isLVal Nothing annK) $ Foldable.toList es
    return (concat annes,es')

mapExpressionToDafny :: (Functor f,Traversable f,Foldable f,DafnyK m) => Bool -> IsQExpr -> AnnKind -> f (Expression GIdentifier (Typed Position)) -> DafnyM m (AnnsDoc,f Doc)
mapExpressionToDafny isLVal isQExpr annK es = do
    rs <- mapM (expressionToDafny isLVal isQExpr annK) es
    return (concat $ Foldable.toList $ fmap fst rs,fmap snd rs)

procCallArgsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression GIdentifier (Typed Position),IsVariadic) -> DafnyM m (AnnsDoc,[Doc])
procCallArgsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (procCallArgToDafny isLVal annK) $ Foldable.toList es
    return (concat annes,es')
    
procCallArgToDafny :: DafnyK m => Bool -> AnnKind -> (Expression GIdentifier (Typed Position),IsVariadic) -> DafnyM m (AnnsDoc,Doc)
procCallArgToDafny isLVal annK (e,False) = expressionToDafny isLVal Nothing annK e
procCallArgToDafny isLVal annK (e,True) = do
    ppe <- lift $ pp e
    genError (unTyped $ loc e) $ text "unsupported variadic procedure argument" <+> ppe

sysParamsToDafny :: [SyscallParameter GIdentifier (Typed Position)] -> Maybe ([Expression GIdentifier (Typed Position)],VarName GIdentifier (Typed Position))
sysParamsToDafny xs | not (null xs) && all ispush (init xs) && isret (last xs) = Just (map unpush $ init xs,unret $ last xs)
    where
    ispush (SyscallPush _ (x,False)) = True
    ispush _ = False
    isret (SyscallReturn {}) = True
    isret _ = False
    unpush (SyscallPush _ (x,False)) = x
    unret (SyscallReturn _ ret) = ret
sysParamsToDafny params = Nothing

syscallToDafny :: DafnyK m => Position -> String -> [SyscallParameter GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,Doc)
syscallToDafny l "core.cat" (sysParamsToDafny -> Just ([x,y,n],ret)) = do
    (annx,px) <- expressionToDafny False Nothing StmtK x
    (anny,py) <- expressionToDafny False Nothing StmtK y
    let tx = typed $ loc x
    case tx of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            mbn <- lift $ tryTcError l $ fullyEvaluateIndexExpr l $ fmap typed n
            case (mbd,mbn) of
                (Right 1,Right 0) -> do
                    pret <- varToDafny ret
                    (annse,pe) <- qExprToDafny Nothing (annx++anny) (parens $ px <+> char '+' <+> py)
                    addAnnsC StmtKC annse $ pret <+> text ":=" <+> pe <> semi
                (Right d,Right n) -> do
                    pret <- varToDafny ret
                    (annse,pe) <- qExprToDafny Nothing (annx++anny) (parens $ px <+> char '+' <+> py)
                    addAnnsC StmtKC annse $ pret <+> text ":=" <+> text "new Array" <> int (fromEnum d) <> text ".cat" <> int (fromEnum n) <> parens (px <> comma <> py) <> semi
                (err1,err2) -> do
                    ppx <- lift $ pp x
                    ppy <- lift $ pp y
                    ppn <- lift $ pp n
                    genError (locpos l) $ text "syscallToDafny: unsupported cat dimension" <+> ppx <+> ppy <+> ppn <+> vcat (map ppid $ lefts [err1,err2])
        otherwise -> do
            ppx <- lift $ pp x
            ppy <- lift $ pp y
            ppn <- lift $ pp n
            pptx <- lift $ pp tx
            genError l $ text "syscallToDafny: unsupported cat type" <+> ppx <+> ppy <+> ppn <+> pptx
syscallToDafny l "core.reshape" (sysParamsToDafny -> Just ((x:szs),ret)) = do
    (annx,px) <- expressionToDafny False Nothing StmtK x
    (concat -> annszs,pszs) <- Utils.mapAndUnzipM (expressionToDafny False Nothing StmtK) szs
    pret <- varToDafny ret
    let tx = typed $ loc x
    let tret = typed $ loc ret
    mbdx <- lift $ tryTcError l $ typeDim l tx >>= fullyEvaluateIndexExpr l
    mbdret <- lift $ tryTcError l $ typeDim l tret >>= fullyEvaluateIndexExpr l
    case (mbdx,mbdret) of
        (Right dx,Right d@((>1) -> True)) -> do
            return (annszs,pret <+> text ":=" <+> text "new Array" <> int (fromEnum d) <> text ".reshape" <> int (fromEnum dx) <> parens (px <> comma <> sepBy comma pszs) <> semi)
        otherwise -> do
            ppx <- lift $ pp x
            pptx <- lift $ pp tx
            ppret <- lift $ pp ret
            pptret <- lift $ pp tret
            ppszs <- lift $ pp szs
            let errs = lefts [mbdx,mbdret]
            genError l $ text "syscallToDafny: unsupported reshape type" <+> ppx <+> text "::" <+> pptx <+> int (length szs) <+> ppszs <+> ppret <+> text "::" <+> pptret $+$ vcat (map ppid errs)
syscallToDafny l n params = do
    ppn <- lift $ pp n
    ppparams <- lift $ liftM (sepBy comma) $ mapM pp params
    genError l $ text "syscallToDafny: unexpected" <+> ppn <+> ppparams

builtinToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Typed Position -> String -> [Expression GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,Doc)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.eq" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "==" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.neq" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "!=" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.band" [x,y] = do
    (annx,px) <- expressionToDafny isLVal isQExpr annK x
    (anny,py) <- expressionToDafny isLVal isQExpr annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "&&" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.bor" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "||" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.lt" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "<" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.le" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "<=" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.gt" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text ">" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.ge" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text ">=" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.implies" [x,y] = do
    (annx,px) <- expressionToDafny isLVal isQExpr annK x
    (anny,py) <- expressionToDafny isLVal isQExpr annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "==>" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.subset" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "<=" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.in" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "in" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.union" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "+" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.add" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "+" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.sum" [xs] = do
    (pret,annpret) <- typeToDafny l annK ret
    (annxs,pxs) <- expressionToDafny isLVal Nothing annK xs
    qExprToDafny isQExpr (annpret++annxs) (parens $ text "sum_" <> pret <> parens pxs)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.sub" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "-" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.mul" [x,y] = do
    (pt,annt) <- lift (typeBase l ret) >>= typeToDafny l annK
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    mbd <- lift $ tryTcError l $ typeDim l ret >>= fullyEvaluateIndexExpr l
    case mbd of
        Right 0 -> qExprToDafny isQExpr (annt++annx++anny) (parens $ px <+> text "*" <+> py)
        Right n -> qExprToDafny isQExpr (annt++annx++anny) (text "mul" <> int (fromEnum n) <> char '_' <> pt <> parens (px <> comma <> py))
        otherwise -> do
            ppret <- lift $ pp ret
            genError (locpos l) $ text "builtinToDafny: unsupported mul dimension for" <+> ppret
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.div" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (parens $ px <+> text "/" <+> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.declassify" [x] = do -- we ignore security types
    vs <- lift $ usedVs' x
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    leakMode <- getLeakMode
    inAnn <- getInAnn
    if leakMode && not inAnn
        then do
            assert <- annExpr Nothing True True annK vs (text "DeclassifiedIn" <> parens px)
            qExprToDafny isQExpr (annx++assert) px
        else qExprToDafny isQExpr annx px
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.classify" [x] = do -- we ignore security types
    expressionToDafny isLVal Nothing annK x
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.reclassify" [x] = do -- we ignore security types
    vs <- lift $ usedVs' x
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    leakMode <- getLeakMode
    inAnn <- getInAnn
    isPub <- lift $ liftM isJust $ tryTcErrorMaybe l $ isPublic l False ret
    if leakMode && not inAnn && isPub
        then do
            assert <- annExpr Nothing True True annK vs (text "DeclassifiedIn" <> parens px)
            qExprToDafny isQExpr (annx++assert) px
        else qExprToDafny isQExpr annx px
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.cat" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    let tx = typed $ loc x
    case tx of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            case (mbd) of
                (Right 1) -> qExprToDafny isQExpr (annx++anny) (parens $ px <+> char '+' <+> py)
                (err1) -> do
                    ppx <- lift $ pp x
                    ppy <- lift $ pp y
                    genError (locpos l) $ text "builtinToDafny: unsupported cat dimension" <+> ppx <+> ppy <+> vcat (map ppid $ lefts [err1])
        otherwise -> do
            ppx <- lift $ pp x
            ppy <- lift $ pp y
            pptx <- lift $ pp tx
            genError l $ text "builtinToDafny: unsupported cat type" <+> ppx <+> ppy <+> pptx
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.size" [x] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    let tx = typed $ loc x
    case tx of
        BaseT b -> qExprToDafny isQExpr (annx) (dafnySize 0 px)
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            case mbd of
                Right n -> qExprToDafny isQExpr (annx) $ dafnySize n px
                otherwise -> do
                    ppx <- lift $ pp x
                    pptx <- lift $ pp tx
                    genError l $ text "builtinToDafny: unknown size" <+> ppx <+> pptx
        otherwise -> do
            ppx <- lift $ pp x
            pptx <- lift $ pp tx
            genError l $ text "builtinToDafny: unknown size" <+> ppx <+> pptx
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.shape" [x] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    let tx = typed $ loc x
    case tx of
        BaseT b -> qExprToDafny isQExpr (annx) (brackets empty)
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            case mbd of
                Right 0 -> qExprToDafny isQExpr (annx) $ brackets empty
                Right n -> qExprToDafny isQExpr (annx) $ dafnyShape n px
                otherwise -> do
                    ppx <- lift $ pp x
                    pptx <- lift $ pp tx
                    genError l $ text "builtinToDafny: unknown shape" <+> ppx <+> pptx
        otherwise -> do
            ppx <- lift $ pp x
            pptx <- lift $ pp tx
            genError l $ text "builtinToDafny: unknown shape" <+> ppx <+> pptx
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.repeat" [x,sz] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (annsz,psz) <- expressionToDafny isLVal Nothing annK sz
    qExprToDafny isQExpr (annx++annsz) (text "Repeat" <> parens (px <> comma <> psz))
builtinToDafny isLVal isQExpr annK (Typed l ret) n es = do
    ppannK <- lift $ pp annK
    ppret <- lift $ pp ret
    ppn <- lift $ pp n
    ppes <- lift $ pp es
    genError l $ text "builtinToDafny: unexpected" <+> ppannK <+> ppret <+> ppn <+> ppes

literalToDafny :: DafnyK m => AnnKind -> Literal (Typed Position) -> DafnyM m (AnnsDoc,Doc)
literalToDafny annK lit = do
    let t = typed $ loc lit
    case t of
        ((==BaseT bool) -> True) -> return ([],ppid lit)
        ((==BaseT string) -> True) -> return ([],ppid lit)
        (isNumericType -> True) -> do
            (pt,anns) <- typeToDafny (unTyped $ loc lit) annK (typed $ loc lit)
            return (anns,pt <> parens (ppid lit))

varToDafny :: DafnyK m => VarName GIdentifier (Typed Position) -> DafnyM m Doc
varToDafny (VarName (Typed l t) n) = do
    let suffix = if isPublicType t then "Public" else "Private"
    dn <- dafnyGIdM n
    return $ dn <> text suffix

dafnyVarId :: DebugM m => VarIdentifier -> m Doc
dafnyVarId v = do
    pm <- case varIdModule v of
        Nothing -> return empty
        Just (m,blk) -> do
            ppblk <- pp blk
            return $ text m <> char '_' <> ppblk <> char '_'
    pid <- ppOpt (varIdUniq v) (\x -> liftM (char '_' <>) (pp x))
    return $ pm <> text (varIdBase v) <> pid

dafnyGId :: DebugM m => GIdentifier -> m Doc
dafnyGId (VIden vn) = dafnyVarId vn
dafnyGId (MIden vn) = dafnyVarId vn
dafnyGId (PIden vn) = dafnyVarId vn
dafnyGId (TIden vn) = dafnyVarId vn
dafnyGId (OIden on) = pp on

dafnyGIdM :: DafnyK m => GIdentifier -> DafnyM m Doc
dafnyGIdM v = lift $ dafnyGId v

instance (DebugM m) => PP m DafnyId where
    pp did = ppDafnyId did

ppDafnyId :: DebugM m => DafnyId -> m Doc
ppDafnyId (PId pn (ModuleTyVarId mn uid)) = do
    prefix <- ppModule mn
    ppn <- dafnyGId pn
    puid <- pp uid
    let suffix = text "ShadowProc"
    return $ prefix <> ppn <> puid <> suffix    
ppDafnyId (FId pn (ModuleTyVarId mn uid) isLeak) = do
    prefix <- ppModule mn
    ppn <- dafnyGId pn
    puid <- pp uid
    let suffix = if isLeak then text "ShadowFun" else text "OriginalFun"
    return $ prefix <> ppn <> puid <> suffix
ppDafnyId (LId pn (ModuleTyVarId mn uid) isLeak) = do
    prefix <- ppModule mn
    ppn <- dafnyGId pn
    puid <- pp uid
    let suffix = if isLeak then text "ShadowLemma" else text "OriginalLemma"
    return $ prefix <> ppn <> puid <> suffix
ppDafnyId (SId sn (ModuleTyVarId mn uid)) = do
    prefix <- ppModule mn
    psn <- dafnyGId sn
    puid <- pp uid
    let suffix = empty
    return $ prefix <> psn <> puid <> suffix
ppDafnyId (AId (ModuleTyVarId mn uid) isLeak) = do
    prefix <- ppModule mn
    psn <- dafnyGId $ PIden $ mkVarId "axiom"
    puid <- pp uid
    let suffix = if isLeak then text "ShadowAxiom" else text "OriginalAxiom"
    return $ prefix <> psn <> puid <> suffix

ppModuleName :: PP m VarIdentifier => Maybe (Identifier) -> m Doc
ppModuleName Nothing = return $ text "BUILTIN"
ppModuleName (Just mn) = return $ text mn

ppModule :: PP m VarIdentifier => Maybe (Identifier,TyVarId) -> m Doc
ppModule Nothing = return $ text "BUILTIN"
ppModule (Just (mn,blk)) = do
    ppblk <- pp blk
    return $ text mn <> char '_' <> ppblk

ppDafnyIdM :: DafnyK m => DafnyId -> DafnyM m Doc
ppDafnyIdM did = lift $ ppDafnyId did


