{-# LANGUAGE TupleSections, UndecidableInstances, MultiParamTypeClasses, FlexibleInstances, DeriveGeneric, DeriveDataTypeable, ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.Transformation.Dafny where

import Language.SecreC.Syntax
import Language.SecreC.Monad
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
import Control.Monad.State.Strict (StateT(..))
import qualified Control.Monad.State.Strict as State

import Safe

type DafnyK m = ProverK Position m
type DafnyM m = StateT DafnySt (TcM m)

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

dafnyIdModule :: DafnyId -> Identifier
dafnyIdModule = maybe "main" id . dafnyIdModuleMb

putDafnyIdModuleTyVarId :: ModuleTyVarId -> DafnyId -> DafnyId
putDafnyIdModuleTyVarId tid (PId po _) = PId po tid
putDafnyIdModuleTyVarId tid (FId po _ b) = FId po tid b
putDafnyIdModuleTyVarId tid (LId g _ b) = LId g tid b
putDafnyIdModuleTyVarId tid (SId g _) = SId g tid
putDafnyIdModuleTyVarId tid (AId _ isLeak) = AId tid isLeak

dafnyIdModuleMb :: DafnyId -> Maybe Identifier
dafnyIdModuleMb = fmap fst . modTyName . dafnyIdModuleTyVarId

type DafnyEntry = ([Type],Position,DafnyId,DDoc,DecType)

dropEntryDoc :: DafnyEntry -> DafnyEntry
dropEntryDoc (ts,p,did,_,dec) = (ts,p,did,dempty,dec)

data FreeMode = KeepF | FreeF | DeleteF
  deriving (Data,Typeable,Show,Eq,Ord)

data DafnySt = DafnySt {
      dafnies :: Map (Maybe Identifier) (Map DafnyId (Map DafnyId DafnyEntry)) -- generated Dafny entries (top-level variables, types, functions, methods), grouped by module, grouped by base ids
    , imports :: Map Identifier (Set Identifier)
    , leakageMode :: Bool -- True=leakage, False=correctness
    , axiomIds :: Set DafnyId
    , inDecl :: Maybe DafnyId -- decl id
    , decResult :: Maybe DDoc --result expression
    , inAnn :: Bool -- inside an annotation
    , currentModule :: Maybe Identifier
    , assumptions :: AnnsDoc
    , freeMode :: FreeMode
    , verifiedIds :: VDafnyIds -- dafny entries verified in a previous execution
    }

withFreeMode :: Monad m => FreeMode -> DafnyM m a -> DafnyM m a
withFreeMode isFree m = do
    old <- State.gets freeMode
    State.modify $ \e -> e { freeMode = isFree }
    x <- m
    State.modify $ \e -> e { freeMode = old }
    return x
    
addFreeMode :: Monad m => FreeMode -> DafnyM m a -> DafnyM m a
addFreeMode isFree m = do
    old <- State.gets freeMode
    State.modify $ \e -> e { freeMode = appendFreeMode old isFree }
    x <- m
    State.modify $ \e -> e { freeMode = old }
    return x

getAssumptions :: Monad m => DafnyM m AnnsDoc
getAssumptions = State.gets assumptions

withAssumptions :: DafnyK m => DafnyM m a -> DafnyM m a
withAssumptions m = do
    anns <- getAssumptions
    x <- m
    State.modify $ \env -> env { assumptions = anns }
    return x

resetAssumptions :: DafnyK m => DafnyM m a -> DafnyM m a
resetAssumptions m = do
    anns <- getAssumptions
    State.modify $ \env -> env { assumptions = [] }
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
insideDecl did m = do
    o <- getInDecl
    State.modify $ \env -> env { inDecl = Just did }
    vids <- State.gets verifiedIds
    lmode <- State.gets leakageMode
    let fmode = case Map.lookup did vids of
                    Nothing -> KeepF
                    Just NoneV -> KeepF
                    Just BothV -> FreeF
                    Just FuncV -> if lmode==False then FreeF else KeepF
                    Just LeakV -> if lmode==True then FreeF else KeepF
    x <- addFreeMode fmode m
    State.modify $ \env -> env { inDecl = o }
    return x

getResult :: DafnyK m => DafnyM m (Maybe DDoc)
getResult = State.gets decResult

withResult :: DafnyK m => DDoc -> DafnyM m x -> DafnyM m x
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

toDafny :: DafnyK m => FilePath -> Bool -> [DafnyId] -> VDafnyIds -> TcM m (DDoc,[String],Set DafnyId)
toDafny prelude leakMode entries vids = flip State.evalStateT (DafnySt Map.empty Map.empty leakMode Set.empty Nothing Nothing False Nothing [] KeepF vids) $ do
    dfy <- liftIO $ readFile prelude
    loadAxioms
    mapM_ (loadDafnyId noloc) entries
    ds <- State.gets (Map.toList . dafnies)
    let modules = map fst ds
    (types,code) <- printDafnyModules ds
    opts <- lift askOpts
    let code' = if noDafnyModules opts
                    then dtext dfy $$+$$ types $$+$$ code
                    else dtext "module" <<+>> dtext "prelude" <<+>> dvbraces (dtext dfy $$+$$ types) $$+$$ code
    axioms <- State.gets (Set.toList . axiomIds)
    paxioms <- mapM (boogieName modules) axioms
    dids <- State.gets (Set.unions . map Map.keysSet . Map.elems . dafnies)
    return (code',paxioms,dids)

boogieName :: DafnyK m => [Maybe Identifier] -> DafnyId -> DafnyM m String
boogieName modules did = do
    pdid <- ppDafnyIdM did
    ppmn <- lift $ ppModuleName mn
    return $ show $ dtext "_" <<>> dint mnum <<>> dtext "_" <<>> ppmn <<>> dtext ".__default." <<>> dtext (duplicateUnderscores $ show pdid)
  where
    mn = dafnyIdModuleMb did
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

printDafnyModules :: DafnyK m => [(Maybe Identifier,Map DafnyId (Map DafnyId DafnyEntry))] -> DafnyM m (DDoc,DDoc)
printDafnyModules xs = do
    is <- State.gets imports
    (types,code) <- Utils.mapAndUnzipM (\(x,y) -> printDafnyModule x (Map.unions $ Map.elems y) is) xs
    return (dvcat types,dvcat code)

printDafnyModule :: DafnyK m => Maybe Identifier -> Map DafnyId DafnyEntry -> Map Identifier (Set Identifier) -> DafnyM m (DDoc,DDoc)
printDafnyModule mn xs imports = do
    opts <- lift askOpts
    let (types,rest) = Map.partitionWithKey (\k v -> isTypeDafnyId k) xs
    let cmp (_,p1,_,_,_) (_,p2,_,_,_) = compare p1 p2
    let fourth (x,y,z,w,q) = w
    let defstypes = dvcat $ map fourth $ List.sortBy cmp $ Map.elems types
    let defsrest = dvcat $ map fourth $ List.sortBy cmp $ Map.elems rest
    ppmn <- lift $ ppModuleName mn
    lift $ debugTc $ do
        pks <- mapM ppDafnyId $ Map.keys rest
        liftIO $ putStrLn $ show $ dtext "printing dafny" <<+>> ppmn <<+>> dtext "defs" <<+>> (dsepBy pks comma)
    let is = case mn of
                Nothing -> []
                Just mname -> maybe [] Set.toList $ Map.lookup mname imports
    let pis = if noDafnyModules opts
                then dempty
                else dvcat $ map (\i -> dtext "import opened" <<+>> dtext i) ("prelude":is)
    let modu = if noDafnyModules opts
                then pis $$+$$ defsrest
                else dtext "module" <<+>> ppmn <<+>> dvbraces (pis $$+$$ defsrest)
    return (defstypes,modu)

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
    mbe <- lookupDafnyIdMb l n
    case mbe of
        Nothing -> do
            lift $ debugTc $ do
                ppn <- ppr n
                liftIO $ putStrLn $ "loadDafnyId: did not load " ++ ppn
            return Nothing
        Just e -> do
            let dec = unDecT $ entryType e
            mb <- loadDafnyDec l dec
            case mb of
                Nothing -> do
                    lift $ debugTc $ do
                        ppd <- ppr dec
                        liftIO $ putStrLn $ "loadDafnyId: did not load " ++ ppd
                    return Nothing
                Just did -> return $ Just did

lookupAndLoadDafnyDec :: DafnyK m => Position -> DecType -> DafnyM m DafnyId
lookupAndLoadDafnyDec l dec = if hasDecBody dec
    then load dec
    else case decDafnyId dec of
        Nothing -> load dec
        Just did -> do
            mb <- lookupDafnyIdMb l did
            case mb of
                Nothing -> load dec
                Just dec' -> load $ unDecT $ entryType dec'
  where
    load dec = do
        lift $ debugTc $ do
            ppd <- ppr dec
            liftIO $ putStrLn $ "lookupAndLoadDafnyDec in: " ++ ppd
        mb <- loadDafnyDec l dec
        case mb of
            Just dec -> return dec
            Nothing -> lift $ do
                ppd <- pp dec
                genError (locpos l) $ text "lookupAndLoadDafnyDec out:" <+> ppd

addImport :: Maybe Identifier -> Maybe Identifier -> Map Identifier (Set Identifier) -> Map Identifier (Set Identifier)
addImport (Just current) (Just mn) = Map.insertWith Set.union current (Set.singleton mn)
addImport _ _ = id

loadDafnyDec :: DafnyK m => Position -> DecType -> DafnyM m (Maybe DafnyId)
loadDafnyDec l dec = do
    --liftIO $ putStrLn $ "loadDafnyDec: " ++ ppr dec
    current <- getModule
    case decDafnyIds dec of
        Just fid@(bid,did,targs) -> do
            let mn = dafnyIdModuleMb bid
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
                                        State.modify $ \env -> env { dafnies = Map.update (Just . Map.update (Just . Map.insert did (dropEntryDoc entry)) bid) mn $ dafnies env }
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
                then return $ Just (ts,p',uid',dempty,dec')
                else do
                    lift $ debugTc $ do
                        ppdid' <- ppr did'
                        ppdid <- ppr did
                        liftIO $ putStrLn $ "entries do not match: " ++ ppdid' ++ ppdid
                    findEntry l es fid dec

newEntry :: DafnyK m => Position -> DecType -> (DafnyId,DafnyId,[Type]) -> DafnyM m (Maybe DafnyId)
newEntry l dec fid@(bid,did,ts) = do
    let mn = dafnyIdModuleMb bid
    State.modify $ \env -> env { dafnies = Map.alter (Just . Map.alter (Just . Map.insert did (ts,noloc,did,dempty,dec) . maybe Map.empty id) bid . maybe Map.empty id) mn $ dafnies env }
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
lookupDafnyId l did = do
    mb <- lookupDafnyIdMb l did
    case mb of
        Nothing -> do
            ppdid <- lift $ pp did
            genError l $ text "lookupDafnyId: can't find" <+> ppdid
        Just e -> return e

lookupDafnyIdMb :: DafnyK m => Position -> DafnyId -> DafnyM m (Maybe EntryEnv)
lookupDafnyIdMb l did@(SId sn tid@(ModuleTyVarId  m _)) = do
    lift $ getEntry (Just sn) tid TKind True
lookupDafnyIdMb l did@(AId tid@(ModuleTyVarId m _) isLeak) = do
    lift $ getEntry Nothing tid AKind True
lookupDafnyIdMb l did@(PId pn tid@(ModuleTyVarId m _)) = do
    lift $ getEntry (Just pn) tid PKind True
lookupDafnyIdMb l did@(LId pn tid@(ModuleTyVarId m _) isLeak) = do
    lift $ getEntry (Just pn) tid LKind True
lookupDafnyIdMb l did@(FId pn tid@(ModuleTyVarId m _) isLeak) = do
    lift $ getEntry (Just pn) tid FKind True

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

addAnnsCond :: DDoc -> AnnsDoc -> AnnsDoc
addAnnsCond c anns = map add anns
    where
    add ann@(ReadsK,_,_,_,_) = ann
    add ann@(ModifiesK,_,_,_,_) = ann
    add (x,y,z,w,q) = (x,y,z,c <<+>> dtext "==>" <<+>> dparens w,q)

-- to work around the fact that Dafny does not allow inputs to be mutated
newDafnyArgs :: DafnyK m => Position -> [(Bool,Var,IsVariadic)] -> DafnyM m ([Statement GIdentifier (Typed Position)],TSubsts)
newDafnyArgs l xs = do
    (xs',ss) <- Utils.mapAndUnzipM (newDafnyArg l) xs
    return (concat xs',mconcat ss)

newDafnyArg :: DafnyK m => Position -> (Bool,Var,IsVariadic) -> DafnyM m ([Statement GIdentifier (Typed Position)],TSubsts)
newDafnyArg l (isConst,VarName t v@(VIden vv),isVariadic) = do
    t' <- lift $ type2TypeSpecifierNonVoid l t
    v'@(VIden vv') <- lift $ genVar v
    let tv = VarName (Typed l t) v
    let tv' = VarName (Typed l t) v'
    let tl = notTyped "newArg" l
    let def = VarStatement tl $ VariableDeclaration tl False True t' $ WrapNe $ VariableInitialization tl tv' Nothing Nothing
    let ass = ExpressionStatement tl $ BinaryAssign tl (varExpr tv') (BinaryAssignEqual tl) (varExpr tv)
    annframes <- copyDafnyAssumptions l v v'
    return ([def,ass],TSubsts $ Map.singleton vv $ IdxT $ fmap typed $ varExpr tv')

decToDafny :: DafnyK m => Position -> DecType -> DafnyM m (Maybe (Position,DDoc))
decToDafny l dec@(emptyDec -> Just (mid,ProcType p pn args ret anns (Just body) cl)) = resetAssumptions $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    ppn <- ppDafnyIdM did
    (pargs,parganns) <- procedureArgsToDafny l False args
    (pargs',ssargs) <- newDafnyArgs l args
    (pret,pretanns,anns',body') <- case ret of
        ComplexT Void -> return (dempty,[],anns,body ++ [ReturnStatement (Typed l ret) Nothing])
        ComplexT ct -> do
            result <- lift $ liftM (VarName (ComplexT ct)) $ genVar (VIden $ mkVarId $ "result_"++show ppn)
            let ssres = TSubsts $ Map.singleton (mkVarId "\\result") (IdxT $ varExpr result)
            anns' <- lift $ substFromTSubstsNoDec "procedureToDafny" p ssres False Map.empty anns
            body' <- lift $ substFromTSubstsNoDec "procedureToDafny" p ssargs False Map.empty body
            (pret,pretanns) <- procedureArgsToDafny l True [(False,result,False)]
            return (dtext "returns" <<+>> pret,pretanns,anns',body')
        otherwise -> do
            ppret <- lift $ pp ret
            genError p $ text "procedureToDafny: unsupported return type" <+> ppret
    pcl <- decClassToDafny cl
    panns <- procedureAnnsToDafny anns'
    (annb,pbody) <- statementToDafny $ compoundStmt (decPos dec) (pargs'++body')
    let tag = dtext "method"
    lift $ debugTc $ do
        ppdec <- ppr dec
        ppdid <- ppDafnyId did
        liftIO $ putStrLn $ "decToDafny " ++ show ppdid ++ " " ++ ppdec
    let anns' = parganns ++ pretanns ++ panns ++annb
    annframes <- propagateDafnyAssumptions p EnsureK (decClassReads cl) (decClassWrites cl)
    return $ Just (p,tag <<+>> ppn <<+>> pargs <<+>> pret $$+$$ pcl $$+$$ annLinesProcC annframes $$+$$ annLinesProcC anns' $$+$$ pbody)
  where did = pIdenToDafnyId pn mid
decToDafny l dec@(emptyDec -> Just (mid,FunType isLeak p pn args ret anns (Just body) cl)) = resetAssumptions $ withLeakMode isLeak $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    ppn <- ppDafnyIdM did
    pvars <- liftM (dparens . flip dsepBy comma) $ mapM (varToDafny . fmap (Typed l) . snd3) args
    let result = ppn <<+>> pvars
    withResult result $ do
        (pargs,parganns) <- procedureArgsToDafny l False args
        (pret,pretanns) <- typeToDafny l RequireK ret
        pcl <- decClassToDafny cl
        panns <- procedureAnnsToDafny anns
        (pbodyanns,pbody) <- expressionToDafny False Nothing RequireK body
        let fanns = unfreeAnns $ pretanns ++ parganns ++ panns ++ pbodyanns
        let tag = if isAnnDecClass cl then dtext "function" else dtext "function method"
        return $ Just (p,tag <<+>> ppn <<+>> pargs <<+>> dchar ':' <<+>> pret $$+$$ pcl $$+$$ annLinesProcC fanns $$+$$ dvbraces pbody)
  where did = fIdenToDafnyId pn mid isLeak
decToDafny l dec@(targsDec -> Just (mid,targs,LemmaType isLeak p pn args anns (Just body) cl)) = resetAssumptions $ withLeakMode isLeak $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    ppn <- ppDafnyIdM did
    (pargs,parganns) <- procedureArgsToDafny l False args
    (pargs',ssargs) <- newDafnyArgs l args
    fmode <- State.gets freeMode
    let dropBody body = if fmode > KeepF then Nothing else body
    body' <- lift $ substFromTSubstsNoDec "procedureToDafny" p ssargs False Map.empty $ dropBody body
    pcl <- decClassToDafny cl
    ptargs <- typeArgsToDafny l targs
    panns <- procedureAnnsToDafny anns
    (annsb,pbody) <- case body' of 
        Just ss -> do
            (annsb,pss) <- statementToDafny $ compoundStmt noloc (pargs'++ss)
            return (annsb,dvbraces pss)
        Nothing -> return ([],dempty)
    let anns' = parganns++panns++annsb
    return $ Just (p,dtext "lemma" <<+>> ppn <<+>> ptargs <<+>> pargs $$+$$ annLinesProcC anns' $$+$$ pbody)
  where did = LId (funit pn) mid isLeak
decToDafny l (emptyDec -> Just (mid,StructType p sn (Just atts) cl)) = withLeakMode False $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    psn <- ppDafnyIdM did
    patts <- structAttsToDafny l psn atts
    return $ Just (p,dtext "datatype" <<+>> psn <<+>> dchar '=' <<+>> psn <<>> dparens patts)
  where did = SId sn mid
decToDafny l d@(targsDec -> Just (mid,targs,AxiomType isLeak p args anns cl)) = resetAssumptions $ insideDecl did $ withInAnn (decClassAnn cl) $ do
    leakMode <- getLeakMode
    if (leakMode >= isLeak)
        then do
            ptargs <- typeArgsToDafny l targs
            (pargs,parganns) <- procedureArgsToDafny l False args
            panns <- procedureAnnsToDafny $ dropFreeProcAnns anns
            pn <- ppDafnyIdM did
            State.modify $ \env -> env { axiomIds = Set.insert did $ axiomIds env }
            return $ Just (p,dtext "lemma" <<+>> pn <<+>> ptargs <<+>> pargs $$+$$ annLinesProcC (panns ++ parganns))
        else return Nothing
  where did = AId mid isLeak
decToDafny l dec = do
    lift $ debugTc $ do
        ppdec <- ppr dec
        liftIO $ putStrLn $ "decToDafny: " ++ ppdec
    return Nothing

dropFreeProcAnns :: [ProcedureAnnotation GIdentifier (Typed Position)] -> [ProcedureAnnotation GIdentifier (Typed Position)]
dropFreeProcAnns xs = filter (not . isFree) xs
    where
    isFree (RequiresAnn _ isFree _ _) = isFree
    isFree (EnsuresAnn _ isFree _ _) = isFree
    isFree _ = False

decClassToDafny :: DafnyK m => DecClass -> DafnyM m DDoc
decClassToDafny (DecClass _ _ rs ws) = do
    let ppVar (v,(t,_)) = varToDafny $ VarName (Typed noloc t) $ VIden v
    prs <- mapM ppVar $ Map.toList (Map.filter snd $ fst rs)
    pws <- mapM ppVar $ Map.toList (Map.filter snd $ fst ws)
    let pr = if null prs then dempty else dtext "reads" <<+>> dsepBy prs space
    let pw = if null pws then dempty else dtext "modifies" <<+>> dsepBy pws space
    return $ pr $$+$$ pw

structAttsToDafny :: DafnyK m => Position -> DDoc -> [Attr] -> DafnyM m DDoc
structAttsToDafny l sn = liftM (flip dsepBy comma) . (mapM (structAttToDafny l True sn . attributeName))

structAttToDafny :: DafnyK m => Position -> Bool -> DDoc -> AttributeName GIdentifier Type -> DafnyM m DDoc
structAttToDafny l withType sn (AttributeName t n) = do
    pv <- varToDafny $ VarName (Typed noloc t) n
    pt <- if withType
        then liftM (dchar ':' <<>>) (liftM fst $ typeToDafny l NoK t)
        else return dempty
    return $ sn <<>> dchar '_' <<>> pv <<>> pt

typeArgsToDafny :: DafnyK m => Position -> [(Constrained Var,IsVariadic)] -> DafnyM m DDoc
typeArgsToDafny l xs = do
    pxs <- mapM (typeArgToDafny l) xs
    let pxs' = catMaybes pxs
    let pxs'' = if null pxs' then dempty else dabrackets (dsepBy pxs' comma)
    return pxs''

typeArgToDafny :: DafnyK m => Position -> (Constrained Var,IsVariadic) -> DafnyM m (Maybe DDoc)
typeArgToDafny l cv@(Constrained v Nothing,False) = case typeClass "targ" (loc v) of
    (isType -> True) -> liftM Just $ return $ DIden (varNameId v) -- there is a slight mismatch here: SecreC only supports base types while Dafny supports any type
    (isKind -> True) -> return Nothing
    (isDomain -> True) -> return Nothing
    otherwise -> do
        ppcv <- lift $ pp cv
        genError l $ text "typeArgToDafny:" <+> ppcv 

procedureArgsToDafny :: DafnyK m => Position -> Bool -> [(Bool,Var,IsVariadic)] -> DafnyM m (DDoc,AnnsDoc)
procedureArgsToDafny l isPost xs = do
    (vs,as) <- Utils.mapAndUnzipM (procedureArgToDafny l isPost) xs
    return (dparens $ dsepBy vs comma,concat as)

procedureArgToDafny :: DafnyK m => Position -> Bool -> (Bool,Var,IsVariadic) -> DafnyM m (DDoc,AnnsDoc)
procedureArgToDafny l isPost (_,v,False) = do
    vs <- lift $ usedVs' v
    let annK = if isPost then EnsureK else RequireK
    pv <- varToDafny $ fmap (Typed noloc) v
    (pt,annt) <- typeToDafny l annK (loc v)
    annp <- genDafnyAssumptions l False annK vs pv (loc v)
    return (pv <<>> dchar ':' <<>> pt,annp ++ annt)
procedureArgToDafny l isPost (_,v,True) = do
    ppv <- lift $ pp v
    genError l $ text "procedureArgToDafny:" <+> ppv <> text "..."

dafnyAs :: DDoc -> DDoc -> DDoc
dafnyAs x pt = dparens x <<+>> dtext "as" <<+>> pt

dafnyUint64 :: DDoc -> DDoc
dafnyUint64 x = dafnyAs x (dtext "uint64")

dafnySize n x = if n > 1
    then x <<>> dtext ".size()"
    else dafnyUint64 (dchar '|' <<>> x <<>> dchar '|') 

dafnyShape n x = if n > 1
    then x <<>> dtext ".shape()"
    else dbrackets (dafnyUint64 (dchar '|' <<>> x <<>> dchar '|'))

qualifiedDafny :: DafnyK m => Position -> Type -> DDoc -> DafnyM m DDoc
qualifiedDafny l t x = do
    (pt,annst) <- typeToDafny l NoK t
    return $ dparens (dparens (dtext "x" <<>> dchar ':' <<>> pt) <<+>> dtext "=>" <<+>> dtext "x") <<>> dparens x

genDafnyAssumptions :: DafnyK m => Position -> Bool -> AnnKind -> Set VarIdentifier -> DDoc -> Type -> DafnyM m AnnsDoc
genDafnyAssumptions l hasLeak annK vs pv tv = do
    anns1 <- genDafnyArrays l hasLeak annK vs pv tv
    anns2 <- genDafnyPublics l hasLeak annK vs pv tv
    return (anns1++anns2)

genDafnyArrays :: DafnyK m => Position -> Bool -> AnnKind -> Set VarIdentifier -> DDoc -> Type -> DafnyM m AnnsDoc
genDafnyArrays l True annK vs pv tv = return []
genDafnyArrays l False annK vs pv tv = do
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
                            ann1 <- annExpr (Just False) Nothing False ReadsK vs (pv <<>> dtext "`arr" <<>> dint (fromEnum n))
                            ann2 <- annExpr (Just False) Nothing False ReadsK vs (pv <<>> dtext ".arr" <<>> dint (fromEnum n))
                            return (ann1++ann2)
                    notnull <- annExpr (Just False) Nothing False annK vs (pv <<+>> dtext "!= null &&" <<+>> pv <<>> dtext ".valid()")
                    return $ notnull++readarr
                otherwise -> return []
        otherwise -> return []

genDafnyArrayWrites :: DafnyK m => Position -> AnnKind -> [(VarIdentifier,Type)] -> DafnyM m AnnsDoc
genDafnyArrayWrites p annK xs = do
    concatMapM (uncurry (genDafnyArrayWrite p annK)) xs

genDafnyArrayWrite :: DafnyK m => Position -> AnnKind -> VarIdentifier -> Type -> DafnyM m AnnsDoc
genDafnyArrayWrite l annK wv wt = do
    pv <- varToDafny $ VarName (Typed noloc wt) (VIden wv)
    let vs = (Set.singleton wv)
    case wt of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            case mbd of
                Right n@((>1) -> True) -> do
                    inD <- getInDecl
                    modiarr <- case inD of
                        Nothing -> return []
                        Just (LId {}) -> return []
                        Just (AId {}) -> return []
                        otherwise -> do
                            ann2 <- annExpr (Just False) Nothing False ModifiesK vs (pv <<>> dtext ".arr" <<>> dint (fromEnum n))
                            return (ann2)
                    notnull <- annExpr (Just False) Nothing False annK vs (pv <<+>> dtext "!= null &&" <<+>> pv <<>> dtext ".valid()")
                    return $ notnull++modiarr
                otherwise -> return []
        otherwise -> return []

-- copy dafny assumptions for variable assignments
copyDafnyAssumptions :: DafnyK m => Position -> GIdentifier -> GIdentifier -> DafnyM m ()
copyDafnyAssumptions p (VIden v) (VIden v') = do
    anns <- getAssumptions
    let anns' = foldr chgVar [] anns
    State.modify $ \env -> env { assumptions = assumptions env ++ anns' }
  where
    chgDoc doc = mapDDoc (\x -> if x == VIden v then VIden v' else x) doc 
    chgVar (annk,isFree,vs,doc,isLeak) xs = if Set.member v vs
        then (annk,isFree,Set.insert v' $ Set.delete v vs,chgDoc doc,isLeak) : xs
        else xs

propagateDafnyAssumptions :: DafnyK m => Position -> AnnKind -> DecClassVars -> DecClassVars -> DafnyM m AnnsDoc
propagateDafnyAssumptions p annK (rs,_) (ws,_) = do
    let untouched = Map.toList $ Map.map fst $ Map.difference rs ws
    lift $ debugTc $ do
        ppus <- liftM (sepBy space) $ mapM (pp . fst) untouched
        liftIO $ putStrLn $ "propagateDafnyAssumptions " ++ show annK ++ " " ++ show ppus
    frames <- genDafnyFrames p annK untouched
    invs <- genDafnyInvariantAssumptions p annK untouched
    modifies <- genDafnyArrayWrites p annK (Map.toList $ Map.map fst ws)
    return (modifies++frames++invs)

-- propagate untouched asumptions into post-conditions or invariants
genDafnyInvariantAssumptions :: DafnyK m => Position -> AnnKind -> [(VarIdentifier,Type)] -> DafnyM m AnnsDoc
genDafnyInvariantAssumptions p annK xs = do
    anns <- getAssumptions
    lift $ debugTc $ do
        ppas <- ppAnnLs anns
        liftIO $ putStrLn $ "genDafnyInvariantAssumptions " ++ pprid p ++ " " ++ show ppas
    let anns' = filter isUntouched anns
    lift $ debugTc $ do
        ppas' <- ppAnnLs anns'
        liftIO $ putStrLn $ "genDafnyInvariantAssumptions " ++ pprid p ++ " " ++ show ppas'
    concatMapM propagate anns'
  where
    isUntouched (k,_,vs,_,_) = Set.null (Set.difference vs (Set.fromList $ map fst xs))
                            && List.elem k [StmtK,EnsureK,RequireK,InvariantK]
    propagate (_,_,vs,pe,isLeak) = unlessNoAssumptions annK Nothing [] $ annExpr (Just False) isLeak (isJust isLeak) annK vs pe

-- generate a frame condition for every untouched variable
genDafnyFrames :: DafnyK m => Position -> AnnKind -> [(VarIdentifier,Type)] -> DafnyM m AnnsDoc
genDafnyFrames p annK xs = concatMapM (genDafnyFrame p annK) xs
    where
    genDafnyFrame p annK (v,t) = unlessNoAssumptions annK Nothing [] $ do
        pv <- varToDafny $ VarName (Typed p t) (VIden v)
        annExpr (Just False) Nothing False annK (Set.singleton v) (pv <<+>> dtext "==" <<+>> dtext "old" <<>> dparens pv)

genDafnyPublics :: DafnyK m => Position -> Bool -> AnnKind -> Set VarIdentifier -> DDoc -> Type -> DafnyM m AnnsDoc
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
            let genPublic t@(BaseT {}) = annExpr (Just False) (Just False) True annK vs (dtext publick <<>> dparens pv)
                genPublic t@(ComplexT (CType s b d)) | isPublicSecType s && isPrimBaseType b = annExpr (Just False) (Just False) True annK vs (dtext publick <<>> dparens pv)
                genPublic t = return []
            -- only generate public sizes for private types
            let genPublicSize t@(ComplexT (CType s b d)) | not (isPublicSecType s) = do
                    mb <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
                    case mb of
                        Right 0 -> return []
                        Right 1 -> do
                            let psize = dafnySize 1 pv
                            annExpr (Just False) (Just False) True annK vs (dtext publick <<>> dparens psize)
                        Right n -> do
                            let pshape = dafnyShape n pv
                            annExpr (Just False) (Just False) True annK vs (dtext publick <<>> dparens pshape)
                        otherwise -> do
                            ppt <- lift $ pp t
                            genError l $ text "genPublicSize:" <+> ppid pv <+> ppt
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
    
annLine :: AnnDoc -> DDoc
annLine (EnsureK,isFree,vs,x,isLeak) = ppIsFree isFree (dtext "ensures") (ppLeakageFun isLeak x) <<>> dsemicolon
annLine (RequireK,isFree,vs,x,isLeak) = ppIsFree isFree (dtext "requires") (ppLeakageFun isLeak x) <<>> dsemicolon
annLine (RequireK,isFree,vs,x,isLeak) = ppIsFree isFree (dtext "ensures") (ppLeakageFun isLeak x) <<>> dsemicolon
annLine (StmtK,Just _,vs,x,isLeak) = dtext "assume" <<+>> ppLeakageAtt isLeak <<+>> x <<>> dsemicolon
annLine (StmtK,Nothing,vs,x,isLeak) = dtext "assert" <<+>> ppLeakageAtt isLeak <<+>> x <<>> dsemicolon
annLine (InvariantK,isFree,vs,x,isLeak) = ppIsFree isFree (dtext "invariant") (ppLeakageFun isLeak x) <<>> dsemicolon
annLine (DecreaseK,isFree,vs,x,isLeak) = dtext "decreases" <<+>> x <<>> dsemicolon
annLine (ReadsK,_,vs,x,isLeak) = dtext "reads" <<+>> x <<>> dsemicolon
annLine (ModifiesK,_,vs,x,isLeak) = dtext "modifies" <<+>> x <<>> dsemicolon
annLine (NoK,isFree,vs,x,isLeak) = ppIsFree (fmap (const True) isFree) dempty x

ppIsFree :: Maybe Bool -> DDoc -> DDoc -> DDoc
ppIsFree Nothing c d = c <<+>> d
ppIsFree (Just False) c d = dppFree True (c <<+>> d)
ppIsFree (Just True) c d = c <<+>> (dppFreeFun True d)

dppFree isFree doc = if isFree then dtext "free" <<+>> doc else doc
dppLeak Nothing doc = doc
dppLeak (Just False) doc = dtext "leakage" <<+>> doc
dppLeak (Just True) doc = dtext "leakageout" <<+>> doc

ppLeakageAtt :: Maybe Bool -> DDoc
ppLeakageAtt Nothing = dempty
ppLeakageAtt (Just False) = dtext "{:leakage}"
ppLeakageAtt (Just True) = dtext "{:leakageout}"

ppLeakageFun :: Maybe Bool -> DDoc -> DDoc
ppLeakageFun Nothing d = d
ppLeakageFun (Just False) d = dtext "Leakage" <<>> dparens d
ppLeakageFun (Just True) d = dtext "LeakageOut" <<>> dparens d

dppFreeFun :: Bool -> DDoc -> DDoc
dppFreeFun False d = d
dppFreeFun True d = dtext "Free" <<>> dparens d

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
annKindClass ModifiesK = ProcKC
annKindClass NoK = ExprKC

annLines :: AnnKind -> AnnsDoc -> (AnnsDoc,DDoc)
annLines c anns = annLinesC (annKindClass c) anns

-- the input boolean determines if we are in a procedure context or not
-- if not in a procedure context, we postpone procedure annotations
annLinesC :: AnnKindClass -> AnnsDoc -> (AnnsDoc,DDoc)
annLinesC cl anns = (anns',dvcat $ map annLine xs)
    where (anns',xs) = List.partition ((>cl) . annKindClass . fst5) anns

annLinesProcC :: AnnsDoc -> DDoc
annLinesProcC anns = d
    where
    (reads,anns') = List.partition ((==ReadsK) . fst5) anns
    (modifies,anns'') = List.partition ((==ReadsK) . fst5) anns'
    anns''' = List.nub anns''
    reads' = Set.fromList $ map fou5 reads
    readk = case Set.toList reads' of
                [] -> []
                xs -> [(ReadsK,Just False,Set.empty,dsepBy xs comma,Nothing)]
    modifies' = Set.fromList $ map fou5 modifies
    modifyk = case Set.toList modifies' of
                [] -> []
                xs -> [(ModifiesK,Just False,Set.empty,dsepBy xs comma,Nothing)]
    ([],d) = annLinesC ProcKC (readk ++ modifyk ++ anns''')

quantifierAnnsToDafny :: DafnyK m => Set VarIdentifier -> [ProcedureAnnotation GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,AnnsDoc)
quantifierAnnsToDafny qvs xs = do
    (anns,ens) <- Utils.mapAndUnzipM (quantifierAnnToDafny qvs) xs
    return (concat anns,concat ens)

quantifierAnnToDafny :: DafnyK m => Set VarIdentifier -> ProcedureAnnotation GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,AnnsDoc)
quantifierAnnToDafny qvs (EnsuresAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing EnsureK e
        (anns,pe') <- annotateExpr anne qvs pe
        ens <- annExpr (boolIsFree isFree) isLeak leakMode EnsureK vs pe'
        return (anns,ens)

procedureAnnsToDafny :: DafnyK m => [ProcedureAnnotation GIdentifier (Typed Position)] -> DafnyM m AnnsDoc
procedureAnnsToDafny xs = liftM concat $ mapM (procedureAnnToDafny) xs

procedureAnnToDafny :: DafnyK m => ProcedureAnnotation GIdentifier (Typed Position) -> DafnyM m AnnsDoc
procedureAnnToDafny (RequiresAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing RequireK e
        req <- annExpr (boolIsFree isFree) isLeak leakMode RequireK vs pe
        return $ anne ++ req
procedureAnnToDafny (EnsuresAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing EnsureK e
        ens <- annExpr (boolIsFree isFree) isLeak leakMode EnsureK vs pe
        return $ anne ++ ens
procedureAnnToDafny (InlineAnn l isInline) = withInAnn True $ return []
procedureAnnToDafny (PDecreasesAnn l e) = withInAnn True $ do
    leakMode <- getLeakMode
    vs <- lift $ usedVs' e
    (anne,pe) <- expressionToDafny False Nothing EnsureK e
    decr <- annExpr Nothing Nothing leakMode DecreaseK vs pe
    return $ anne ++ decr

statementsToDafny :: DafnyK m => [Statement GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,DDoc)
statementsToDafny ss = do
    (anns,docs) <- Utils.mapAndUnzipM statementToDafny ss
    return (concat anns,dvcat docs)

addAnnsC :: DafnyK m => AnnKindClass -> AnnsDoc -> DDoc -> DafnyM m (AnnsDoc,DDoc)
addAnnsC c anns doc = do
    let (anns1,anns2) = annLinesC c anns
    return (anns1,anns2 $$+$$ doc)

dropAnns :: Set VarIdentifier -> AnnsDoc -> AnnsDoc
dropAnns vs as = filter keepAnn as
    where
    keepAnn (_,_,avs,_,_) = Set.null $ Set.intersection vs vs

statementToDafny :: DafnyK m => Statement GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
statementToDafny qs@(QuantifiedStatement l q args ann s) = withAssumptions $ do
    let pq = quantifierToDafny q
    (annpargs,pargs) <- quantifierArgsToDafny StmtK args
    vs <- lift $ liftM Set.unions $ mapM usedVs' args
    (preqs,pens) <- quantifierAnnsToDafny vs ann
    (anns,ps) <- statementsToDafny s
    let (topanns,passerts) = annLinesC StmtKC (preqs++anns)
    lift $ debugTc $ do
        liftIO $ putStrLn $ "quantifierStmtToDafny " ++ show vs ++ "\n" ++ show ps
    return (dropAnns vs topanns,pq <<+>> dparens pargs $$+$$ annLinesProcC pens $$+$$ dvbraces (passerts $$+$$ ps))
statementToDafny (CompoundStatement _ ss) = do
    (anns,pss) <- statementsToDafny ss
    return (anns,dvbraces pss)
statementToDafny (IfStatement _ c s1 s2) = do
    (ann1,pc) <- expressionToDafny False Nothing StmtK c
    (annthen,ps1) <- withAssumptions $ statementToDafny s1
    (concat -> annelse,ps2) <- withAssumptions $ Utils.mapAndUnzipM statementToDafny s2
    let annthen' = addAnnsCond pc annthen
    let annelse' = addAnnsCond (dchar '!' <<>> dparens pc) annelse
    ppo <- dppOptM ps2 (return . (dtext "else" <<+>>))
    addAnnsC StmtKC (ann1++annthen'++annelse') $ dtext "if" <<+>> pc <<+>> ps1 $$+$$ ppo
statementToDafny (BreakStatement l) = return ([],dtext "break" <<>> dsemicolon)
statementToDafny (ContinueStatement l) = return ([],dtext "continue" <<>> dsemicolon)
statementToDafny (ReturnStatement l e) = do
    (anne,pe) <- mapExpressionToDafny False Nothing StmtK e
    addAnnsC StmtKC anne $ dtext "return" <<+>> maybe dempty id pe <<>> dsemicolon
statementToDafny (ExpressionStatement _ (BinaryAssign l le (BinaryAssignEqual _) re)) = do
    (pres,pre) <- expressionToDafny False Nothing StmtK re
    leftvs <- lift $ usedVs' le    
    (post,pass) <- dropAssumptions leftvs $ assignmentToDafny StmtK le (Left pre)
    let (anns1,pres') = annLinesC StmtKC pres
    let (anns2,post') = annLinesC StmtKC post
    case (le,re) of
        (RVariablePExpr _ (VarName _ v'),RVariablePExpr _ (VarName _ v)) -> copyDafnyAssumptions (unTyped l) v v'
        otherwise -> return ()
    return (anns1++anns2,pres' $$+$$ pass <<>> dsemicolon $$+$$ post')
statementToDafny es@(ExpressionStatement (Typed l _) e) = do
    let t = typed $ loc e
    case t of
        ComplexT Void -> do
            (anne,pe) <- expressionToDafny False Nothing StmtK e
            let ppe = if (pe==dempty) then pe else pe <<>> dsemicolon
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
    assert <- annExpr Nothing Nothing leakMode StmtK vs pe
    addAnnsC StmtKC (anne++assert) dempty
statementToDafny (AnnStatement l ss) = withInAnn True $ do
    (anns,doc) <- statementAnnsToDafny ss
    addAnnsC StmtKC anns doc
statementToDafny (VarStatement l (VariableDeclaration _ isConst isHavoc t vs)) = do
    (t',annst) <- typeToDafny (unTyped $ loc t) StmtK (typed $ loc t)
    (concat -> anns,dvcat -> pvd) <- Utils.mapAndUnzipM (varInitToDafny isConst isHavoc t') $ Foldable.toList vs
    addAnnsC StmtKC (annst++anns) pvd
statementToDafny (WhileStatement (Typed l (WhileT rs ws)) e anns s) = withAssumptions $ do
    annframes <- propagateDafnyAssumptions l InvariantK rs ws
    (anne,pe) <- expressionToDafny False Nothing InvariantK e
    annl <- loopAnnsToDafny anns
    let (annw,annl') = annLinesC StmtKC annl
    (ann2,ps) <- statementToDafny s
    (anns,pw) <- addAnnsC StmtKC (anne++annw++ann2) $ annl' $$+$$ dvbraces ps
    return (anns,dtext "while" <<+>> pe $$+$$ annLinesProcC annframes $$+$$ pw)
statementToDafny (SyscallStatement l n params) = do
    (concat -> ss,concat -> params') <- lift $ runSimplify $ Utils.mapAndUnzipM simplifySyscallParameter params
    (anns1,pss) <- statementsToDafny ss
    (anns2,psys) <- syscallToDafny (unTyped l) n params'
    addAnnsC StmtKC (anns1++anns2) (pss $$+$$ psys)
statementToDafny (PrintStatement l es) = do
    (anne,pes) <- procCallArgsToDafny False StmtK es
    let prints = dvcat $ map (\pe -> dtext "print" <<>> dparens pe <<>> dsemicolon) pes
    addAnnsC StmtKC anne prints
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
    ass <- getAssumptions
    anns <- m
    -- if there is any assumption bigger than @x@, drop x
--    let (rest,anns') = List.partition (\x -> any (supersedesAssumption x) ass) anns
--    lift $ debugTc $ liftIO $ putStrLn $ show $ text "dropped assumptions" <+> annLinesProcC rest $+$ text "because of" <> annLinesProcC anns
    State.modify $ \env -> env { assumptions = assumptions env ++ anns }
    return anns

genFree :: Bool -> Bool -> FreeMode
genFree isLeak leakMode = case (leakMode,isLeak) of
    (True,True) -> KeepF
    (True,False) -> FreeF
    (False,True) -> DeleteF
    (False,False) -> KeepF

appendFreeMode :: FreeMode -> FreeMode -> FreeMode
appendFreeMode x y = max x y

annExpr :: DafnyK m => Maybe Bool -> Maybe Bool -> Bool -> AnnKind -> Set VarIdentifier -> DDoc -> DafnyM m AnnsDoc
annExpr isFree isLeak leakMode annK vs e = addAssumptions $ do
    mode <- State.gets freeMode
    case (appendFreeMode mode $ genFree (isJust isLeak) leakMode) of
        DeleteF -> return []
        KeepF -> return [(annK,isFree,vs,e,isLeak)]
        FreeF -> return [(annK,Just False,vs,e,isLeak)]
    
loopAnnToDafny :: DafnyK m => LoopAnnotation GIdentifier (Typed Position) -> DafnyM m AnnsDoc
loopAnnToDafny (DecreasesAnn l isFree e) = withInAnn True $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing InvariantK e
        decrease <- annExpr (boolIsFree isFree) Nothing False DecreaseK vs pe
        return $ anne ++ decrease
loopAnnToDafny (InvariantAnn l isFree isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing InvariantK e
        inv <- annExpr (boolIsFree isFree) isLeak leakMode InvariantK vs pe
        return $ anne ++ inv

boolIsFree :: Bool -> Maybe Bool
boolIsFree False = Nothing
boolIsFree True = Just False

statementAnnsToDafny :: DafnyK m => [StatementAnnotation GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,DDoc)
statementAnnsToDafny ss = do
    (anns,docs) <- Utils.mapAndUnzipM statementAnnToDafny ss
    return (concat anns,dvcat docs)

statementAnnToDafny :: DafnyK m => StatementAnnotation GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
statementAnnToDafny (AssumeAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing StmtK e
        assume <- annExpr (Just False) isLeak leakMode StmtK vs pe
        addAnnsC StmtKC (anne++assume) dempty
statementAnnToDafny (AssertAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ do
        vs <- lift $ usedVs' e
        (anne,pe) <- expressionToDafny False Nothing StmtK e
        assert <- annExpr Nothing isLeak leakMode StmtK vs pe
        addAnnsC StmtKC (anne++assert) dempty
statementAnnToDafny (EmbedAnn l isLeak e) = withInAnn True $ do
    leakMode <- getLeakMode
    withLeakMode (isJust isLeak) $ withFreeMode (genFree (isJust isLeak) leakMode) $ do
        vs <- lift $ usedVs' e
        (anns,call) <- statementToDafny e
        addAnnsC StmtKC (anns) call

-- checks that a dafny expression has a given shape
checkDafnyShape :: DafnyK m => Position -> Maybe Bool -> Set VarIdentifier -> Sizes GIdentifier (Typed Position) -> DDoc -> DafnyM m AnnsDoc
checkDafnyShape l isFree vs (Sizes szs) e = case Foldable.toList szs of
    [] -> return []
    (ds@(all (not . snd) -> True)) -> do
        (anns,des) <- Utils.mapAndUnzipM (expressionToDafny False Nothing StmtK) (map fst ds)
        let check = case des of
                        [de] -> dafnySize 0 e <<+>> dtext "==" <<+>> de
                        des -> e <<>> dtext ".shape()" <<+>> dtext "==" <<+>> dbrackets (dsepBy des comma)
        return $ concat anns ++ [(StmtK,isFree,vs,check,Nothing)]
    otherwise -> do
        ppszs <- lift $ pp (Sizes szs)
        ppe <- lift $ pp e
        genError l $ text "checkDafnyShape: unsupported array size" <+> ppszs <+> text "for" <+> ppe
    
varInitToDafny :: DafnyK m => Bool -> Bool -> DDoc -> VariableInitialization GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
varInitToDafny isConst False pty vd@(VariableInitialization l v sz (Just e)) = do
    ppvd <- lift $ pp vd
    genError (unTyped l) $ text "varInitToDafny: cannot convert default expression at" <+> ppvd
varInitToDafny isConst isHavoc pty (VariableInitialization l v sz ini) = do
    vs <- lift $ usedVs' (v,sz)
    vvs <- lift $ usedVs' v
    pv <- varToDafny v
    let def = dtext "var" <<+>> pv <<>> dchar ':' <<>> pty <<>> dsemicolon
    annp <- genDafnyAssumptions (unTyped $ loc v) False StmtK vvs pv (typed $ loc v)
    (annsini,pini) <- mapExpressionToDafny False Nothing StmtK ini
    annsize <- case (sz) of
        (Just szs) -> do
            let isFree = if isJust ini then Nothing else Just False
            checkDafnyShape (unTyped l) isFree vs szs pv
        otherwise -> return []
    assign <- dppOptM pini (\e -> return $ pv <<+>> dtext ":=" <<+>> e <<+>> dsemicolon)
    let (anns1,annsini') = annLinesC StmtKC annsini
    let (anns2,annsize') = annLinesC StmtKC $ annp ++ annsize
    lift $ debugTc $ liftIO $ putStrLn $ "varInitToDafny: " ++ show annsini' ++ "\n" ++ show pv ++ "\n" ++ show annsize'
    return (anns1++anns2,def $$+$$ annsini' $$+$$ assign $$+$$ annsize')

typeToDafny :: DafnyK m => Position -> AnnKind -> Type -> DafnyM m (DDoc,AnnsDoc)
typeToDafny l annK (BaseT b) = baseTypeToDafny l annK b
typeToDafny l annK (ComplexT t) = complexTypeToDafny l annK t
typeToDafny l annK t = do
    ppt <- lift $ pp t
    genError l $ text "typeToDafny:" <+> ppt

baseTypeToDafny :: DafnyK m => Position -> AnnKind -> BaseType -> DafnyM m (DDoc,AnnsDoc)
baseTypeToDafny l annK (BVar v _) = liftM (,[]) $ return $ DIden $ VIden v
baseTypeToDafny l annK (TyPrim prim) = liftM (,[]) $ lift $ liftM ddoc $ pp prim
baseTypeToDafny l annK (MSet b) = do
    (b',anns) <- complexTypeToDafny l annK b
    return (dtext "multiset" <<>> dabrackets b',anns)
baseTypeToDafny l annK (Set b) = do
    (b',anns) <- complexTypeToDafny l annK b
    return (dtext "set" <<>> dabrackets b',anns)
baseTypeToDafny l annK (TApp _ args dec@(decTypeTyVarId -> Just mid)) = do
    did <- lookupAndLoadDafnyDec l dec
    psn <- ppDafnyIdM did
    let ppArg (t,False) = typeToDafny l annK t
        ppArg (t,True) = do
            ppt <- lift $ pp t
            genError l $ text "baseTypeToDafny: variadic argument" <+> ppt
    (args',anns) <- Utils.mapAndUnzipM ppArg args
    let pargs = if null args' then dempty else dabrackets $ dsepBy args' comma
    return (psn <<>> pargs,concat anns)
--baseTypeToDafny t = genError noloc $ text "baseTypeToDafny:" <+> pp t

complexTypeToDafny :: DafnyK m => Position -> AnnKind -> ComplexType -> DafnyM m (DDoc,AnnsDoc)
complexTypeToDafny l annK t@(CType s b d) = do
    (pb,annsb) <- baseTypeToDafny l annK b
    mb <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
    case mb of
        Right 0 -> return (pb,annsb)
        -- uni-dimensional arrays as sequences
        Right 1 -> return (dtext "seq" <<>> dabrackets pb,annsb)
        -- multi-dimensional arrays as Dafny's fixed-length multi-dimensional arrays wrapped inside a class
        Right n -> return (dtext "Array" <<>> dint (fromEnum n) <<>> dabrackets pb,annsb)
        Left err -> do
            ppt <- lift $ pp t
            throwError $ GenericError l (text "complexTypeToDafny:" <+> ppt) $ Just err
complexTypeToDafny l annK t = do
    ppt <- lift $ pp t
    genError l $ text "complexTypeToDafny:" <+> ppt

data AnnKind = StmtK | EnsureK | RequireK | InvariantK | DecreaseK | NoK | ReadsK | ModifiesK
  deriving (Show,Eq)
instance Monad m => PP m AnnKind where
    pp = return . text . show

type AnnsDoc = [AnnDoc]
-- (kind,isFree (Nothing=not free,Just False=not inlined,Just True=inlined),used variables,dafny expression)
type AnnDoc = (AnnKind,Maybe Bool,Set VarIdentifier,DDoc,Maybe Bool)

isFreeAnnDoc :: AnnDoc -> Bool
isFreeAnnDoc (_,isFree,_,_,_) = isJust isFree

indexToDafny :: DafnyK m => Bool -> AnnKind -> Maybe DDoc -> Int -> Index GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
indexToDafny isLVal annK isClass i (IndexInt l e) = do
    (anne,pe) <- expressionToDafny isLVal Nothing annK e
    return (anne,pe)
indexToDafny isLVal annK Nothing i (IndexSlice l e1 e2) = do
    (anne1,pe1) <- mapExpressionToDafny isLVal Nothing annK e1
    (anne2,pe2) <- mapExpressionToDafny isLVal Nothing annK e2
    return (anne1++anne2,maybe dempty id pe1 <<>> dtext ".." <<>> maybe dempty id pe2)
indexToDafny isLVal annK (Just pe) i (IndexSlice l e1 e2) = do
    (anne1,pe1) <- mapExpressionToDafny isLVal Nothing annK e1
    let pe1' = maybe (dint 0) id pe1
    (anne2,pe2) <- mapExpressionToDafny isLVal Nothing annK e2
    let pe2' = maybe (pe <<>> dtext ".Length" <<>> dint i <<>> dtext "()") id pe2
    return (anne1++anne2,pe1' <<>> dtext "," <<>> pe2')

-- left = expression, right = update
assignmentToDafny :: DafnyK m => AnnKind -> Expression GIdentifier (Typed Position) -> Either DDoc DDoc -> DafnyM m (AnnsDoc,DDoc)
assignmentToDafny annK se@(SelectionExpr l e att) (Left pre) = do
    did <- tAttDec (unTyped $ loc e) (liftM ddoc $ pp se) (typed $ loc e)
    psn <- ppDafnyIdM did
    patt <- structAttToDafny (unTyped l) False psn $ fmap typed att
    (annse,_) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ dchar '.' <<>> dparens (patt <<+>> dtext ":=" <<+>> pre))
    return (annse++ann,doc)
assignmentToDafny annK se@(SelectionExpr l e att) (Right upd) = do
    did <- tAttDec (unTyped $ loc e) (liftM ddoc $ pp se) (typed $ loc e)
    psn <- ppDafnyIdM did
    patt <- structAttToDafny (unTyped l) False psn $ fmap typed att
    (annse,pse) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ dchar '.' <<>> dparens (patt <<+>> dtext ":=" <<+>> pse <<>> upd))
    return (annse++ann,doc)
assignmentToDafny annK se@(PostIndexExpr l e (Foldable.toList -> [i])) (Left pre) = do
    (anni,pi) <- indexToDafny True annK Nothing 0 i
    (annse,_) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ dbrackets (dtext "int" <<>> dparens pi <<+>> dtext ":=" <<+>> pre))
    return (anni++annse++ann,doc)
assignmentToDafny annK se@(PostIndexExpr l e (Foldable.toList -> [i])) (Right upd) = do
    (anni,pi) <- indexToDafny True annK Nothing 0 i
    (annse,pse) <- expressionToDafny True Nothing annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ dbrackets (dtext "int" <<>> dparens pi <<+>> dtext ":=" <<+>> pse <<>> upd))
    return (anni++annse++ann,doc)
assignmentToDafny annK (PostIndexExpr l e (Foldable.toList -> [i,j])) (Left pre) = do
    (anne,pe) <- expressionToDafny True Nothing annK e
    (anni,pi) <- indexToDafny True annK (Just pe) 0 i
    (annj,pj) <- indexToDafny True annK (Just pe) 1 j
    let args = pi <<>> dcomma <<>> pj <<>> dcomma <<>> pre
    let ppids = ppIndexIds [i,j]
    return (anni++annj++anne,pe <<>> dtext ".update" <<>> ppids <<>> dparens args)
assignmentToDafny annK e@(RVariablePExpr {}) (Left pre) = do
    (anne,pe) <- expressionToDafny True Nothing annK e
    return (anne,pe <<+>> dtext ":=" <<+>> pre)
assignmentToDafny annK e@(RVariablePExpr {}) (Right upd) = do
    (anne,pe) <- expressionToDafny True Nothing annK e
    return (anne,pe <<+>> dtext ":=" <<+>> pe <<>> upd)
assignmentToDafny annK e pre = do
    ppannK <- lift $ pp annK
    ppe <- lift $ pp e
    pppre <- lift $ pp pre
    genError (unTyped $ loc e) $ text "assignmentToDafny:" <+> ppannK <+> ppe <+> pppre

tAttDec :: DafnyK m => Position -> TcM m DDoc -> Type -> DafnyM m DafnyId
tAttDec l ppe t@(BaseT (TApp _ _ d)) = do
    did <- lookupAndLoadDafnyDec l d
    return did
tAttDec l ppe t@(ComplexT (CType Public b d)) = do
    mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
    case mbd of
        Right 0 -> tAttDec l ppe (BaseT b)
        otherwise -> do
            ppl <- lift $ pp l
            ppt <- lift $ pp t
            pe <- lift $ ppe >>= pp
            genError l $ text "tAttDec:" <+> ppl <+> text "unsupported complex type" <+> ppt <+> text "in expression" <+> pe
tAttDec l ppe t = do
    ppl <- lift $ pp l
    ppt <- lift $ pp t
    pe <- lift $ ppe >>= pp
    genError l $ text "tAttDec:" <+> ppl <+> text "unsupported type" <+> ppt <+> text "in expression" <+> pe

hasLeakExpr :: Expression GIdentifier (Typed Position) -> Bool
hasLeakExpr = everything (||) (mkQ False aux)
    where
    aux :: Expression GIdentifier (Typed Position) -> Bool
    aux (LeakExpr {}) = True
    aux _ = False

unlessNoAssumptions :: DafnyK m => AnnKind -> Maybe (Expression GIdentifier (Typed Position)) -> a -> DafnyM m a -> DafnyM m a
unlessNoAssumptions annK e def m = do
    no <- noAssumptions annK e
    if no then return def else m

noAssumptions :: DafnyK m => AnnKind -> Maybe (Expression GIdentifier (Typed Position)) -> DafnyM m Bool
noAssumptions annK mbe = do
    dec <- getInDecl
    let isAx = maybe False isAxiomDafnyId dec
    let isAnnExpr = maybe False (\e -> hasLeakExpr e || isLeakDecExpr e || not (isAnnDecExpr e)) mbe
    return $ (isAx && annK==EnsureK) || isAnnExpr

isLeakDecExpr :: Expression GIdentifier (Typed Position) -> Bool
isLeakDecExpr e = everything (||) (mkQ False isLeakIDecType) e

isAnnDecExpr :: Expression GIdentifier (Typed Position) -> Bool
isAnnDecExpr e = everything (&&) (mkQ True aux) e
    where
    aux :: InnerDecType -> Bool
    aux (ProcType {}) = False
    aux (LemmaType {}) = False
    aux _ = True

projectionToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Expression GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
projectionToDafny isLVal isQExpr annK se@(PostIndexExpr l e (Foldable.toList -> is)) = do
    vs <- lift $ usedVs' se
    (anne,pe) <- expressionToDafny isLVal Nothing annK e
    let Typed _ t = loc e
    mbd <- lift $ tryTcError l $ typeDim l t >>= fullyEvaluateIndexExpr l
    case (mbd,is) of
        (Right 1,[i]) -> do
            (anne,pe) <- expressionToDafny isLVal Nothing annK e
            (anni,pi) <- indexToDafny isLVal annK Nothing 0 i
            let pse = pe <<>> dbrackets pi
            doGen <- noAssumptions annK (Just se)
            annp <- genDafnyAssumptions (unTyped l) doGen annK vs pse (typed l)
            qExprToDafny isQExpr (anne++anni++annp) pse
        (Right n,is) -> do
            (anne,pe) <- expressionToDafny isLVal Nothing annK e
            let is' = take (fromEnum n) $ is ++ repeat (IndexSlice l Nothing Nothing)
            (concat -> annis,pis) <- Utils.mapAndUnzipM (\(idx,i) -> indexToDafny isLVal annK (Just pe) i idx) (zip is' [0..])
            let pse = pe <<>> dtext ".project" <<>> ppIndexIds is' <<>> dparens (dsepBy pis comma)
            doGen <- noAssumptions annK (Just se)
            annp <- genDafnyAssumptions (unTyped l) doGen annK vs pse (typed l)
            qExprToDafny isQExpr (anne++annis++annp) pse
        otherwise -> do
            ppannK <- lift $ pp annK
            ppe <- lift $ pp e
            ppis <- lift $ liftM (sepBy comma) $ mapM pp is
            genError (unTyped $ loc e) $ text "projectionToDafny:" <+> ppid isLVal <+> ppannK <+> ppe <> brackets ppis

ppIndexIds :: [Index iden loc] -> DDoc
ppIndexIds [] = dempty
ppIndexIds (IndexInt {}:xs) = dint 0 <<>> ppIndexIds xs
ppIndexIds (IndexSlice {}:xs) = dint 1 <<>> ppIndexIds xs

type IsQExpr = Maybe (Set VarIdentifier)

expressionToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Expression GIdentifier (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
expressionToDafny isLVal isQExpr annK se@(PostIndexExpr {}) = do
    projectionToDafny isLVal isQExpr annK se
expressionToDafny isLVal isQExpr annK se@(SelectionExpr l e att) = do
    vs <- lift $ usedVs' se
    (anne,pe) <- expressionToDafny isLVal Nothing annK e
    did <- tAttDec (unTyped $ loc e) (liftM ddoc $ pp se) (typed $ loc e)
    psn <- ppDafnyIdM did
    patt <- structAttToDafny (unTyped l) False psn $ fmap typed att
    let pse = pe <<>> dchar '.' <<>> patt
    doGen <- noAssumptions annK (Just se)
    annp <- genDafnyAssumptions (unTyped l) doGen annK vs pse (typed l)
    -- always assert equality of projection, if it is a base type, since we don't do so when declaring the struct variable
    qExprToDafny isQExpr (anne++annp) pse
expressionToDafny isLVal isQExpr annK e@(RVariablePExpr l v) = do
    vs <- lift $ usedVs' e
    pv <- varToDafny v
    doGen <- noAssumptions annK (Just e)
    annp <- genDafnyAssumptions (unTyped $ loc v) doGen annK vs pv (typed $ loc v)
    qExprToDafny isQExpr annp pv
expressionToDafny isLVal isQExpr annK le@(LitPExpr l lit) = do
    (anns,pe) <- literalToDafny annK lit
    qExprToDafny isQExpr anns pe
expressionToDafny isLVal isQExpr annK le@(LeakExpr l e) = do
    (anne,pe) <- expressionToDafny False Nothing annK e
    leakMode <- getLeakMode
    if leakMode
        then qExprToDafny isQExpr anne (dtext "Leak" <<>> dparens pe)
        else qExprToDafny isQExpr anne (dtext "true")
expressionToDafny isLVal isQExpr annK (QualExpr l e _) = do
    expressionToDafny isLVal isQExpr annK e
expressionToDafny isLVal isQExpr annK e@(MultisetConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let pme = dtext "multiset" <<>> dbraces (dsepBy pes comma)
    pme' <- if List.null pes then qualifiedDafny (unTyped l) (typed l) pme else return pme
    qExprToDafny isQExpr annes pme'
expressionToDafny isLVal isQExpr annK e@(SetConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let pme = dbraces (dsepBy pes comma)
    pme' <- if List.null pes then qualifiedDafny (unTyped l) (typed l) pme else return pme
    qExprToDafny isQExpr annes pme'
expressionToDafny isLVal isQExpr annK e@(ArrayConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let Typed ll arrt = l
    mbd <- lift $ tryTcError l $ typeDim l arrt >>= fullyEvaluateIndexExpr l
    case mbd of
        Right 1 -> do
            let pae = dbrackets (dsepBy pes comma)
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
    let pme = dtext "multiset" <<>> dparens pe
    doGen <- noAssumptions annK (Just me)
    annp <- genDafnyAssumptions (unTyped l) doGen annK vs pme (typed l)
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
                    let pme = dparens (dtext "set" <<+>> px <<>> dchar ':' <<>> pbt <<+>> dchar '|' <<+>> px <<+>> dtext "in" <<+>> pe)
                    doGen <- noAssumptions annK (Just me)
                    annp <- genDafnyAssumptions (unTyped l) doGen annK vs pme (typed l)
                    qExprToDafny isQExpr (annbt++anne++annp) pme
                Right n -> do
                    x <- lift $ genVar (VIden $ mkVarId "iset" :: GIdentifier)
                    let vx = VarName (Typed (unTyped l) $ BaseT uint64) x
                    px <- varToDafny vx
                    (anne,pe) <- expressionToDafny False Nothing annK e
                    let idxs = fromListNe [IndexInt l (varExpr vx),IndexSlice l Nothing Nothing]
                    (annproj,proje) <- projectionToDafny isLVal isQExpr annK $ PostIndexExpr l e idxs
                    let pme = dparens (dtext "set" <<+>> px <<>> dchar ':' <<>> dtext "uint64" <<+>> dchar '|' <<+>> px <<+>> dtext "<" <<+>> dparens (dafnyShape n pe <<>> dbrackets (dint 0)) <<+>> dtext "::" <<+>> proje)
                    doGen <- noAssumptions annK (Just me)
                    annp <- genDafnyAssumptions (unTyped l) doGen annK vs pme (typed l)
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
            did <- lookupAndLoadDafnyDec (unTyped l) dec
            (annargs,pargs) <- procCallArgsToDafny isLVal annK args
            pn <- ppDafnyIdM did
            let pe = pn <<>> dparens (dsepBy pargs comma)
            doGen <- noAssumptions annK (Just e)
            annp <- genDafnyAssumptions (unTyped l) doGen annK vs pe (typed l)
            qExprToDafny isQExpr (annargs++annp) pe
        --Just (mbdec,ss) -> do
        --    -- load the lemma separately (to check its body)
        --    mapM_ (lookupAndLoadDafnyDec (unTyped l)) mbdec
        --    -- inline the lemma call without its body
        --    anns <- mapM statementAnnToDafny ss
        --    return (concat anns,empty)
expressionToDafny isLVal isQExpr annK e@(BinaryExpr l e1 op@(loc -> (Typed _ (DecT dec))) e2) = do
    vs <- lift $ usedVs' e
    did <- lookupAndLoadDafnyDec (unTyped l) dec
    (annargs,pargs) <- procCallArgsToDafny isLVal annK [(e1,False),(e2,False)]
    pn <- ppDafnyIdM did
    let pe = pn <<>> dparens (dsepBy pargs comma)
    doGen <- noAssumptions annK (Just e)
    annp <- genDafnyAssumptions (unTyped l) doGen annK vs pe (typed l)
    qExprToDafny isQExpr (annargs++annp) pe
expressionToDafny isLVal isQExpr annK qe@(QuantifiedExpr l q args e) = withAssumptions $ do
    let pq = quantifierToDafny q
    (annpargs,pargs) <- quantifierArgsToDafny annK args
    vs <- lift $ liftM Set.unions $ mapM usedVs' args
    (anne,pe) <- expressionToDafny isLVal (Just vs) annK e
    (anns,pe') <- annotateExpr (annpargs++anne) vs pe
    lift $ debugTc $ do
        liftIO $ putStrLn $ "quantifierExprToDafny " ++ show vs ++ "\n" ++ show pe ++ "\n --> \n" ++ show pe'
    return (dropAnns vs anns,dparens (pq <<+>> pargs <<+>> dtext "::" <<+>> pe'))
expressionToDafny isLVal isQExpr annK me@(SetComprehensionExpr l t x px fx) = withAssumptions $ do
    (annarg,parg) <- quantifierArgToDafny annK (t,x)
    vs <- lift $ usedVs' (t,x)
    (annpe,pppx) <- expressionToDafny isLVal (Just vs) annK px
    (annfe,pfx) <- mapExpressionToDafny isLVal (Just vs) annK fx
    ppfx <- lift $ dppOptM pfx (liftM (dtext "::" <<+>>) . liftM ddoc . pp)
    (anns,pppx') <- annotateExpr (annarg++annpe++annfe) vs pppx
    let pme = dparens (dtext "set" <<+>> parg <<+>> dchar '|' <<+>> pppx' <<+>> ppfx)
    return (dropAnns vs anns,pme)
expressionToDafny isLVal isQExpr annK ce@(CondExpr l econd ethen eelse) = do
    (anncond,ppcond) <- expressionToDafny isLVal isQExpr annK econd
    (annthen,ppthen) <- expressionToDafny isLVal isQExpr annK ethen
    (annelse,ppelse) <- expressionToDafny isLVal isQExpr annK eelse
    let annthen' = addAnnsCond ppcond annthen
    let annelse' = addAnnsCond (dchar '!' <<>> dparens ppcond) annelse
    return (anncond++annthen'++annelse',dtext "if" <<+>> ppcond <<+>> dtext "then" <<+>> ppthen <<+>> dtext "else" <<+>> ppelse)
expressionToDafny isLVal isQExpr annK e@(ResultExpr l) = do
    mb <- getResult
    case mb of
        Just result -> return ([],result)
        otherwise -> do
            ppannK <- lift $ pp annK
            ppe <- lift $ pp e
            genError (unTyped $ loc e) $ text "expressionToDafny:" <+> ppid isLVal <+> ppannK <+> ppe
expressionToDafny isLVal isQExpr annK (OldExpr l e) = do
    (anne,ppe) <- expressionToDafny isLVal isQExpr annK e
    return (anne,dtext "old" <<>> dparens ppe)
expressionToDafny isLVal isQExpr annK e = do
    ppannK <- lift $ pp annK
    ppe <- lift $ pp e
    genError (unTyped $ loc e) $ text "expressionToDafny:" <+> ppid isLVal <+> ppannK <+> ppe

qExprToDafny :: DafnyK m => IsQExpr -> AnnsDoc -> DDoc -> DafnyM m (AnnsDoc,DDoc)
qExprToDafny (Just vs) anne e = annotateExpr anne vs e
qExprToDafny Nothing anne e = return (anne,e)

annotateExpr :: DafnyK m => AnnsDoc -> Set VarIdentifier -> DDoc -> DafnyM m (AnnsDoc,DDoc)
annotateExpr anne vs pe = do
    lift $ debugTc $ do
        ppas <- ppAnnLs anne'
        ppvs <- liftM (sepBy space) $ mapM pp $ Set.toList vs
        liftIO $ putStrLn $ "annotateExpr: " ++ show ppvs ++ "\n" ++ show ppas
    return (anne',pppre (pppost pe))
  where
    pppre = maybe id (\p x -> dparens (p <<+>> dtext "==>" <<+>> x)) (ands pre)
    pppost = maybe id (\p x -> dparens (p <<+>> dtext "&&" <<+>> x)) (ands post)
    (deps,anne') = List.partition (\(k,_,evs,_,_) -> k /= ReadsK && k /= ModifiesK && not (Set.null $ Set.intersection evs vs)) anne
    (map fou5 -> pre,map fou5 -> post) = List.partition (isJust . snd5) deps
    ands [] = Nothing
    ands (x:xs) = case ands xs of
        Nothing -> Just x
        Just ys -> Just $ dparens (x <<+>> dtext "&&" <<+>> ys)

quantifierToDafny :: Quantifier (Typed Position) -> DDoc
quantifierToDafny (ForallQ _) = dtext "forall"
quantifierToDafny (ExistsQ _) = dtext "exists"

quantifierArgsToDafny :: DafnyK m => AnnKind -> [(TypeSpecifier GIdentifier (Typed Position),VarName GIdentifier (Typed Position))] -> DafnyM m (AnnsDoc,DDoc)
quantifierArgsToDafny annK xs = do
    (anns,vs) <- Utils.mapAndUnzipM (quantifierArgToDafny annK) xs
    return (concat anns,dsepBy vs comma)

quantifierArgToDafny :: DafnyK m => AnnKind -> (TypeSpecifier GIdentifier (Typed Position),VarName GIdentifier (Typed Position)) -> DafnyM m (AnnsDoc,DDoc)
quantifierArgToDafny annK (t,v) = do
    pv <- varToDafny v
    (pt,anns) <- typeToDafny (unTyped $ loc v) annK (typed $ loc v)
    return (anns,pv <<>> dchar ':' <<>> pt)

expressionsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression GIdentifier (Typed Position)) -> DafnyM m (AnnsDoc,[DDoc])
expressionsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (expressionToDafny isLVal Nothing annK) $ Foldable.toList es
    return (concat annes,es')

mapExpressionToDafny :: (Functor f,Traversable f,Foldable f,DafnyK m) => Bool -> IsQExpr -> AnnKind -> f (Expression GIdentifier (Typed Position)) -> DafnyM m (AnnsDoc,f DDoc)
mapExpressionToDafny isLVal isQExpr annK es = do
    rs <- mapM (expressionToDafny isLVal isQExpr annK) es
    return (concat $ Foldable.toList $ fmap fst rs,fmap snd rs)

procCallArgsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression GIdentifier (Typed Position),IsVariadic) -> DafnyM m (AnnsDoc,[DDoc])
procCallArgsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (procCallArgToDafny isLVal annK) $ Foldable.toList es
    return (concat annes,es')
    
procCallArgToDafny :: DafnyK m => Bool -> AnnKind -> (Expression GIdentifier (Typed Position),IsVariadic) -> DafnyM m (AnnsDoc,DDoc)
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

syscallToDafny :: DafnyK m => Position -> String -> [SyscallParameter GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,DDoc)
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
                    (annse,pe) <- qExprToDafny Nothing (annx++anny) (dparens $ px <<+>> dchar '+' <<+>> py)
                    addAnnsC StmtKC annse $ pret <<+>> dtext ":=" <<+>> pe <<>> dsemicolon
                (Right d,Right n) -> do
                    pret <- varToDafny ret
                    (annse,pe) <- qExprToDafny Nothing (annx++anny) (dparens $ px <<+>> dchar '+' <<+>> py)
                    addAnnsC StmtKC annse $ pret <<+>> dtext ":=" <<+>> dtext "new Array" <<>> dint (fromEnum d) <<>> dtext ".cat" <<>> dint (fromEnum n) <<>> dparens (px <<>> dcomma <<>> py) <<>> dsemicolon
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
            return (annszs,pret <<+>> dtext ":=" <<+>> dtext "new Array" <<>> dint (fromEnum d) <<>> dtext ".reshape" <<>> dint (fromEnum dx) <<>> dparens (px <<>> dcomma <<>> dsepBy pszs comma) <<>> dsemicolon)
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

builtinToDafny :: DafnyK m => Bool -> IsQExpr -> AnnKind -> Typed Position -> String -> [Expression GIdentifier (Typed Position)] -> DafnyM m (AnnsDoc,DDoc)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.eq" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "==" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.neq" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "!=" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.band" [x,y] = do
    (annx,px) <- expressionToDafny isLVal isQExpr annK x
    (anny,py) <- expressionToDafny isLVal isQExpr annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "&&" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.bor" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "||" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.lt" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "<" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.le" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "<=" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.gt" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext ">" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.ge" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext ">=" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.implies" [x,y] = do
    (annx,px) <- expressionToDafny isLVal isQExpr annK x
    (anny,py) <- expressionToDafny isLVal isQExpr annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "==>" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.subset" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "<=" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.in" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    let Typed _ t = loc y
    mbd <- lift $ tryTcError l $ typeDim l t >>= fullyEvaluateIndexExpr l
    case mbd of
        Right 0 -> qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "in" <<+>> py)
        Right 1 -> qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "in" <<+>> py)
        Right n@((>1) -> True) -> do
            let pin = py <<>> dtext ".contains" <<>> dparens px
            qExprToDafny isQExpr (annx++anny) pin   
        Right n -> do
            ppt <- lift $ pp t
            genError (locpos l) $ text "builtinToDafny: unsupported in dimension" <+> ppid n <+> text "for" <+> ppt
        Left err -> do
            ppt <- lift $ pp t
            pperr <- lift $ pp err
            genError (locpos l) $ text "builtinToDafny: unsupported in dimension for" <+> ppt $+$ pperr
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.union" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "+" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.add" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "+" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.sum" [xs] = do
    (pret,annpret) <- typeToDafny l annK ret
    (annxs,pxs) <- expressionToDafny isLVal Nothing annK xs
    qExprToDafny isQExpr (annpret++annxs) (dparens $ dtext "sum_" <<>> pret <<>> dparens pxs)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.sub" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "-" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.mul" [x,y] = do
    (pt,annt) <- lift (typeBase l ret) >>= typeToDafny l annK
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    mbd <- lift $ tryTcError l $ typeDim l ret >>= fullyEvaluateIndexExpr l
    case mbd of
        Right 0 -> qExprToDafny isQExpr (annt++annx++anny) (dparens $ px <<+>> dtext "*" <<+>> py)
        Right n -> qExprToDafny isQExpr (annt++annx++anny) (dtext "mul" <<>> dint (fromEnum n) <<>> dchar '_' <<>> pt <<>> dparens (px <<>> dcomma <<>> py))
        otherwise -> do
            ppret <- lift $ pp ret
            genError (locpos l) $ text "builtinToDafny: unsupported mul dimension for" <+> ppret
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.div" [x,y] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    (anny,py) <- expressionToDafny isLVal Nothing annK y
    qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dtext "/" <<+>> py)
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.declassify" [x] = do -- we ignore security types
    vs <- lift $ usedVs' x
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    leakMode <- getLeakMode
    inAnn <- getInAnn
    if leakMode && not inAnn
        then do
            assert <- annExpr Nothing (Just False) True annK vs (dtext "DeclassifiedIn" <<>> dparens px)
            qExprToDafny isQExpr (annx++assert) px
        else qExprToDafny isQExpr annx px
builtinToDafny isLVal isQExpr annK (Typed l ret) "core.declassifyOut" [x] = do -- we ignore security types
    vs <- lift $ usedVs' x
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    leakMode <- getLeakMode
    inAnn <- getInAnn
    if leakMode && not inAnn
        then do
            assert <- annExpr Nothing (Just True) True annK vs (dtext "DeclassifiedOut" <<>> dparens px)
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
            assert <- annExpr Nothing (Just False) True annK vs (dtext "DeclassifiedIn" <<>> dparens px)
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
                (Right 1) -> qExprToDafny isQExpr (annx++anny) (dparens $ px <<+>> dchar '+' <<+>> py)
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
        BaseT b -> qExprToDafny isQExpr (annx) (dbrackets dempty)
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryTcError l $ fullyEvaluateIndexExpr l d
            case mbd of
                Right 0 -> qExprToDafny isQExpr (annx) $ dbrackets dempty
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
    qExprToDafny isQExpr (annx++annsz) (dtext "Repeat" <<>> dparens (px <<>> dcomma <<>> psz))
builtinToDafny isLVal isQExpr annK (Typed l tret) "core.cast" [x] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    let tx = typed $ loc x
    bret <- lift $ getBaseType l tret
    bx <- lift $ getBaseType l tx
    fn <- case (bret,bx) of
        (isUint8BaseType  -> True,isBoolBaseType -> True) -> return "bool_to_uint8"
        (isUint16BaseType -> True,isBoolBaseType -> True) -> return "bool_to_uint16"
        (isUint32BaseType -> True,isBoolBaseType -> True) -> return "bool_to_uint32"
        (isUint64BaseType -> True,isBoolBaseType -> True) -> return "bool_to_uint64"  
        (isFloat32BaseType -> True,isBoolBaseType -> True) -> return "bool_to_float32"  
        (isFloat64BaseType -> True,isBoolBaseType -> True) -> return "bool_to_float64"  
        otherwise -> do
            ppret <- lift $ pp tret
            ppx <- lift $ pp tx
            genError l $ text "builtinToDafny: unexpected cast expression" <+> ppret <+> ppx
    qExprToDafny isQExpr (annx) (dtext fn <<>> dparens (px))
builtinToDafny isLVal isQExpr annK (Typed l tret) "core.abs" [x] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    let tx = typed $ loc x
    bx <- lift $ getBaseType l tx
    bret <- lift $ getBaseType l tret
    fn <- case (bret) of
        (isUint8BaseType  -> True)  -> return "abs_uint8"
        (isUint16BaseType -> True)  -> return "abs_uint16"
        (isUint32BaseType -> True)  -> return "abs_uint32"
        (isUint64BaseType -> True)  -> return "abs_uint64"  
        (isFloat32BaseType -> True) -> return "abs_float32"  
        (isFloat64BaseType -> True) -> return "abs_float64"  
        otherwise -> do
            ppret <- lift $ pp tret
            ppx <- lift $ pp tx
            genError l $ text "builtinToDafny: unexpected abs expression" <+> ppret <+> ppx
    qExprToDafny isQExpr (annx) (dtext fn <<>> dparens px)
builtinToDafny isLVal isQExpr annK (Typed l tret) "core.inv" [x] = do
    (annx,px) <- expressionToDafny isLVal Nothing annK x
    let tx = typed $ loc x
    bx <- lift $ getBaseType l tx
    bret <- lift $ getBaseType l tret
    fn <- case (bret) of
        (isUint8BaseType  -> True)  -> return "inv_uint8"
        (isUint16BaseType -> True)  -> return "inv_uint16"
        (isUint32BaseType -> True)  -> return "inv_uint32"
        (isUint64BaseType -> True)  -> return "inv_uint64"  
        (isFloat32BaseType -> True) -> return "inv_float32"  
        (isFloat64BaseType -> True) -> return "inv_float64"  
        otherwise -> do
            ppret <- lift $ pp tret
            ppx <- lift $ pp tx
            genError l $ text "builtinToDafny: unexpected inv expression" <+> ppret <+> ppx
    qExprToDafny isQExpr (annx) (dtext fn <<>> dparens px)
builtinToDafny isLVal isQExpr annK (Typed l ret) n es = do
    ppannK <- lift $ pp annK
    ppret <- lift $ pp ret
    ppn <- lift $ pp n
    ppes <- lift $ pp es
    genError l $ text "builtinToDafny: unexpected" <+> ppannK <+> ppret <+> ppn <+> ppes

literalToDafny :: DafnyK m => AnnKind -> Literal (Typed Position) -> DafnyM m (AnnsDoc,DDoc)
literalToDafny annK lit = do
    let t = typed $ loc lit
    case t of
        ((==BaseT bool) -> True) -> return ([],ddoc $ ppid lit)
        ((==BaseT string) -> True) -> return ([],ddoc $ ppid lit)
        (isNumericType -> True) -> do
            (pt,anns) <- typeToDafny (unTyped $ loc lit) annK (typed $ loc lit)
            return (anns,dafnyAs (ddoc $ ppid lit) pt)

varToDafny :: DafnyK m => VarName GIdentifier (Typed Position) -> DafnyM m DDoc
varToDafny (VarName (Typed l t) n) = do
    let suffix = if isPublicType t then "Public" else "Private"
    let dn = DIden n
    return $ dn <<>> dtext suffix

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
    pp did = ppDafnyId did >>= pp

ppDafnyId :: DebugM m => DafnyId -> m DDoc
ppDafnyId (PId pn (ModuleTyVarId mn uid)) = do
    prefix <- ppModule mn
    let ppn = DIden pn
    puid <- pp uid
    let suffix = dtext "ShadowProc"
    return $ prefix <<>> ppn <<>> ddoc puid <<>> suffix    
ppDafnyId (FId pn (ModuleTyVarId mn uid) isLeak) = do
    prefix <- ppModule mn
    let ppn = DIden pn
    puid <- pp uid
    let suffix = if isLeak then dtext "ShadowFun" else dtext "OriginalFun"
    return $ prefix <<>> ppn <<>> ddoc puid <<>> suffix
ppDafnyId (LId pn (ModuleTyVarId mn uid) isLeak) = do
    prefix <- ppModule mn
    let ppn = DIden pn
    puid <- pp uid
    let suffix = if isLeak then dtext "ShadowLemma" else dtext "OriginalLemma"
    return $ prefix <<>> ppn <<>> ddoc puid <<>> suffix
ppDafnyId (SId sn (ModuleTyVarId mn uid)) = do
    prefix <- ppModule mn
    let psn = DIden sn
    puid <- pp uid
    let suffix = dempty
    return $ prefix <<>> psn <<>> ddoc puid <<>> suffix
ppDafnyId (AId (ModuleTyVarId mn uid) isLeak) = do
    prefix <- ppModule mn
    let psn = DIden $ PIden $ mkVarId "axiom"
    puid <- pp uid
    let suffix = if isLeak then dtext "ShadowAxiom" else dtext "OriginalAxiom"
    return $ prefix <<>> psn <<>> ddoc puid <<>> suffix

ppModuleName :: PP m VarIdentifier => Maybe (Identifier) -> m DDoc
ppModuleName Nothing = return $ dtext "BUILTIN"
ppModuleName (Just mn) = return $ dtext mn

ppModule :: PP m VarIdentifier => Maybe (Identifier,TyVarId) -> m DDoc
ppModule Nothing = return $ dtext "BUILTIN"
ppModule (Just (mn,blk)) = do
    ppblk <- pp blk
    return $ dtext mn <<>> dchar '_' <<>> ddoc ppblk

ppDafnyIdM :: DafnyK m => DafnyId -> DafnyM m DDoc
ppDafnyIdM did = lift $ ppDafnyId did

ppAnnLs xs = liftM vcat $ mapM ppAnnL xs
ppAnnL (_,_,vs,pe,_) = do
    pvs <- liftM (sepBy space) $ mapM pp $ Set.toList vs
    ppe <- pp pe
    return $ ppe <+> text "with variables" <+> pvs

-- dafny expressions

data DDoc = DIden GIdentifier
          | DDoc Doc
          | DLst ([Doc] -> Doc) [DDoc]
  deriving (Data,Typeable)
 
instance DebugM m => PP m DDoc where
    pp (DIden x) = dafnyGId x
    pp (DDoc x) = return x
    pp (DLst g xs) = do
        ys <- mapM pp xs
        return $ g ys
    
instance Show DDoc where
    show = show . ppid
instance Eq DDoc where
    x == y = show x == show y
instance Ord DDoc where
    compare x y = compare (show x) (show y)

mapDDoc :: (GIdentifier -> GIdentifier) -> DDoc -> DDoc
mapDDoc f (DIden x) = DIden $ f x
mapDDoc f (DDoc doc) = DDoc doc
mapDDoc f (DLst g xs) = DLst g $ map (mapDDoc f) xs

x <<+>> y = DLst hsep [x,y]
x $$+$$ y = DLst vcat [x,y]
x <<>> y = DLst hcat [x,y]
ddoc txt = DDoc txt
dtext str = DDoc $ text str
dchar c = DDoc $ char c
dsemicolon = ddoc semicolon
dcomma = ddoc comma
dparens x = DLst hcat [dchar '(',x,dchar ')']
dbraces x = DLst hcat [dchar '{',x,dchar '}']
dbrackets x = DLst hcat [dchar '[',x,dchar ']']
dvbraces x = DLst (vbraces . vcat) [x]
dabrackets x = DLst hcat [dchar '<',x,dchar '>']
dint i = ddoc $ PP.int i
dsepBy xs sep = DLst (sepBy sep) xs
dvcat xs = DLst vcat xs
dhcat xs = DLst hcat xs
dempty = DDoc $ PP.empty

dppOptM :: Monad m => Maybe a -> (a -> m DDoc) -> m DDoc
dppOptM Nothing f = return dempty
dppOptM (Just x) f = f x