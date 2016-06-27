{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.Transformation.Dafny where

import Language.SecreC.Syntax
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base
import Language.SecreC.Utils as Utils
import Language.SecreC.Pretty
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.Modules
import Language.SecreC.Prover.Semantics
import Language.SecreC.Vars

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

type POId = Either VarIdentifier (Op VarIdentifier ())

data DafnyId
    = PId POId ModuleTyVarId
    | FId POId ModuleTyVarId Bool
    | SId VarIdentifier ModuleTyVarId
    | AId ModuleTyVarId Bool
  deriving (Data,Typeable,Generic,Show,Eq,Ord)

isTypeDafnyId :: DafnyId -> Bool
isTypeDafnyId (SId {}) = True
isTypeDafnyId _ = False

dafnyIdLeak :: DafnyId -> Bool
dafnyIdLeak (PId _ tid) = False
dafnyIdLeak (FId _ tid b) = b
dafnyIdLeak (SId _ tid) = False
dafnyIdLeak (AId tid b) = b

dafnyIdModuleTyVarId :: DafnyId -> ModuleTyVarId
dafnyIdModuleTyVarId (PId _ tid) = tid
dafnyIdModuleTyVarId (FId _ tid _) = tid
dafnyIdModuleTyVarId (SId _ tid) = tid
dafnyIdModuleTyVarId (AId tid _) = tid

dafnyIdModule :: DafnyId -> Identifier
dafnyIdModule = fst . dafnyIdModuleTyVarId

data DafnySt = DafnySt {
      dafnies :: Map Identifier (Map DafnyId (Position,Doc)) -- generated Dafny entries (top-level variables, types, functions, methods), grouped by module
    , imports :: Map Identifier (Set Identifier)
    , leakageMode :: Bool -- True=leakage, False=correctness
    , axiomIds :: Set DafnyId
    , inDecl :: Maybe DafnyId
    }

getLeakMode :: DafnyK m => DafnyM m Bool
getLeakMode = State.gets leakageMode

whenLeakMode :: (Monoid x,DafnyK m) => DafnyM m x -> DafnyM m x
whenLeakMode m = do
    leakMode <- getLeakMode
    if leakMode then m else return mempty
    
withLeakMode :: DafnyK m => Bool -> DafnyM m x -> DafnyM m x
withLeakMode b m = do
    o <- getLeakMode
    State.modify $ \env -> env { leakageMode = b }
    x <- m
    State.modify $ \env -> env { leakageMode = o }
    return x
    
getInDecl :: DafnyK m => DafnyM m (Maybe DafnyId)
getInDecl = State.gets inDecl
    
insideDecl :: DafnyK m => DafnyId -> DafnyM m x -> DafnyM m x
insideDecl b m = do
    o <- getInDecl
    State.modify $ \env -> env { inDecl = Just b }
    x <- m
    State.modify $ \env -> env { inDecl = o }
    return x

toDafny :: DafnyK m => FilePath -> Bool -> [DafnyId] -> TcM m (Doc,[String])
toDafny prelude leakMode entries = flip State.evalStateT (DafnySt Map.empty Map.empty leakMode Set.empty Nothing) $ do
    dfy <- liftIO $ readFile prelude
    loadAxioms
    mapM_ loadDafnyId entries
    ds <- State.gets (Map.toList . dafnies)
    let modules = map fst ds
    (types,code) <- printDafnyModules ds
    let code' = text "module" <+> text "prelude" <+> vbraces (text dfy $+$ types) $+$ code
    axioms <- State.gets (Set.toList . axiomIds)
    paxioms <- mapM (boogieName modules) axioms
    return (code',paxioms)

boogieName :: DafnyK m => [Identifier] -> DafnyId -> DafnyM m String
boogieName modules did = do
    pdid <- ppDafnyIdM did
    return $ show $ text "InterModuleCall$$_" <> int mnum <> text "_" <> text mn <> text ".__default." <> pdid
  where
    mn = dafnyIdModule did
    mnum = fromJust $ List.lookup mn (zip modules [(2::Int)..])

loadAxioms :: DafnyK m => DafnyM m ()
loadAxioms = do
    env <- lift $ getModuleField True id
    let isLeakE = isLeakDec . unDecT . entryType
    let as = map (\(mid,e) -> AId mid $ isLeakE e) $ Map.toList $ axioms env
    mapM_ loadDafnyId as

isAxiomDafnyId :: DafnyId -> Bool
isAxiomDafnyId (AId {}) = True
isAxiomDafnyId _ = False

entryPointsTypedModuleFile :: DafnyK m => TypedModuleFile -> TcM m [DafnyId]
entryPointsTypedModuleFile (Left (_,_,m)) = return $ Set.toList $ collectDafnyIds m
entryPointsTypedModuleFile (Right sci) = do
    let env = sciEnv sci
    let decE = fromDecDafnyId . unDecT . entryType
    let ps = concat $ Map.elems $ Map.mapWithKey (\k vs -> map (\(mid,e) -> decE e) $ Map.toList vs) $ filterAnns False $ procedures env
    let os = concat $ Map.elems $ Map.mapWithKey (\k vs -> map (\(mid,e) -> decE e) $ Map.toList vs) $ filterAnns False $ operators env
    let ss = concat $ Map.elems $ Map.mapWithKey (\k vs -> map (\(mid,e) -> decE e) $ Map.toList vs) $ filterAnns False $ structs env
    return $ ps ++ os ++ ss

collectDafnyIds :: Data a => a -> Set DafnyId
collectDafnyIds = everything Set.union (mkQ Set.empty aux)
    where
    aux :: DecType -> Set DafnyId
    aux = Set.fromList . maybeToList . decDafnyId

decDafnyId :: DecType -> Maybe DafnyId
decDafnyId d@(DecType tid _ _ _ _ _ _ _ (ProcType _ pn _ _ _ _ _)) | not (isTemplateDecType d) = Just $ pIdenToDafnyId pn tid
decDafnyId d@(DecType tid _ _ _ _ _ _ _ (FunType isLeak _ pn _ _ _ _ _)) | not (isTemplateDecType d) = Just $ fIdenToDafnyId pn tid isLeak
decDafnyId d@(DecType tid _ _ _ _ _ _ _ (StructType _ (TypeName _ sn) _ _)) | not (isTemplateDecType d) = Just $ SId sn tid
decDafnyId d@(DecType tid _ _ _ _ _ _ _ (AxiomType {})) = Just $ AId tid False
decDafnyId dec = Nothing

fromDecDafnyId :: DecType -> DafnyId
fromDecDafnyId = fromJustNote "fromDecDafnyId" . decDafnyId

printDafnyModules :: DafnyK m => [(Identifier,Map DafnyId (Position,Doc))] -> DafnyM m (Doc,Doc)
printDafnyModules xs = do
    is <- State.gets imports
    (types,code) <- Utils.mapAndUnzipM (\(x,y) -> printDafnyModule x y is) xs
    return (vcat types,vcat code)

printDafnyModule :: DafnyK m => Identifier -> Map DafnyId (Position,Doc) -> Map Identifier (Set Identifier) -> DafnyM m (Doc,Doc)
printDafnyModule mn xs imports = do
    let (types,rest) = Map.partitionWithKey (\k v -> isTypeDafnyId k) xs
    let cmp (p1,_) (p2,_) = compare p1 p2
    let defstypes = vcat $ map snd $ List.sortBy cmp $ Map.elems types
    let defsrest = vcat $ map snd $ List.sortBy cmp $ Map.elems rest
    let is = maybe [] Set.toList $ Map.lookup mn imports 
    let pis = vcat $ map (\i -> text "import opened" <+> text i) ("prelude":is)
    return (defstypes,text "module" <+> pp mn <+> vbraces (pis $+$ defsrest))

resolveEntryPoint :: ProverK Position m => Identifier -> TcM m DafnyId
resolveEntryPoint n = do
    let n' = mkVarId n
    env <- getModuleField True id
    case Map.lookup n' (procedures env) of
        Just (Map.toList -> [(k,e)]) -> return $ fromDecDafnyId $ unDecT $ entryType e
        Nothing -> case Map.lookup n' (structs env) of
            Just (Map.toList -> [(k,e)]) -> return $ fromDecDafnyId $ unDecT $ entryType e
            Nothing -> genError noloc $ text "resolveEntryPoint: can't find" <+> pp n
            otherwise -> genError noloc $ text "resolveEntryPoint: ambiguous" <+> pp n
        otherwise -> genError noloc $ text "resolveEntryPoint: ambiguous" <+> pp n

getModule :: Monad m => DafnyM m Identifier
getModule = lift $ State.gets (fst . moduleCount)

withModule :: Monad m => Identifier -> DafnyM m a -> DafnyM m a
withModule c m = do
    oldc <- getModule
    lift $ State.modify $ \env -> env { moduleCount = let (_,i) = moduleCount env in (c,i) }
    x <- m
    lift $ State.modify $ \env -> env { moduleCount = let (_,i) = moduleCount env in (oldc,i) }
    return x

loadDafnyId :: DafnyK m => DafnyId -> DafnyM m ()
loadDafnyId n = do
    current <- getModule
    unless (current==mn) $ State.modify $ \env -> env { imports = Map.insertWith Set.union current (Set.singleton mn) (imports env) }
    withModule mn $ do
        leakMode <- getLeakMode
        docs <- State.gets (Map.map (Map.filterWithKey (\did v -> leakMode >= dafnyIdLeak did)) . dafnies)
        case Map.lookup mn docs of
            Just docs -> case Map.lookup n docs of
                Just _ -> return ()
                Nothing -> do
                    e <- lookupDafnyId n
                    State.modify $ \env -> env { dafnies = Map.update (Just . Map.insert n (noloc,empty)) mn $ dafnies env }
                    mb <- entryToDafny n e
                    case mb of
                        Nothing -> State.modify $ \env -> env { dafnies = Map.update (Just . Map.delete n) mn $ dafnies env }
                        Just doc -> State.modify $ \env -> env { dafnies = Map.update (Just . Map.insert n doc) mn $ dafnies env }
            Nothing -> do
                e <- lookupDafnyId n
                State.modify $ \env -> env { dafnies = Map.insert mn (Map.singleton n (noloc,empty)) $ dafnies env }
                mb <- entryToDafny n e
                case mb of
                    Nothing -> State.modify $ \env -> env { dafnies = Map.update (Just . Map.delete n) mn $ dafnies env }
                    Just doc -> State.modify $ \env -> env { dafnies = Map.update (Just . Map.insert n doc) mn $ dafnies env }
  where mn = dafnyIdModule n

lookupDafnyId :: DafnyK m => DafnyId -> DafnyM m EntryEnv
lookupDafnyId did@(SId sn tid@(m,_)) = do
    ss <- lift $ getModuleField True structs
    case Map.lookup sn ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(AId tid@(m,_) isLeak) = do
    as <- lift $ getModuleField True axioms
    case Map.lookup tid as of
        Just e -> return e
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(PId (Left pn) tid@(m,_)) = do
    ss <- lift $ getModuleField True procedures
    case Map.lookup pn ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(FId (Left pn) tid@(m,_) isLeak) = do
    ss <- lift $ getModuleField True procedures
    case Map.lookup pn ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(PId (Right on) tid@(m,_)) = do
    ss <- lift $ getModuleField True operators
    case Map.lookup on ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(FId (Right on) tid@(m,_) isLeak) = do
    ss <- lift $ getModuleField True operators
    case Map.lookup on ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did

entryToDafny :: DafnyK m => DafnyId -> EntryEnv -> DafnyM m (Maybe (Position,Doc))
entryToDafny n (EntryEnv p (DecT d)) = decToDafny n d

emptyDec (DecType tid Nothing [] ((==emptyPureTDict)->True) ((==mempty)->True) ((==emptyPureTDict)->True) ((==mempty)->True) [] t) = Just (tid,t)
emptyDec d = Nothing

targsDec (DecType tid Nothing ts ((==emptyPureTDict)->True) ((==mempty)->True) ((==emptyPureTDict)->True) ((==mempty)->True) [] t) = Just (tid,ts,t)
targsDec d = Nothing


pIdenToDafnyId :: PIdentifier -> ModuleTyVarId -> DafnyId
pIdenToDafnyId (Left n) mid = PId (Left n) mid
pIdenToDafnyId (Right n) mid = PId (Right $ funit n) mid

fIdenToDafnyId :: PIdentifier -> ModuleTyVarId -> Bool -> DafnyId
fIdenToDafnyId (Left n) mid isLeak = FId (Left n) mid isLeak
fIdenToDafnyId (Right n) mid isLeak = FId (Right $ funit n) mid isLeak

decToDafny :: DafnyK m => DafnyId -> DecType -> DafnyM m (Maybe (Position,Doc))
decToDafny n (emptyDec -> Just (mid,ProcType p pn args ret anns (Just body) cl)) = insideDecl did $ do
    ppn <- ppDafnyIdM did
    (pargs,parganns) <- procedureArgsToDafny False args
    (pret,pretanns,anns',body') <- case ret of
        ComplexT Void -> return (empty,empty,anns,body)
        ComplexT ct -> do
            result <- lift $ liftM (VarName (ComplexT ct)) $ genVar (mkVarId "result")
            let ss = TSubsts $ Map.singleton (mkVarId "\\result") (IdxT $ varExpr result)
            anns' <- lift $ substFromTSubsts "procedureToDafny" p ss False Map.empty anns
            body' <- lift $ substFromTSubsts "procedureToDafny" p ss False Map.empty body
            (pret,pretanns) <- procedureArgsToDafny True [(False,result,False)]
            return (text "returns" <+> pret,pretanns,anns',body')
        otherwise -> genError p $ text "procedureToDafny: unsupported return type" <+> pp ret
    pcl <- decClassToDafny cl
    panns <- procedureAnnsToDafny anns'
    pbody <- statementToDafny $ compoundStmt noloc body'
    return $ Just (p,text "method" <+> ppn <+> pargs <+> pret $+$ pcl $+$ parganns $+$ pretanns $+$ panns $+$ pbody)
  where did = pIdenToDafnyId pn mid
decToDafny n (emptyDec -> Just (mid,StructType p (TypeName _ sn) (Just atts) cl)) = insideDecl did $ do
    psn <- ppDafnyIdM did
    patts <- structAttsToDafny psn atts
    return $ Just (p,text "datatype" <+> psn <+> char '=' <+> psn <> parens patts)
  where did = SId sn mid
decToDafny n (targsDec -> Just (mid,targs,AxiomType isLeak p args anns cl)) = insideDecl did $ do
    leakMode <- getLeakMode
    if (leakMode >= isLeak)
        then do
            ptargs <- typeArgsToDafny targs
            (pargs,parganns) <- procedureArgsToDafny False args
            panns <- procedureAnnsToDafny anns
            pn <- ppDafnyIdM n
            State.modify $ \env -> env { axiomIds = Set.insert n $ axiomIds env }
            return $ Just (p,text "lemma" <+> pn <+> ptargs <+> pargs $+$ panns)
        else return Nothing
  where did = n
--decToDafny mid (FunType {}) = gen
decToDafny mid dec = genError noloc $ text "decToDafny:" <+> pp mid <+> pp dec

decClassToDafny :: DafnyK m => DecClass -> DafnyM m Doc
decClassToDafny (DecClass _ rs ws) = do
    let ppVar (v,t) = varToDafny $ VarName (Typed noloc t) v
    prs <- mapM ppVar $ Map.toList rs
    pws <- mapM ppVar $ Map.toList ws
    let pr = if null prs then empty else text "reads" <+> sepBy space prs
    let pw = if null pws then empty else text "modifies" <+> sepBy space pws
    return $ pr $+$ pw

structAttsToDafny :: DafnyK m => Doc -> [Attribute VarIdentifier Type] -> DafnyM m Doc
structAttsToDafny sn = liftM (sepBy comma) . (mapM (structAttToDafny True sn . attributeName))

structAttToDafny :: DafnyK m => Bool -> Doc -> AttributeName VarIdentifier Type -> DafnyM m Doc
structAttToDafny withType sn (AttributeName t n) = do
    pv <- varToDafny $ VarName (Typed noloc t) n
    pt <- if withType
        then liftM (char ':' <>) (typeToDafny t)
        else return empty
    return $ sn <> char '_' <> pv <> pt

typeArgsToDafny :: DafnyK m => [(Constrained Var,IsVariadic)] -> DafnyM m Doc
typeArgsToDafny xs = do
    pxs <- mapM typeArgToDafny xs
    return $ abrackets (sepBy comma $ catMaybes pxs)

typeArgToDafny :: DafnyK m => (Constrained Var,IsVariadic) -> DafnyM m (Maybe Doc)
typeArgToDafny cv@(Constrained v Nothing,False) = case typeClass "targ" (loc v) of
    (isType -> True) -> liftM Just $ dafnyVarIdM (varNameId v) -- there is a slight mismatch here: SecreC only supports base types while Dafny supports any type
    (isKind -> True) -> return Nothing
    (isDomain -> True) -> return Nothing
    otherwise -> genError noloc $ text "typeArgToDafny:" <+> pp cv 

procedureArgsToDafny :: DafnyK m => Bool -> [(Bool,Var,IsVariadic)] -> DafnyM m (Doc,Doc)
procedureArgsToDafny isPost xs = do
    (vs,as) <- Utils.mapAndUnzipM (procedureArgToDafny isPost) xs
    return (parens $ sepBy comma vs,vcat as)

procedureArgToDafny :: DafnyK m => Bool -> (Bool,Var,IsVariadic) -> DafnyM m (Doc,Doc)
procedureArgToDafny isPost (_,v,False) = do
    let annK = if isPost then EnsureK else RequireK
    pv <- varToDafny $ fmap (Typed noloc) v
    pt <- typeToDafny $ loc v
    annp <- genDafnyPublics False annK pv (loc v)
    return (pv <> char ':' <> pt,vcat annp)

dafnySize x = text "uint64" <> parens (char '|' <> x <> char '|')

qualifiedDafny :: DafnyK m => Type -> Doc -> DafnyM m Doc
qualifiedDafny t x = do
    pt <- typeToDafny t
    return $ parens (parens (text "x" <> char ':' <> pt) <+> text "=>" <+> text "x") <> parens x

genDafnyPublics :: DafnyK m => Bool -> AnnKind -> Doc -> Type -> DafnyM m [Doc]
genDafnyPublics True annK pv tv = return []
genDafnyPublics False annK pv tv = whenLeakMode $ do
    d <- getInDecl
    if isLeakageInDecl d
        then do
            let psize = dafnySize pv
            let publick = case annK of
                            StmtK -> "PublicMid"
                            InvariantK -> "PublicMid"
                            EnsureK -> "PublicOut"
                            RequireK -> "PublicIn"
            -- only generate publics for primitive types
            let genPublic t@(BaseT {}) = return $ Just $ annLine True annK (text publick <> parens pv)
                genPublic t@(ComplexT (CType s b d)) | isPublicSecType s && isPrimBaseType b = return $ Just $ annLine True annK (text publick <> parens pv)
                genPublic t = return Nothing
            -- only generate public sizes for private types
            let genPublicSize t@(ComplexT (CType s b d)) | not (isPublicSecType s) = do
                    let p = (noloc::Position)
                    mb <- lift $ tryError $ evaluateIndexExpr p d
                    case mb of
                        Right 0 -> return Nothing
                        Right 1 -> do
                            return $ Just $ annLine True annK (text publick <> parens psize)
                        otherwise -> genError p $ text "genPublicSize:" <+> pv <+> pp t
                genPublicSize t = return Nothing
            ispublic <- genPublic tv
            publicsize <- genPublicSize tv
            return $ maybeToList ispublic ++ maybeToList publicsize
        else return []
    
isLeakageInDecl :: Maybe DafnyId -> Bool
isLeakageInDecl Nothing = False
isLeakageInDecl (Just (PId {})) = True
isLeakageInDecl (Just (AId _ isLeak)) = isLeak
isLeakageInDecl (Just (SId {})) = False
isLeakageInDecl (Just (FId _ _ isLeak)) = isLeak
    
annLine :: Bool -> AnnKind -> Doc -> Doc
annLine isFree EnsureK x = ppFree isFree $ text "ensures" <+> x <+> semicolon
annLine isFree RequireK x = ppFree isFree $ text "requires" <+> x <+> semicolon
annLine True StmtK x = text "assume" <+> x <+> semicolon
annLine False StmtK x = text "assert" <+> x <+> semicolon
annLine isFree InvariantK x = ppFree isFree $ text "invariant" <+> x <+> semicolon
annLine isFree DecreaseK x = ppFree isFree $ text "decreases" <+> x <+> semicolon

procedureAnnsToDafny :: DafnyK m => [ProcedureAnnotation VarIdentifier (Typed Position)] -> DafnyM m Doc
procedureAnnsToDafny xs = liftM vcat $ mapM (procedureAnnToDafny) xs

procedureAnnToDafny :: DafnyK m => ProcedureAnnotation VarIdentifier (Typed Position) -> DafnyM m Doc
procedureAnnToDafny (RequiresAnn l isFree isLeak e) = do
    (anne,pe) <- expressionToDafny False RequireK e
    req <- annExpr isFree isLeak RequireK pe
    return $ vcat anne $+$ req
procedureAnnToDafny (EnsuresAnn l isFree isLeak e) = do
    (anne,pe) <- expressionToDafny False EnsureK e
    ens <- annExpr isFree isLeak EnsureK pe
    return $ vcat anne $+$ ens

statementsToDafny :: DafnyK m => [Statement VarIdentifier (Typed Position)] -> DafnyM m Doc
statementsToDafny = liftM vcat . mapM statementToDafny

statementToDafny :: DafnyK m => Statement VarIdentifier (Typed Position) -> DafnyM m Doc
statementToDafny (CompoundStatement _ ss) = do
    pss <- statementsToDafny ss
    return $ vbraces pss
statementToDafny (IfStatement _ c s1 s2) = do
    (annc,pc) <- expressionToDafny False StmtK c
    ps1 <- statementToDafny s1
    ps2 <- mapM statementToDafny s2
    return $ vcat annc $+$ text "if" <+> pc <+> ps1 $+$ pp ps2
statementToDafny (BreakStatement l) = return $ text "break" <> semicolon
statementToDafny (ContinueStatement l) = return $ text "continue" <> semicolon
statementToDafny (ReturnStatement l e) = do
    (anne,pe) <- mapExpressionToDafny False StmtK e
    return $ vcat anne $+$ text "return" <+> pp pe <> semicolon
statementToDafny (ExpressionStatement _ (BinaryAssign l le (BinaryAssignEqual _) re)) = do
    (pres,pre) <- expressionToDafny False StmtK re
    (post,pass) <- assignmentToDafny StmtK le (Left pre)
    return $ vcat pres $+$ pass <> semicolon $+$ vcat post
statementToDafny (ExpressionStatement l e) = do
    (anne,pe) <- expressionToDafny False StmtK e
    return $ vcat anne $+$ pe <> semicolon
statementToDafny (AssertStatement l e) = do
    (anne,pe) <- expressionToDafny False StmtK e
    assert <- annExpr False False StmtK pe
    return $ vcat anne $+$ assert
statementToDafny (AnnStatement l ss) = liftM vcat $ mapM statementAnnToDafny ss
statementToDafny (VarStatement l (VariableDeclaration _ isConst isHavoc t vs)) = do
    t' <- typeToDafny (typed $ loc t)
    liftM vcat $ mapM (varInitToDafny isConst isHavoc t') $ Foldable.toList vs
statementToDafny (WhileStatement l e anns s) = do
    (anne,pe) <- expressionToDafny False InvariantK e
    annl <- loopAnnsToDafny anns
    ps <- statementToDafny s
    return $ text "while" <+> pe $+$ vcat anne $+$ vcat annl $+$ vbraces (ps)    
statementToDafny s = genError noloc $ text "statementToDafny:" <+> pp s

loopAnnsToDafny :: DafnyK m => [LoopAnnotation VarIdentifier (Typed Position)] -> DafnyM m [Doc]
loopAnnsToDafny xs = liftM concat $ mapM loopAnnToDafny xs

annExpr :: DafnyK m => Bool -> Bool -> AnnKind -> Doc -> DafnyM m Doc
annExpr isFree isLeak annK e = do
    leakMode <- getLeakMode
    case (leakMode,isLeak) of
        (True,True) -> return $ annLine isFree annK e
        (True,False) -> return $ annLine True annK e
        (False,True) -> return empty
        (False,False) -> return $ annLine isFree annK e
    
loopAnnToDafny :: DafnyK m => LoopAnnotation VarIdentifier (Typed Position) -> DafnyM m [Doc]
loopAnnToDafny (DecreasesAnn l isLeak e) = do
    (anne,pe) <- expressionToDafny False InvariantK e
    decrease <- annExpr False isLeak DecreaseK pe
    return $ anne ++ [decrease]
loopAnnToDafny (InvariantAnn l isFree isLeak e) = do
    (anne,pe) <- expressionToDafny False InvariantK e
    inv <- annExpr isFree isLeak InvariantK pe
    return $ anne ++ [inv]

statementAnnToDafny :: DafnyK m => StatementAnnotation VarIdentifier (Typed Position) -> DafnyM m Doc
statementAnnToDafny (AssumeAnn l isLeak e) = do
    (anne,pe) <- expressionToDafny False StmtK e
    assume <- annExpr True isLeak StmtK pe
    return $ vcat anne $+$ assume
statementAnnToDafny (AssertAnn l isLeak e) = do
    (anne,pe) <- expressionToDafny False StmtK e
    assert <- annExpr False isLeak StmtK pe
    return $ vcat anne $+$ assert

-- TODO: ignore sizes?
varInitToDafny :: DafnyK m => Bool -> Bool -> Doc -> VariableInitialization VarIdentifier (Typed Position) -> DafnyM m Doc
varInitToDafny isConst False pty vd@(VariableInitialization l v sz (Just e)) = genError noloc $ text "varInitToDafny: cannot convert default expression at" <+> pp vd
varInitToDafny isConst isHavoc pty (VariableInitialization l v sz ini) = do
    pv <- varToDafny v
    let def = text "var" <+> pv <> char ':' <> pty <> semicolon
    annp <- genDafnyPublics False StmtK pv (typed $ loc v)
    (annsini,pini) <- mapExpressionToDafny False StmtK ini
    let assign = ppOpt pini (\e -> pv <+> text ":=" <+> e <+> semicolon)
    return $ def $+$ vcat annsini $+$ assign $+$ vcat annp

typeToDafny :: DafnyK m => Type -> DafnyM m Doc
typeToDafny (BaseT b) = baseTypeToDafny b
typeToDafny (ComplexT t) = complexTypeToDafny t
typeToDafny t = genError noloc $ text "typeToDafny:" <+> pp t

baseTypeToDafny :: DafnyK m => BaseType -> DafnyM m Doc
baseTypeToDafny (BVar v) = dafnyVarIdM v
baseTypeToDafny (TyPrim prim) = return $ pp prim
baseTypeToDafny (MSet b) = do
    b' <- baseTypeToDafny b
    return $ text "multiset" <> abrackets b'
baseTypeToDafny (TApp _ args dec@(decTypeTyVarId -> Just mid)) = do
    let did = fromDecDafnyId dec
    loadDafnyId did
    psn <- ppDafnyIdM did
    let ppArg (t,False) = typeToDafny t
        ppArg (t,True) = genError noloc $ text "baseTypeToDafny: variadic argument" <+> pp t
    args' <- mapM ppArg args
    let pargs = if null args' then empty else abrackets $ sepBy comma args'
    return $ psn <> pargs
--baseTypeToDafny t = genError noloc $ text "baseTypeToDafny:" <+> pp t

complexTypeToDafny :: DafnyK m => ComplexType -> DafnyM m Doc
complexTypeToDafny t@(CType s b d) = do
    let p = noloc::Position
    pb <- baseTypeToDafny b
    mb <- lift $ tryError $ evaluateIndexExpr p d
    case mb of
        Right 0 -> return pb
        Right 1 -> return $ text "seq" <> abrackets pb
        Left err -> throwError $ GenericError p (text "complexTypeToDafny:" <+> pp t) $ Just err
complexTypeToDafny t = genError noloc $ text "complexTypeToDafny:" <+> pp t

data AnnKind = StmtK | EnsureK | RequireK | InvariantK | DecreaseK
  deriving Show
instance PP AnnKind where
    pp = text . show

indexToDafny :: DafnyK m => Bool -> AnnKind -> Index VarIdentifier (Typed Position) -> DafnyM m ([Doc],Doc)
indexToDafny isLVal annK (IndexInt l e) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    return (anne,pe)
indexToDafny isLVal annK (IndexSlice l e1 e2) = do
    (anne1,pe1) <- mapExpressionToDafny isLVal annK e1
    (anne2,pe2) <- mapExpressionToDafny isLVal annK e2
    return (anne1++anne2,pp pe1 <> text ".." <> pp pe2)

-- left = expression, right = update
assignmentToDafny :: DafnyK m => AnnKind -> Expression VarIdentifier (Typed Position) -> Either Doc Doc -> DafnyM m ([Doc],Doc)
assignmentToDafny annK se@(SelectionExpr l e att) (Left pre) = do
    dec <- tAppDec $ typed $ loc e
    psn <- ppDafnyIdM $ fromDecDafnyId dec
    patt <- structAttToDafny False psn $ fmap typed att
    (annse,_) <- expressionToDafny True annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ char '.' <> parens (patt <+> text ":=" <+> pre))
    return (annse++ann,doc)
assignmentToDafny annK se@(SelectionExpr l e att) (Right upd) = do
    dec <- tAppDec $ typed $ loc e
    psn <- ppDafnyIdM $ fromDecDafnyId dec
    patt <- structAttToDafny False psn $ fmap typed att
    (annse,pse) <- expressionToDafny True annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ char '.' <> parens (patt <+> text ":=" <+> pse <> upd))
    return (annse++ann,doc)
assignmentToDafny annK se@(PostIndexExpr l e (Foldable.toList -> [i])) (Left pre) = do
    (anni,pi) <- indexToDafny True annK i
    (annse,_) <- expressionToDafny True annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ brackets (text "int" <> parens pi <+> text ":=" <+> pre))
    return (anni++annse++ann,doc)
assignmentToDafny annK se@(PostIndexExpr l e (Foldable.toList -> [i])) (Right upd) = do
    (anni,pi) <- indexToDafny True annK i
    (annse,pse) <- expressionToDafny True annK se
    (ann,doc) <- assignmentToDafny annK e (Right $ brackets (text "int" <> parens pi <+> text ":=" <+> pse <> upd))
    return (anni++annse++ann,doc)
assignmentToDafny annK e@(RVariablePExpr {}) (Left pre) = do
    (anne,pe) <- expressionToDafny True annK e
    return (anne,pe <+> text ":=" <+> pre)
assignmentToDafny annK e@(RVariablePExpr {}) (Right upd) = do
    (anne,pe) <- expressionToDafny True annK e
    return (anne,pe <+> text ":=" <+> pe <> upd)
assignmentToDafny annK e pre = genError noloc $ text "assignmentToDafny:" <+> pp annK <+> pp e <+> pp pre

tAppDec :: DafnyK m => Type -> DafnyM m DecType
tAppDec t@(BaseT (TApp _ _ d)) = return d
tAppDec t@(ComplexT (CType Public b d)) = do
    let l = noloc::Position
    mbd <- lift $ tryError $ evaluateIndexExpr l d
    case mbd of
        Right 0 -> tAppDec (BaseT b)
        otherwise -> genError l $ text "tAppDec: unsupported type" <+> pp t
tAppDec t = genError noloc $ text "tAppDec: unsupported type" <+> pp t

hasLeakExpr :: Expression VarIdentifier (Typed Position) -> Bool
hasLeakExpr = everything (||) (mkQ False aux)
    where
    aux :: Expression VarIdentifier (Typed Position) -> Bool
    aux (LeakExpr {}) = True
    aux _ = False

expressionToDafny :: DafnyK m => Bool -> AnnKind -> Expression VarIdentifier (Typed Position) -> DafnyM m ([Doc],Doc)
expressionToDafny isLVal annK se@(PostIndexExpr l e (Foldable.toList -> [i])) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    (anni,pi) <- indexToDafny isLVal annK i
    let pse = pe <> brackets pi
    annp <- genDafnyPublics (hasLeakExpr se) annK pse (typed l)
    return (anne++anni++annp,pse)
expressionToDafny isLVal annK se@(SelectionExpr l e att) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    dec <- tAppDec $ typed $ loc e
    psn <- ppDafnyIdM $ fromDecDafnyId dec
    patt <- structAttToDafny False psn $ fmap typed att
    let pse = pe <> char '.' <> patt
    annp <- genDafnyPublics (hasLeakExpr se) annK pse (typed l)
    -- always assert equality of projection, if it is a base type, since we don't do so when declaring the struct variable
    return (anne++annp,pse)
expressionToDafny isLVal annK e@(RVariablePExpr l v) = do
    pv <- varToDafny v
    annp <- genDafnyPublics (hasLeakExpr e) annK pv (typed $ loc v)
    return (annp,pv)
expressionToDafny isLVal annK (LitPExpr l lit) = literalToDafny lit
expressionToDafny isLVal annK (LeakExpr l e) = do
    (anne,pe) <- expressionToDafny False annK e
    return (anne,text "Leak" <> parens pe)
expressionToDafny isLVal annK (QualExpr l e _) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    --pqe <- qualifiedDafny (typed l) pe
    return (anne,pe)
expressionToDafny isLVal annK (MultisetConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let pme = text "multiset" <> braces (sepBy comma pes)
    pme' <- if List.null pes then qualifiedDafny (typed l) pme else return pme
    return (annes,pme')
expressionToDafny isLVal annK (ArrayConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    let pae = brackets (sepBy comma pes)
    pae' <- if List.null pes then qualifiedDafny (typed l) pae else return pae
    return (annes,pae')
expressionToDafny isLVal annK me@(ToMultisetExpr l e) = do
    (anne,pe) <- expressionToDafny False annK e
    let pme = text "multiset" <> parens pe
    annp <- genDafnyPublics (hasLeakExpr me) annK pme (typed l)
    return (anne++annp,pme)
expressionToDafny isLVal annK be@(BuiltinExpr l n es) = do
    (ann,pbe) <- builtinToDafny isLVal annK l n es
    annp <- genDafnyPublics (hasLeakExpr be) annK pbe (typed l)
    return (ann++annp,pbe)
expressionToDafny isLVal annK e@(ProcCallExpr l (ProcedureName (Typed _ dec) n) targs args) = do
    let did = fromDecDafnyId (unDecT dec)
    loadDafnyId did
    (annargs,pargs) <- procCallArgsToDafny isLVal annK args
    pn <- ppDafnyIdM did
    let pe = pn <> parens (sepBy comma pargs)
    annp <- genDafnyPublics (hasLeakExpr e) annK pe (typed l)
    return (annargs++annp,pe)
expressionToDafny isLVal annK e@(BinaryExpr l e1 op e2) = genError noloc $ text "expressionToDafny: unsupported binary procedure call" <+> pp e <+> pp (typed $ loc op)
expressionToDafny isLVal annK qe@(QuantifiedExpr l q args e) = do
    let pq = quantifierToDafny q
    (pargs) <- quantifierArgsToDafny args
    (anne,pe) <- expressionToDafny isLVal annK e
    return (anne,parens (pq <+> pargs <+> text "::" <+> pe))
expressionToDafny isLVal annK e = genError noloc $ text "expressionToDafny:" <+> pp isLVal <+> pp annK <+> pp e

quantifierToDafny :: Quantifier (Typed Position) -> Doc
quantifierToDafny (ForallQ _) = text "forall"
quantifierToDafny (ExistsQ _) = text "exists"

quantifierArgsToDafny :: DafnyK m => [(TypeSpecifier VarIdentifier (Typed Position),VarName VarIdentifier (Typed Position))] -> DafnyM m (Doc)
quantifierArgsToDafny xs = do
    (vs) <- mapM quantifierArgToDafny xs
    return (sepBy comma vs)

quantifierArgToDafny :: DafnyK m => (TypeSpecifier VarIdentifier (Typed Position),VarName VarIdentifier (Typed Position)) -> DafnyM m (Doc)
quantifierArgToDafny (t,v) = do
    pv <- varToDafny v
    pt <- typeToDafny $ typed $ loc v
    return (pv <> char ':' <> pt)

expressionsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression VarIdentifier (Typed Position)) -> DafnyM m ([Doc],[Doc])
expressionsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (expressionToDafny isLVal annK) $ Foldable.toList es
    return (concat annes,es')

mapExpressionToDafny :: (Functor f,Traversable f,Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression VarIdentifier (Typed Position)) -> DafnyM m ([Doc],f Doc)
mapExpressionToDafny isLVal annK es = do
    rs <- mapM (expressionToDafny isLVal annK) es
    return (concat $ Foldable.toList $ fmap fst rs,fmap snd rs)

procCallArgsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression VarIdentifier (Typed Position),IsVariadic) -> DafnyM m ([Doc],[Doc])
procCallArgsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (procCallArgToDafny isLVal annK) $ Foldable.toList es
    return (concat annes,es')
    
procCallArgToDafny :: DafnyK m => Bool -> AnnKind -> (Expression VarIdentifier (Typed Position),IsVariadic) -> DafnyM m ([Doc],Doc)
procCallArgToDafny isLVal annK (e,False) = expressionToDafny isLVal annK e
procCallArgToDafny isLVal annK (e,True) = genError noloc $ text "unsupported variadic procedure argument" <+> pp e

builtinToDafny :: DafnyK m => Bool -> AnnKind -> Typed Position -> String -> [Expression VarIdentifier (Typed Position)] -> DafnyM m ([Doc],Doc)
builtinToDafny isLVal annK (Typed l ret) "core.eq" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "==" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.band" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "&&" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.bor" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "||" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.lt" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "<" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.le" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "<=" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.gt" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text ">" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.ge" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text ">=" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.implies" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "==>" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.subset" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "<=" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.union" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "+" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.add" [x,y] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    return (annx++anny,parens $ px <> text "+" <> py)
builtinToDafny isLVal annK (Typed l ret) "core.declassify" [x] = do -- we ignore security types
    (annx,px) <- expressionToDafny isLVal annK x
    leakMode <- getLeakMode
    if leakMode
        then do
            let assert = text "assert" <> parens (text "DeclassifiedIn" <> parens px) <> semicolon
            return (annx++[assert],px)
        else return (annx,px)
builtinToDafny isLVal annK (Typed l ret) "core.classify" [x] = do -- we ignore security types
    expressionToDafny isLVal annK x
builtinToDafny isLVal annK (Typed l ret) "core.cat" [x,y,n] = do
    (annx,px) <- expressionToDafny isLVal annK x
    (anny,py) <- expressionToDafny isLVal annK y
    let tx = typed $ loc x
    case tx of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryError $ evaluateIndexExpr l d
            mbn <- lift $ tryError $ evaluateIndexExpr l $ fmap typed n
            case (mbd,mbn) of
                (Right 1,Right 0) -> return (annx++anny,parens $ px <+> char '+' <+> py)
                (err1,err2) -> genError noloc $ text "builtinToDafny: unsupported cat dimension" <+> pp x <+> pp y <+> pp n <+> vcat (map pp $ lefts [err1,err2])
        otherwise -> genError noloc $ text "builtinToDafny: unsupported cat type" <+> pp x <+> pp y <+> pp n <+> pp tx
builtinToDafny isLVal annK (Typed l ret) "core.size" [x] = do
    (annx,px) <- expressionToDafny isLVal annK x
    let tx = typed $ loc x
    case tx of
        BaseT b -> return (annx,dafnySize px)
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryError $ evaluateIndexExpr l d
            case mbd of
                Right 0 -> return (annx,dafnySize px)
                Right 1 -> return (annx,dafnySize px)
                otherwise -> genError noloc $ text "builtinToDafny: unknown size" <+> pp x <+> pp tx
        otherwise -> genError noloc $ text "builtinToDafny: unknown size" <+> pp x <+> pp tx
builtinToDafny isLVal annK (Typed l ret) "core.shape" [x] = do
    (annx,px) <- expressionToDafny isLVal annK x
    let tx = typed $ loc x
    case tx of
        BaseT b -> return (annx,brackets empty)
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryError $ evaluateIndexExpr l d
            case mbd of
                Right 0 -> return (annx,brackets empty)
                Right 1 -> return (annx,brackets $ dafnySize px)
                otherwise -> genError noloc $ text "builtinToDafny: unknown shape" <+> pp x <+> pp tx
        otherwise -> genError noloc $ text "builtinToDafny: unknown shape" <+> pp x <+> pp tx
builtinToDafny isLVal annK ret n es = genError noloc $ text "builtinToDafny:" <+> pp isLVal <+> pp annK <+> pp ret <+> pp n <+> pp es

literalToDafny :: DafnyK m => Literal (Typed Position) -> DafnyM m ([Doc],Doc)
literalToDafny lit = do
    let t = typed $ loc lit
    case t of
        ((==BaseT bool) -> True) -> return ([],pp lit)
        ((==BaseT string) -> True) -> return ([],pp lit)
        (isNumericType -> True) -> do
            pt <- typeToDafny (typed $ loc lit)
            return ([],pt <> parens (pp lit))

varToDafny :: DafnyK m => VarName VarIdentifier (Typed Position) -> DafnyM m Doc
varToDafny (VarName (Typed l t) n) = do
    let suffix = if isPublicType t then "Public" else "Private"
    dn <- dafnyVarIdM n
    return $ dn <> text suffix

dafnyVarId :: Identifier -> VarIdentifier -> Doc
dafnyVarId current v = pm <> text (varIdBase v) <> pid
    where
    pm = case varIdModule v of
            Nothing -> empty
            Just m -> text m <> char '_'
    pid = ppOpt (varIdUniq v) (\x -> char '_' <> pp x)

dafnyVarIdM :: DafnyK m => VarIdentifier -> DafnyM m Doc
dafnyVarIdM v = do
    current <- getModule
    return $ dafnyVarId current v

instance PP DafnyId where
    pp did = ppDafnyId (dafnyIdModule did) did

ppPOId :: Identifier -> POId -> Doc
ppPOId current (Left pn) = dafnyVarId current pn
ppPOId current (Right _) = error "unsupported operator"

ppDafnyId :: Identifier -> DafnyId -> Doc
ppDafnyId current (PId pn (mn,uid)) = prefix <> ppn <> pp uid <> suffix
    where
    ppn = ppPOId current pn
    prefix = text mn 
    suffix = empty
ppDafnyId current (FId on (mn,uid) isLeak) = error $ show $ text "ppDafnyId: function not supported" <+> pp on
ppDafnyId current (SId sn (mn,uid)) = prefix <> psn <> pp uid <> suffix
    where
    psn = dafnyVarId current sn
    prefix = text mn 
    suffix = empty
ppDafnyId current (AId (mn,uid) isLeak) = prefix <> psn <> pp uid <> suffix
    where
    psn = dafnyVarId current $ mkVarId "axiom"
    prefix = text mn 
    suffix = if isLeak then text "Leakage" else empty

ppDafnyIdM :: DafnyK m => DafnyId -> DafnyM m Doc
ppDafnyIdM did = do
    current <- getModule
    return $ ppDafnyId current did


