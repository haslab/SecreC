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

import GHC.Generics

import Control.Monad
import Control.Monad.Trans
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State

type DafnyK m = ProverK Position m
type DafnyM m = StateT DafnySt (TcM m)

data DafnyId
    = PId VarIdentifier ModuleTyVarId Bool
    | OId (Op VarIdentifier ()) ModuleTyVarId Bool
    | SId VarIdentifier ModuleTyVarId Bool
    | AId ModuleTyVarId Bool
  deriving (Data,Typeable,Generic,Show,Eq,Ord)

dafnyIdLeak :: DafnyId -> Bool
dafnyIdLeak (PId _ tid b) = b
dafnyIdLeak (OId _ tid b) = b
dafnyIdLeak (SId _ tid b) = b
dafnyIdLeak (AId tid b) = b

dafnyIdModuleTyVarId :: DafnyId -> ModuleTyVarId
dafnyIdModuleTyVarId (PId _ tid _) = tid
dafnyIdModuleTyVarId (OId _ tid _) = tid
dafnyIdModuleTyVarId (SId _ tid _) = tid
dafnyIdModuleTyVarId (AId tid _) = tid

dafnyIdModule :: DafnyId -> Identifier
dafnyIdModule = fst . dafnyIdModuleTyVarId

data DafnySt = DafnySt {
      dafnies :: Map Identifier (Map DafnyId (Position,Doc)) -- generated Dafny entries (top-level variables, functions, methods), grouped by module
    , leakageMode :: Bool -- True=leakage, False=correctness
    , axiomIds :: Set DafnyId
    }

getLeakMode :: DafnyK m => DafnyM m Bool
getLeakMode = State.gets leakageMode

whenLeakMode :: (Monoid x,DafnyK m) => DafnyM m x -> DafnyM m x
whenLeakMode m = do
    leakMode <- getLeakMode
    if leakMode then m else return mempty

toDafny :: DafnyK m => FilePath -> Bool -> [DafnyId] -> TcM m (Doc,[String])
toDafny leakPrelude leakMode entries = flip State.evalStateT (DafnySt Map.empty leakMode Set.empty) $ do
    loadAxioms
    mapM_ loadDafnyId entries
    ds <- State.gets (Map.toList . dafnies)
    code <- printDafnyModules ds
    code' <- if leakMode
        then do
            dfyLeak <- liftIO $ readFile leakPrelude
            return $ text dfyLeak $+$ code
        else return code
    axioms <- State.gets (Set.toList . axiomIds)
    paxioms <- mapM (liftM show . ppDafnyIdM) axioms
    return (code',paxioms)

loadAxioms :: DafnyK m => DafnyM m ()
loadAxioms = do
    env <- lift $ getModuleField id
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
    let isLeakE = isLeakDec . unDecT . entryType
    let ps = concat $ Map.elems $ Map.mapWithKey (\k vs -> map (\(mid,e) -> PId k mid $ isLeakE e) $ Map.toList vs) $ filterAnns False $ procedures env
    let os = concat $ Map.elems $ Map.mapWithKey (\k vs -> map (\(mid,e) -> OId k mid $ isLeakE e) $ Map.toList vs) $ filterAnns False $ operators env
    let ss = concat $ Map.elems $ Map.mapWithKey (\k vs -> map (\(mid,e) -> SId k mid $ isLeakE e) $ Map.toList vs) $ filterAnns False $ structs env
    return $ ps ++ os ++ ss

collectDafnyIds :: Data a => a -> Set DafnyId
collectDafnyIds = everything Set.union (mkQ Set.empty aux)
    where
    aux :: DecType -> Set DafnyId
    aux (DecType tid Nothing [] ((==emptyPureTDict)->True) ((==mempty)->True) ((==emptyPureTDict)->True) ((==mempty)->True) [] (ProcType _ pn _ _ _ _ _)) = Set.singleton $ pIdenToDafnyId pn tid False
    aux (DecType tid Nothing [] ((==emptyPureTDict)->True) ((==mempty)->True) ((==emptyPureTDict)->True) ((==mempty)->True) [] (FunType isLeak _ pn _ _ _ _ _)) = Set.singleton $ pIdenToDafnyId pn tid isLeak
    aux (DecType tid Nothing [] ((==emptyPureTDict)->True) ((==mempty)->True) ((==emptyPureTDict)->True) ((==mempty)->True) [] (StructType _ (TypeName _ sn) _ _)) = Set.singleton $ SId sn tid False
    aux (DecType tid Nothing [] ((==emptyPureTDict)->True) ((==mempty)->True) ((==emptyPureTDict)->True) ((==mempty)->True) [] (AxiomType {})) = Set.singleton $ AId tid False
    aux _ = Set.empty

printDafnyModules :: DafnyK m => [(Identifier,Map DafnyId (Position,Doc))] -> DafnyM m Doc
printDafnyModules = liftM vcat . mapM (uncurry printDafnyModule)

printDafnyModule :: DafnyK m => Identifier -> Map DafnyId (Position,Doc) -> DafnyM m Doc
printDafnyModule mn xs = do
    let cmp (p1,_) (p2,_) = compare p1 p2
    let defs = vcat $ map snd $ List.sortBy cmp $ Map.elems xs
    return $ text "module" <+> pp mn <+> vbraces defs

resolveEntryPoint :: ProverK Position m => Identifier -> TcM m DafnyId
resolveEntryPoint n = do
    let n' = mkVarId n
    env <- getModuleField id
    case Map.lookup n' (procedures env) of
        Just (Map.toList -> [(k,e)]) -> return $ PId n' k (isLeakDec $ unDecT $ entryType e)
        Nothing -> case Map.lookup n' (structs env) of
            Just (Map.toList -> [(k,e)]) -> return $ SId n' k (isLeakDec $ unDecT $ entryType e)
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
loadDafnyId n = withModule mn $ do
    leakMode <- getLeakMode
    docs <- State.gets (Map.map (Map.filterWithKey (\did v -> leakMode >= dafnyIdLeak did)) . dafnies)
    case Map.lookup mn docs of
        Just docs -> case Map.lookup n docs of
            Just _ -> return ()
            Nothing -> do
                e <- lookupDafnyId n
                mb <- entryToDafny n e
                case mb of
                    Nothing -> return ()
                    Just doc -> State.modify $ \env -> env { dafnies = Map.update (Just . Map.insert n doc) mn $ dafnies env }
        Nothing -> do
            e <- lookupDafnyId n
            mb <- entryToDafny n e
            case mb of
                Nothing -> return ()
                Just doc -> State.modify $ \env -> env { dafnies = Map.insert mn (Map.singleton n doc) $ dafnies env }
  where mn = dafnyIdModule n

lookupDafnyId :: DafnyK m => DafnyId -> DafnyM m EntryEnv
lookupDafnyId did@(SId sn tid@(m,_) isLeak) = do
    ss <- lift $ getModuleField structs
    case Map.lookup sn ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(AId tid@(m,_) isLeak) = do
    as <- lift $ getModuleField axioms
    case Map.lookup tid as of
        Just e -> return e
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(PId pn tid@(m,_) isLeak) = do
    ss <- lift $ getModuleField procedures
    case Map.lookup pn ss of
        Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
        Just es -> case Map.lookup tid es of
            Just e -> return e
            Nothing -> genError noloc $ text "lookupDafnyId: can't find" <+> pp did
lookupDafnyId did@(OId on tid@(m,_) isLeak) = do
    ss <- lift $ getModuleField operators
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


pIdenToDafnyId :: PIdentifier -> ModuleTyVarId -> Bool -> DafnyId
pIdenToDafnyId (Left n) mid isLeak = PId n mid isLeak
pIdenToDafnyId (Right n) mid isLeak = OId (funit n) mid isLeak

decToDafny :: DafnyK m => DafnyId -> DecType -> DafnyM m (Maybe (Position,Doc))
decToDafny n (emptyDec -> Just (mid,ProcType p pn args ret anns (Just body) cl)) = do
    let did = pIdenToDafnyId pn mid False
    ppn <- ppDafnyIdM did
    (pargs,parganns) <- procedureArgsToDafny False args
    (pret,pretanns,anns',body') <- case ret of
        ComplexT Void -> return (empty,empty,anns,body)
        ComplexT ct -> do
            result <- lift $ liftM (VarName (ComplexT ct)) $ genVar (mkVarId "result")
            let ss = TSubsts $ Map.singleton (mkVarId "\\result") (IdxT $ varExpr result)
            anns' <- lift $ substFromTSubsts "procedureToDafny" p ss False Map.empty anns
            body' <- lift $ substFromTSubsts "procedureToDafny" p ss False Map.empty body
            (pret,pretanns) <- procedureArgsToDafny True [(False,Constrained result Nothing,False)]
            return (text "returns" <+> pret,pretanns,anns',body')
        otherwise -> genError p $ text "procedureToDafny: unsupported return type" <+> pp ret
    pcl <- decClassToDafny cl
    panns <- procedureAnnsToDafny anns'
    pbody <- statementToDafny $ compoundStmt noloc body'
    return $ Just (p,text "method" <+> ppn <+> pargs <+> pret $+$ pcl $+$ parganns $+$ pretanns $+$ panns $+$ pbody)
decToDafny n (emptyDec -> Just (mid,StructType p (TypeName _ sn) (Just atts) cl)) = do
    psn <- ppDafnyIdM $ SId sn mid False
    patts <- structAttsToDafny atts
    return $ Just (p,text "datatype" <+> psn <+> char '=' <+> psn <> parens patts)
decToDafny n (targsDec -> Just (mid,targs,AxiomType isLeak p args anns cl)) = do
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

structAttsToDafny :: DafnyK m => [AttributeName VarIdentifier Type] -> DafnyM m Doc
structAttsToDafny = liftM (sepBy comma) . (mapM structAttToDafny)

structAttToDafny :: DafnyK m => AttributeName VarIdentifier Type -> DafnyM m Doc
structAttToDafny (AttributeName t n) = do
    pv <- varToDafny $ VarName (Typed noloc t) n
    pt <- typeToDafny t
    return $ pv <> char ':' <> pt

typeArgsToDafny :: DafnyK m => [(Constrained Var,IsVariadic)] -> DafnyM m Doc
typeArgsToDafny xs = do
    pxs <- mapM typeArgToDafny xs
    return $ abrackets (sepBy comma $ catMaybes pxs)

typeArgToDafny :: DafnyK m => (Constrained Var,IsVariadic) -> DafnyM m (Maybe Doc)
typeArgToDafny cv@(Constrained v Nothing,False) = case typeClass "targ" (loc v) of
    (isType -> True) -> liftM Just $ varToDafny (fmap (Typed noloc) v) -- there is a slight mismatch here: SecreC only supports base types while Dafny supports any type
    (isKind -> True) -> return Nothing
    (isDomain -> True) -> return Nothing
    otherwise -> genError noloc $ text "typeArgToDafny:" <+> pp cv 

procedureArgsToDafny :: DafnyK m => Bool -> [(Bool,Constrained Var,IsVariadic)] -> DafnyM m (Doc,Doc)
procedureArgsToDafny isPost xs = do
    (vs,as) <- Utils.mapAndUnzipM (procedureArgToDafny isPost) xs
    return (parens $ sepBy comma vs,vcat as)

procedureArgToDafny :: DafnyK m => Bool -> (Bool,Constrained Var,IsVariadic) -> DafnyM m (Doc,Doc)
procedureArgToDafny isPost (_,Constrained v e,False) = do
    let annK = if isPost then EnsureK else RequireK
    pv <- varToDafny $ fmap (Typed noloc) v
    pt <- typeToDafny $ loc v
    (anne,pe) <- mapExpressionToDafny False annK $ fmap (fmap (Typed noloc)) e
    publics <- genDafnyPublics annK pv (loc v)
    return (pv <> char ':' <> pt,vcat anne $+$ vcat (map (annLine False annK) (maybeToList pe) ++ publics))

genDafnyPublics :: DafnyK m => AnnKind -> Doc -> Type -> DafnyM m [Doc]
genDafnyPublics annK pv tv = whenLeakMode $ do
    let psize = char '|' <> pv <> char '|'
    let publick = case annK of
                    StmtK -> "PublicMid"
                    InvariantK -> "PublicMid"
                    EnsureK -> "PublicOut"
                    RequireK -> "PublicIn"
    let ispublic = if isPublicType tv then Just (annLine True annK (text publick <> parens pv)) else Nothing
    let genPublicSize t@(ComplexT (CType s b d)) | not (isPublicSecType s) = do
            let p = (noloc::Position)
            mb <- lift $ tryError $ evaluateIndexExpr p d
            case mb of
                Right 0 -> return Nothing
                Right 1 -> do
                    return $ Just $ annLine True annK (text publick <> parens psize)
                otherwise -> genError p $ text "genPublicSize:" <+> pv <+> pp t
        genPublicSize t = return Nothing
    publicsize <- genPublicSize tv
    return $ maybeToList ispublic ++ maybeToList publicsize
    
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
    return $ vcat anne $+$ annLine (isFree) RequireK pe
procedureAnnToDafny (EnsuresAnn l isFree isLeak e) = do
    (anne,pe) <- expressionToDafny False EnsureK e
    return $ vcat anne $+$ annLine (isFree) EnsureK pe

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
    (post,ple) <- expressionToDafny True StmtK le
    (pres,pre) <- expressionToDafny False StmtK re
    return $ vcat pres $+$ ple <+> text ":=" <+> pre $+$ vcat post
statementToDafny (ExpressionStatement l e) = do
    (anne,pe) <- expressionToDafny False StmtK e
    return $ vcat anne $+$ pe <> semicolon
statementToDafny (AssertStatement l e) = do
    (anne,pe) <- expressionToDafny False StmtK e
    assert <- annExpr False False StmtK pe
    return $ vcat anne $+$ assert
statementToDafny (AnnStatement l ss) = liftM vcat $ mapM statementAnnToDafny ss
statementToDafny (VarStatement l (VariableDeclaration _ t vs)) = do
    t' <- typeToDafny (typed $ loc t)
    liftM vcat $ mapM (varInitToDafny t') $ Foldable.toList vs
statementToDafny (ConstStatement l (ConstDeclaration _ t vs)) = do
    t' <- typeToDafny (typed $ loc t)
    liftM vcat $ mapM (constInitToDafny t') $ Foldable.toList vs
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

--    | ForStatement loc (ForInitializer iden loc) (Maybe (Expression iden loc)) (Maybe (Expression iden loc)) [LoopAnnotation iden loc] (Statement iden loc)
--    | WhileStatement loc (Expression iden loc) [LoopAnnotation iden loc] (Statement iden loc)
--    | PrintStatement loc [(Expression iden loc,IsVariadic)]
--    | DowhileStatement loc [LoopAnnotation iden loc] (Statement iden loc) (Expression iden loc)
--    | SyscallStatement loc String [SyscallParameter iden loc]

-- TODO: ignore sizes?
varInitToDafny :: DafnyK m => Doc -> VariableInitialization VarIdentifier (Typed Position) -> DafnyM m Doc
varInitToDafny pty (VariableInitialization l v sz ini) = do
    pv <- varToDafny v
    let def = text "var" <+> pv <> char ':' <> pty <> semicolon
    anns <- genDafnyPublics StmtK pv (typed $ loc v)
    (annsini,pini) <- mapExpressionToDafny False StmtK ini
    let assign = ppOpt pini (\e -> pv <+> text ":=" <+> e <+> semicolon)
    return $ def $+$ vcat annsini $+$ assign $+$ vcat anns

-- TODO: ignore sizes?
constInitToDafny :: DafnyK m => Doc -> ConstInitialization VarIdentifier (Typed Position) -> DafnyM m Doc
constInitToDafny pty (ConstInitialization l v sz ini) = do
    pv <- varToDafny v
    let def = text "var" <+> pv <> char ':' <> pty <> semicolon
    anns <- genDafnyPublics StmtK pv (typed $ loc v)
    (annsini,pini) <- mapExpressionToDafny False StmtK ini
    let assign = ppOpt pini (\e -> pv <+> text ":=" <+> e <+> semicolon)
    return $ def $+$ vcat annsini $+$ assign $+$ vcat anns
    
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
baseTypeToDafny (TApp (TypeName _ n) args _) = do
    pn <- dafnyVarIdM n
    let ppArg (t,False) = typeToDafny t
        ppArg (t,True) = genError noloc $ text "baseTypeToDafny: variadic argument" <+> pp t
    args' <- mapM ppArg args
    let pargs = if null args' then empty else abrackets $ sepBy comma args'
    return $ pn <> pargs
--baseTypeToDafny t = genError noloc $ text "baseTypeToDafny:" <+> pp t

complexTypeToDafny :: DafnyK m => ComplexType -> DafnyM m Doc
complexTypeToDafny t@(CType s b d) = do
    let p = noloc::Position
    pb <- baseTypeToDafny b
    mb <- lift $ tryError $ evaluateIndexExpr p d
    case mb of
        Right 0 -> return pb
        Right 1 -> return $ text "seq" <> abrackets pb
        otherwise -> genError p $ text "complexTypeToDafny:" <+> pp t
complexTypeToDafny t = genError noloc $ text "complexTypeToDafny:" <+> pp t

data AnnKind = StmtK | EnsureK | RequireK | InvariantK | DecreaseK
  deriving Show
instance PP AnnKind where
    pp = text . show

indexToDafny :: DafnyK m => Bool -> AnnKind -> Index VarIdentifier (Typed Position) -> DafnyM m ([Doc],Doc)
indexToDafny isLVal annK (IndexInt l e) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    return (anne,brackets pe)
indexToDafny isLVal annK (IndexSlice l e1 e2) = do
    (anne1,pe1) <- mapExpressionToDafny isLVal annK e1
    (anne2,pe2) <- mapExpressionToDafny isLVal annK e2
    return (anne1++anne2,brackets (pp pe1 <> text ".." <> pp pe2))

expressionToDafny :: DafnyK m => Bool -> AnnKind -> Expression VarIdentifier (Typed Position) -> DafnyM m ([Doc],Doc)
expressionToDafny isLVal annK (PostIndexExpr l e (Foldable.toList -> [i])) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    (anni,pi) <- indexToDafny isLVal annK i
    return (anne++anni,pe <> pi)
expressionToDafny isLVal annK se@(SelectionExpr l e att) = do
    (anne,pe) <- expressionToDafny isLVal annK e
    patt <- structAttToDafny $ fmap typed att
    let pse = pe <> char '.' <> patt
    anns <- genDafnyPublics annK pse (typed l)
    return (anne++anns,pse)
expressionToDafny isLVal annK (RVariablePExpr l v) = do
    pv <- varToDafny v
    anns <- if isLVal then genDafnyPublics annK pv (typed $ loc v) else return []
    return (anns,pv)
expressionToDafny isLVal annK (LitPExpr l lit) = literalToDafny lit
expressionToDafny isLVal annK (LeakExpr l e) = do
    (anne,pe) <- expressionToDafny False annK e
    return (anne,text "Leak" <> parens pe)
expressionToDafny isLVal annK (QualExpr _ e _) = expressionToDafny isLVal annK e -- TODO: revise type annotations
expressionToDafny isLVal annK (MultisetConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    return (annes,text "multiset" <> braces (sepBy comma pes))
expressionToDafny isLVal annK (ArrayConstructorPExpr l es) = do
    (annes,pes) <- expressionsToDafny False annK es
    return (annes,brackets (sepBy comma pes))
expressionToDafny isLVal annK (ToMultisetExpr l e) = do
    (anne,pe) <- expressionToDafny False annK e
    return (anne,text "multiset" <> parens pe)
expressionToDafny isLVal annK (BuiltinExpr l n es) = builtinToDafny annK l n es
expressionToDafny isLVal annK e@(ProcCallExpr l (ProcedureName (Typed _ dec) n) targs args) = genError noloc $ text "expressionToDafny: unsupported procedure call" <+> pp e <+> pp dec
expressionToDafny isLVal annK e@(BinaryExpr l e1 op e2) = genError noloc $ text "expressionToDafny: unsupported binary procedure call" <+> pp e <+> pp (typed $ loc op)
expressionToDafny isLVal annK e = genError noloc $ text "expressionToDafny:" <+> pp isLVal <+> pp annK <+> pp e

expressionsToDafny :: (Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression VarIdentifier (Typed Position)) -> DafnyM m ([Doc],[Doc])
expressionsToDafny isLVal annK es = do
    (annes,es') <- Utils.mapAndUnzipM (expressionToDafny isLVal annK) $ Foldable.toList es
    return (concat annes,es')

mapExpressionToDafny :: (Functor f,Traversable f,Foldable f,DafnyK m) => Bool -> AnnKind -> f (Expression VarIdentifier (Typed Position)) -> DafnyM m ([Doc],f Doc)
mapExpressionToDafny isLVal annK es = do
    rs <- mapM (expressionToDafny isLVal annK) es
    return (concat $ Foldable.toList $ fmap fst rs,fmap snd rs)

builtinToDafny :: DafnyK m => AnnKind -> Typed Position -> String -> [Expression VarIdentifier (Typed Position)] -> DafnyM m ([Doc],Doc)
builtinToDafny annK (Typed l ret) "core.eq" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "==" <> py)
builtinToDafny annK (Typed l ret) "core.band" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "&&" <> py)
builtinToDafny annK (Typed l ret) "core.bor" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "||" <> py)
builtinToDafny annK (Typed l ret) "core.lt" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "<" <> py)
builtinToDafny annK (Typed l ret) "core.le" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "<=" <> py)
builtinToDafny annK (Typed l ret) "core.gt" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text ">" <> py)
builtinToDafny annK (Typed l ret) "core.ge" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text ">=" <> py)
builtinToDafny annK (Typed l ret) "core.implies" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "==>" <> py)
builtinToDafny annK (Typed l ret) "core.subset" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "<=" <> py)
builtinToDafny annK (Typed l ret) "core.union" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "+" <> py)
builtinToDafny annK (Typed l ret) "core.add" [x,y] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    return (annx++anny,px <> text "+" <> py)
builtinToDafny annK (Typed l ret) "core.declassify" [x] = do -- we ignore security types
    expressionToDafny False annK x
builtinToDafny annK (Typed l ret) "core.classify" [x] = do -- we ignore security types
    expressionToDafny False annK x
builtinToDafny annK (Typed l ret) "core.cat" [x,y,n] = do
    (annx,px) <- expressionToDafny False annK x
    (anny,py) <- expressionToDafny False annK y
    let tx = typed $ loc x
    case tx of
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryError $ evaluateIndexExpr l d
            mbn <- lift $ tryError $ evaluateIndexExpr l $ fmap typed n
            case (mbd,mbn) of
                (Right 1,Right 0) -> return (annx++anny,px <+> char '+' <+> py)
                otherwise -> genError noloc $ text "builtinToDafny: unsupported cat" <+> pp x <+> pp y <+> pp n
        otherwise -> genError noloc $ text "builtinToDafny: unsupported cat" <+> pp x <+> pp y <+> pp n
    return (annx++anny,px)
builtinToDafny annK (Typed l ret) "core.size" [x] = do
    (annx,px) <- expressionToDafny False annK x
    let tx = typed $ loc x
    case tx of
        BaseT b -> return (annx,text "1")
        ComplexT (CType s b d) -> do
            mbd <- lift $ tryError $ evaluateIndexExpr l d
            case mbd of
                Right 0 -> return (annx,text "1")
                Right 1 -> return (annx,char '|' <> px <> char '|')
                otherwise -> genError noloc $ text "builtinToDafny: unknown size" <+> pp x <+> pp tx
        otherwise -> genError noloc $ text "builtinToDafny: unknown size" <+> pp x <+> pp tx
builtinToDafny annK ret n es = genError noloc $ text "builtinToDafny:" <+> pp annK <+> pp ret <+> pp n <+> pp es

--    = BinaryAssign loc (Expression iden loc) (BinaryAssignOp loc) (Expression iden loc)
--    | CondExpr loc (Expression iden loc) (Expression iden loc) (Expression iden loc)
--    | BinaryExpr loc (Expression iden loc) (Op iden loc) (Expression iden loc)
--    | UnaryExpr loc (Op iden loc) (Expression iden loc)
--    | PreOp loc (Op iden loc) (Expression iden loc)
--    | PostOp loc (Op iden loc) (Expression iden loc)
--    | VArraySizeExpr loc (Expression iden loc)
--    | VArrayExpr loc (Expression iden loc) (Expression iden loc)
--    | ProcCallExpr loc (ProcedureName iden loc) (Maybe [(TemplateTypeArgument iden loc,IsVariadic)]) [(Expression iden loc,IsVariadic)]
--    | PostIndexExpr loc (Expression iden loc) (Subscript iden loc)
--    | SelectionExpr loc (Expression iden loc) (AttributeName iden loc)
--    | QuantifiedExpr loc (Quantifier loc) [(TypeSpecifier iden loc,VarName iden loc)] (Expression iden loc)

literalToDafny :: DafnyK m => Literal (Typed Position) -> DafnyM m ([Doc],Doc)
literalToDafny lit = return ([],pp lit)

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
            Just m -> if (current==m)
                then empty
                else text m <> char '.'
    pid = ppOpt (varIdUniq v) (\x -> char '_' <> pp x)

dafnyVarIdM :: DafnyK m => VarIdentifier -> DafnyM m Doc
dafnyVarIdM v = do
    current <- getModule
    return $ dafnyVarId current v

instance PP DafnyId where
    pp did = ppDafnyId (dafnyIdModule did) did

ppDafnyId :: Identifier -> DafnyId -> Doc
ppDafnyId current (PId pn (mn,uid) isLeak) = prefix <> ppn <> pp uid <> suffix
    where
    ppn = dafnyVarId current pn
    prefix = if current==mn then empty else text mn <> char '.' 
    suffix = if isLeak then text "Leakage" else empty
ppDafnyId current (OId on (mn,uid) isLeak) = error $ show $ text "ppDafnyId: operator not supported" <+> pp on
ppDafnyId current (SId sn (mn,uid) isLeak) = prefix <> psn <> pp uid <> suffix
    where
    psn = dafnyVarId current sn
    prefix = if current==mn then empty else text mn <> char '.' 
    suffix = if isLeak then text "Leakage" else empty
ppDafnyId current (AId (mn,uid) isLeak) = prefix <> psn <> pp uid <> suffix
    where
    psn = dafnyVarId current $ mkVarId "axiom"
    prefix = if current==mn then empty else text mn <> char '.' 
    suffix = if isLeak then text "Leakage" else empty

ppDafnyIdM :: DafnyK m => DafnyId -> DafnyM m Doc
ppDafnyIdM did = do
    current <- getModule
    return $ ppDafnyId current did


