{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Environment where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Conversion

import Data.IORef
import Data.Either
import Data.Int
import Data.Word
import Data.Unique
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Generics hiding (GT,typeRep)
import Data.Dynamic hiding (typeRep)
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..),(!))
import qualified Data.Map as Map
import Data.Bifunctor

import Data.Graph.Inductive              as Graph hiding (mapSnd)
import Data.Graph.Inductive.Graph        as Graph
import Data.Graph.Inductive.PatriciaTree as Graph
import Data.Graph.Inductive.Query.DFS    as Graph

import Control.Applicative
import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding ((<>))
import Control.Monad.Trans.RWS (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Except

import System.IO.Unsafe
import Unsafe.Coerce

import Safe

import Text.PrettyPrint as PP hiding (float,int,equals)
import qualified Text.PrettyPrint as Pretty hiding (equals)

import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap

import System.Mem.Weak.Exts as Weak

withFrees :: Monad m => TcM m a -> TcM m a
withFrees m = do
    old <- State.gets localFrees
    State.modify $ \env -> env { localFrees = Set.empty }
    x <- m
    State.modify $ \env -> env { localFrees = old }
    return x

getDoSolve :: Monad m => TcM m Bool
getDoSolve = State.gets (\e -> length (tDict e) <= 1)

getDoAll :: Monad m => TcM m Bool
getDoAll = do
    env <- State.get
    return $ not (inTemplate env)

withInTemplate :: (ProverK Position m) => Bool -> TcM m a -> TcM m a
withInTemplate b m = do
    old <- liftM inTemplate State.get
    State.modify $ \env -> env { inTemplate = b }
    x <- m
    State.modify $ \env -> env { inTemplate = old }
    return x

getAllVars scope = getVarsPred scope (const True)
getVars scope cl = getVarsPred scope (== cl)

-- | Gets the variables of a given type class
getVarsPred :: (MonadIO m) => Scope -> (TypeClass -> Bool) -> TcM m (Map VarIdentifier (Bool,(Bool,EntryEnv)))
getVarsPred GlobalScope f = do
    (x,y) <- liftM moduleEnv State.get
    let vs = Map.map ((True,) . snd) $ globalVars x `Map.union` globalVars y
    return $ Map.filter (\(_,(_,e)) -> f $ typeClass "getVarsG" (entryType e)) vs
getVarsPred LocalScope f = do
    vs <- liftM envVariables State.get
    return $ Map.filterWithKey (\k (_,(_,e)) -> f $ typeClass ("getVarsL " ++ ppr k ++ ppr (locpos $ entryLoc e)) (entryType e)) vs

addVar :: (ProverK loc m) => loc -> Scope -> VarIdentifier -> Maybe Expr -> Bool -> EntryEnv -> TcM m ()
addVar l GlobalScope n v isConst e = do
    dict <- liftM (head . tDict) State.get
    e' <- substFromTDict "addVar" l dict False Map.empty e
    case v of
        Nothing -> modifyModuleEnv $ \env -> env { globalVars = Map.insert n (Nothing,(isConst,e')) (globalVars env) }
        Just val -> do
            unifies l (loc val) (entryType e')
            val' <- substFromTDict "addVar" l dict False Map.empty val
            modifyModuleEnv $ \env -> env { globalVars = Map.insert n (Just val',(isConst,e')) (globalVars env) }
addVar l LocalScope n v isConst e = do
    modify $ \env -> env { localVars = Map.insert n (isConst,e) (localVars env) }
    case v of
        Nothing -> return ()
        Just val -> assignsExprTy l (VarName (entryType e) n) val

getFrees :: (ProverK loc m) => loc -> TcM m (Set VarIdentifier)
getFrees l = do
    frees <- liftM localFrees State.get
    TSubsts ss <- getTSubsts l
    return $ Set.difference frees $ Map.keysSet ss

-- replaces a constraint in the constraint graph by a constraint graph
replaceCstrWithGraph :: (MonadIO m,Location loc) => loc -> Bool -> Int -> Set LocIOCstr -> IOCstrGraph -> Set LocIOCstr -> TcM m ()
replaceCstrWithGraph l filterDeps kid ins gr outs = do
    let cs = flattenIOCstrGraph gr
    --liftIO $ putStrLn $ "replaceCstrWithGraph " ++ ppr kid
    --    ++ " from " ++ show (sepBy space $ map (pp . ioCstrId . unLoc) $ Set.toList ins)
    --    ++ " to " ++ show (sepBy space $ map (pp . ioCstrId . unLoc) $ Set.toList outs)
    --    ++ " for " ++ show (sepBy space $ map (pp . ioCstrId . unLoc) cs)
    updateHeadTDict $ \d -> return ((),d { tCstrs = unionGr gr $ delNode kid (tCstrs d) })
    forM_ cs $ \c -> addIOCstrDependenciesM filterDeps (Set.filter (\x -> ioCstrId (unLoc x) /= kid) ins) c (Set.filter (\x -> ioCstrId (unLoc x) /= kid) outs)
--    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--    liftIO $ putStrLn $ "replaceCstrWithGraph2 [" ++ show ss ++ "\n]"

withDeps :: MonadIO m => Scope -> TcM m a -> TcM m a
withDeps LocalScope m = do
    env <- State.get
    let l = localDeps env
    x <- m
    State.modify $ \env -> env { localDeps = l }
    return x
withDeps GlobalScope m = do
    env <- State.get
    let l = localDeps env
    let g = globalDeps env
    x <- m
    State.modify $ \env -> env { localDeps = l, globalDeps = g }
    return x

getConsts :: Monad m => TcM m (Map Identifier VarIdentifier)
getConsts = do
    env <- State.get
    let (x,y) = moduleEnv env
    return $ Map.unions[localConsts env,globalConsts x,globalConsts y]

checkConst :: MonadIO m => VarIdentifier -> TcM m VarIdentifier
checkConst n = do
    consts <- getConsts
    let n' = case (varIdUniq n) of
                Nothing -> maybe n id (Map.lookup (varIdBase n) consts)
                otherwise -> n
    return n'

registerVar :: Monad m => Bool -> VarIdentifier -> TcM m ()
registerVar isWrite v = if isWrite
    then addProcClass (Proc False Set.empty (Set.singleton v))
    else addProcClass (Proc False (Set.singleton v) Set.empty)

checkVariable :: (ProverK loc m) => Bool -> Bool -> Scope -> VarName VarIdentifier loc -> TcM m (VarName VarIdentifier (Typed loc))
checkVariable isWrite cConst scope v@(VarName l n) = do
    vs <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    n <- checkConst n
    case Map.lookup n vs of
        Just (isGlobal,(isConst,e)) -> do
            when isGlobal $ registerVar isWrite n
            when cConst $ unless isConst $ genTcError (locpos l) $ text "expected variable" <+> pp v <+> text "to be a constant"
            when (isWrite && isConst) $ tcError (locpos l) $ AssignConstVariable (pp n)
            --liftIO $ putStrLn $ "checkVariable " ++ ppr v ++ " " ++ ppr n
            return $ VarName (Typed l $ entryType e) n
        Nothing -> tcError (locpos l) $ VariableNotFound (pp n)

-- | Adds a new variable to the environment
newVariable :: (ProverK loc m) => Scope -> Bool -> VarName VarIdentifier (Typed loc) -> Maybe (Expression VarIdentifier (Typed loc)) -> TcM m ()
newVariable scope isConst v@(VarName (Typed l t) n) val = do
    removeFree n
    vars <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    case Map.lookup n vars of
        Just (_,(_,e)) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
        Nothing -> return ()
    addVar l scope n (fmap (fmap typed) val) isConst (EntryEnv (locpos l) t)

addDeps :: (MonadIO m) => Scope -> Set LocIOCstr -> TcM m ()
addDeps scope xs = forM_ xs $ \x -> addDep scope x

addDep :: (MonadIO m) => Scope -> Loc Position IOCstr -> TcM m ()
addDep GlobalScope hyp = modify $ \env -> env { globalDeps = Set.insert hyp (globalDeps env) }
addDep LocalScope hyp = modify $ \env -> env { localDeps = Set.insert hyp (localDeps env) }

tcNoDeps :: (VarsIdTcM m) => TcM m a -> TcM m a
tcNoDeps m = do
    env <- State.get
    let g = globalDeps env
    let l = localDeps env
    State.modify $ \env -> env { globalDeps = Set.empty, localDeps = Set.empty }
    x <- m
    State.modify $ \env -> env { globalDeps = g, localDeps = l }
    return x

tcAddDeps :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a
tcAddDeps l msg m = do
    (x,ks) <- tcWithCstrs l msg m
    forM_ ks $ addDep LocalScope
    return x
    
tryAddHypothesis :: (ProverK loc m) => loc -> Scope -> Set LocIOCstr -> HypCstr -> TcM m ()
tryAddHypothesis l scope deps hyp = do
    opts <- askOpts
    when (checkAssertions opts) $ do
        isAnn <- getAnn
        isPure <- getPure
        iok <- updateHeadTDict $ \d -> newTDictCstr (locpos l) (HypK hyp isAnn isPure) d
        addDep scope $ Loc (locpos l) iok
        addIOCstrDependenciesM True deps (Loc (locpos l) iok) Set.empty

-- | Adds a new domain variable to the environment
newDomainVariable :: (ProverK loc m) => Scope -> DomainName VarIdentifier (Typed loc) -> TcM m ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    removeFree n
    ds <- getDomains
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (pp n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == KindC || k == VArrayC KindC)
            case Map.lookup n vars of
                Just (_,(_,e)) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
                Nothing -> addVar l scope n Nothing False (EntryEnv (locpos l) t)

-- | Adds a new type variable to the environment
newTypeVariable :: (ProverK loc m) => Scope -> TypeName VarIdentifier (Typed loc) -> TcM m ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    removeFree n
    ss <- getStructs
    case Map.lookup n ss of
        Just (es) -> tcError (locpos l) $ InvalidTypeVariableName (pp n) (map (locpos . entryLoc) (Map.elems es))
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
            case Map.lookup n vars of
                Just (_,(_,e)) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
                Nothing -> addVar l scope n Nothing False (EntryEnv (locpos l) t)

-- | Adds a new domain to the environment
newDomain :: (MonadIO m,Location loc) => DomainName VarIdentifier (Typed loc) -> TcM m ()
newDomain (DomainName (Typed l t) n) = do
    ds <- getDomains
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ MultipleDefinedDomain (pp n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv (locpos l) t
            modifyModuleEnv $ \env -> env { domains = Map.insert n e (domains env) }

isDomain k = k == KindC || k == VArrayC KindC

-- | Checks if a domain exists in scope, and returns its type
-- Searches for both user-defined private domains and domain variables
checkDomain :: (MonadIO m,Location loc) => DomainName VarIdentifier loc -> TcM m (DomainName VarIdentifier (Typed loc))
checkDomain (DomainName l n) = do
    ds <- getDomains
    (n,t) <- case Map.lookup n ds of
        Just e -> case entryType e of
            SType (PrivateKind (Just k)) -> return (n,SecT $ Private (DomainName () n) k)
            otherwise -> genTcError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        Nothing -> do
            dvars <- getVarsPred LocalScope isDomain
            n <- checkConst n
            case Map.lookup n dvars of
                Just (_,(_,e)) -> return (n,varNameToType $ VarName (entryType e) n)
                Nothing -> tcError (locpos l) $ NotDefinedDomain (pp n)
    return $ DomainName (Typed l t) n

checkStruct :: ProverK loc m => loc -> SIdentifier -> ModuleTyVarId -> TcM m DecType
checkStruct l sid@(TypeName _ sn) mid = do
    ss <- getStructs
    case Map.lookup sn ss of
        Just es -> case Map.lookup mid es of
            Just e -> typeToDecType l (entryType e)
            Nothing -> tcError (locpos l) $ NotDefinedType (pp sn <+> pp mid)
        Nothing -> tcError (locpos l) $ NotDefinedType (pp sn <+> pp mid)
        
-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: (ProverK loc m) => TypeName VarIdentifier loc -> TcM m [EntryEnv]
checkType (TypeName l n) = do
    ss <- getStructs
    case Map.lookup n ss of
        Just (es) -> return (Map.elems es)
        Nothing -> tcError (locpos l) $ NotDefinedType (pp n)

checkTypeVariable :: (ProverK loc m) => TypeName VarIdentifier loc -> TcM m (Maybe (TypeName VarIdentifier (Typed loc)))
checkTypeVariable (TypeName l n) = do
    vars <- getVarsPred LocalScope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
    n <- checkConst n
    case Map.lookup n vars of
        Just (_,(_,e)) -> do
            let t = varNameToType (VarName (entryType e) n)
            return $ Just $ TypeName (Typed l t) n
        Nothing -> return Nothing

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkTypeName :: (ProverK loc m) => TypeName VarIdentifier loc -> TcM m (TypeName VarIdentifier (Typed loc))
checkTypeName tn@(TypeName l n) = do
    mb <- checkTypeVariable tn
    case mb of
        Just tn' -> return tn'
        Nothing -> do
            dec <- newDecVar Nothing
            topTcCstrM_ l $ TDec False (TypeName () n) [] dec
            let ret = BaseT $ TApp (TypeName () n) [] dec
            return $ TypeName (Typed l ret) n

checkNonTemplateType :: (ProverK loc m) => TypeName VarIdentifier loc -> TcM m [EntryEnv]
checkNonTemplateType ty@(TypeName l n) = do
    es <- checkType ty
    case es of
        [e] -> case entryType e of
            DecT d -> case d of
                (DecType _ _ [] _ _ _ _ _ (StructType {})) -> return [e]
                otherwise -> tcError (locpos l) $ NoNonTemplateType (pp n)
            t -> tcError (locpos l) $ NoNonTemplateType (pp n)
        es -> tcError (locpos l) $ NoNonTemplateType (pp n)

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: (ProverK loc m) => TypeName VarIdentifier loc -> TcM m [EntryEnv]
checkTemplateType ty@(TypeName _ n) = do
    es <- checkType ty
    let check e = unless (isStructTemplate $ entryType e) $ tcError (locpos $ loc ty) $ NoTemplateType (pp n) (locpos $ entryLoc e) (pp $ entryType e)
    mapM_ check es
    return (es)

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: (ProverK loc m) => TemplateArgName VarIdentifier loc -> TcM m (TemplateArgName VarIdentifier (Typed loc))
checkTemplateArg (TemplateArgName l n) = do
    env <- getModuleEnv
    let ss = structs env
    let ds = domains env
    vs <- liftM envVariables State.get
    vn <- checkConst n
    case (Map.lookup n ss,Map.lookup n ds,Map.lookup vn vs) of
        (Just (es),Nothing,Nothing) -> case ( Map.elems es) of
            [e] -> if (isStructTemplate $ entryType e)
                then tcError (locpos l) $ NoNonTemplateType (pp n)
                else return $ TemplateArgName (Typed l $ entryType e) n
            es -> tcError (locpos l) $ NoNonTemplateType (pp n)
        (Nothing,Just e,Nothing) -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ TemplateArgName (Typed l $ SecT $ Private (DomainName () n) k) n
            otherwise -> genTcError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        (Nothing,Nothing,Just (isGlobal,(b,e))) -> do
            when isGlobal $ registerVar False vn
            return $ TemplateArgName (Typed l $ varNameToType $ VarName (entryType e) vn) vn
        (mb1,mb2,mb3) -> tcError (locpos l) $ AmbiguousName (pp n) $ map (locpos . entryLoc) $ maybe [] (\(es) -> Map.elems es) (mb1) ++ maybeToList (mb2) ++ maybeToList (fmap (snd . snd) mb3)

-- | Checks that a kind exists in scope
checkKind :: (MonadIO m,Location loc) => KindName VarIdentifier loc -> TcM m ()
checkKind (KindName l n) = do
    ks <- getKinds
    case Map.lookup n ks of
        Just e -> return ()
        Nothing -> tcError (locpos l) $ NotDefinedKind (pp n)

-- | Adds a new kind to the environment
newKind :: (MonadIO m,Location loc) => KindName VarIdentifier (Typed loc) -> TcM m ()
newKind (KindName (Typed l t) n) = do
    ks <- getKinds
    case Map.lookup n ks of
        Just e -> tcError (locpos l) $ MultipleDefinedKind (pp n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv (locpos l) t
            modifyModuleEnv $ \env -> env { kinds = Map.insert n e (kinds env) } 

noTSubsts d = d { pureSubsts = emptyTSubsts }

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: (ProverK loc m) => [(Constrained Var,IsVariadic)] -> Deps -> Op VarIdentifier (Typed loc) -> TcM m (Op VarIdentifier (Typed loc))
addTemplateOperator vars hdeps op = do
    let Typed l (IDecT d) = loc op
    let o = funit op
    solve l "addTemplateOperator"
    (hdict,hfrees,bdict,bfrees) <- splitHead l hdeps d
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    (hbsubsts,[]) <- appendTSubsts l NoCheckS (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateOp" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
    liftIO $ putStrLn $ "addTemplateOp " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) dt')

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (ProverK loc m) => Deps -> Op VarIdentifier (Typed loc) -> TcM m (Op VarIdentifier (Typed loc))
newOperator hdeps op = do
    let (Typed l (IDecT d)) = loc op
    let o = funit op
    (_,recdict) <- tcProve l "newOp head" $ addHeadTFlatCstrs l hdeps
    addHeadTDict l recdict
    i <- newModuleTyVarId
    frees <- getFrees l
    d'@(ProcType pl on pargs pret panns body cl) <- substFromTDict "newOp head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] emptyPureTDict frees emptyPureTDict Set.empty [] $ ProcType pl on pargs pret panns [] cl
    rece <- localTemplate l $ EntryEnv (locpos l) recdt
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert i rece . maybe Map.empty id) o (operators env) }
    dirtyGDependencies $ Right $ Left $ Right o
    
    solveTop l "newOperator"
    dict <- liftM (head . tDict) State.get
    d'' <- substFromTDict "newOp body" l dict False Map.empty d'
    let td = DecT $ DecType i False [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] d''
    let e = EntryEnv (locpos l) td
    noFrees e
    liftIO $ putStrLn $ "addOp " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) td)
  
 -- | Checks that an operator exists.
checkOperator :: (VarsIdTcM m,Location loc) => Bool -> Op VarIdentifier loc -> TcM m [EntryEnv]
checkOperator isAnn op@(OpCast l t) = do
    addGDependencies $ Right $ Left $ Right $ funit op
    ps <- getOperators
    let cop = funit op
    -- select all cast declarations
    let casts = concatMap Map.elems $ Map.elems $ Map.filterWithKey (\k v -> isJust $ isOpCast k) ps
    return $ filter (\e -> isAnnProcClass (tyProcClass $ entryType e) <= isAnn) casts
checkOperator isAnn op = do
    addGDependencies $ Right $ Left $ Right $ funit op
    ps <- getOperators
    let cop = funit op
    case Map.lookup cop ps of
        Nothing -> tcError (locpos $ loc op) $ Halt $ NotDefinedOperator $ pp cop
        Just es -> return $ filter (\e -> isAnnProcClass (tyProcClass $ entryType e) <= isAnn) $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: (ProverK loc m) => [(Constrained Var,IsVariadic)] -> Deps -> ProcedureName VarIdentifier (Typed loc) -> TcM m (ProcedureName VarIdentifier (Typed loc))
addTemplateProcedure vars hdeps pn@(ProcedureName (Typed l (IDecT d)) n) = do
--    liftIO $ putStrLn $ "entering addTemplateProc " ++ ppr pn
    solve l "addTemplateProcedure"
    (hdict,hfrees,bdict,bfrees) <- splitHead l hdeps d
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    (hbsubsts,[]) <- appendTSubsts l NoCheckS (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateProc" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
    liftIO $ putStrLn $ "addTemplateProc " ++ ppr (entryType e) ++ ppr hbsubsts
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ ProcedureName (Typed l dt') n

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (ProverK loc m) => Deps -> ProcedureName VarIdentifier (Typed loc) -> TcM m (ProcedureName VarIdentifier (Typed loc))
newProcedure hdeps pn@(ProcedureName (Typed l (IDecT d)) n) = do
    -- prove the head constraints first
    (_,recdict) <- tcProve l "newProc head" $ addHeadTFlatCstrs l hdeps
    addHeadTDict l recdict
    i <- newModuleTyVarId
    frees <- getFrees l
    d'@(ProcType pl ppn pargs pret panns body cl) <- substFromTDict "newProc head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] $ ProcType pl ppn pargs pret panns [] cl
    rece <- localTemplate l $ EntryEnv (locpos l) recdt
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert i rece . maybe Map.empty id) n (procedures env) }
    dirtyGDependencies $ Right $ Left $ Left n
    doc <- liftM (tCstrs . head . tDict) State.get >>= ppConstraints
    liftIO $ putStrLn $ "newProc: " ++ show doc
    solveTop l "newProcedure"
    dict <- liftM (head . tDict) State.get
    d'' <- substFromTDict "newProc body" l dict False Map.empty d'
    let dt = DecType i False [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] d''
    let e = EntryEnv (locpos l) (DecT dt)
    noFrees e
    --liftIO $ putStrLn $ "addProc " ++ ppr (decTypeTyVarId dt) ++ " " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ ProcedureName (Typed l $ DecT dt) n
  
 -- | Checks that a procedure exists.
checkProcedure :: (MonadIO m,Location loc) => Bool -> ProcedureName VarIdentifier loc -> TcM m [EntryEnv]
checkProcedure isAnn pn@(ProcedureName l n) = do
    addGDependencies $ Right $ Left $ Left n
    ps <- getProcedures
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ Halt $ NotDefinedProcedure (pp n)
        Just es -> return $ filter (\e -> isAnnProcClass (tyProcClass $ entryType e) <= isAnn) $ Map.elems es

addProcClass :: Monad m => ProcClass -> TcM m ()
addProcClass cl = State.modify $ \env -> env { procClass = mappend cl $ procClass env }

withoutEntry :: Monad m => EntryEnv -> TcM m a -> TcM m a
withoutEntry e m = do
    let DecT d = entryType e
    env <- State.get
    let (x,y) = moduleEnv env
    let z = recEnv env
    case decTypeId d of
        Just (Right tn,i) -> case Map.lookup tn (structs x) of
            Just es -> case Map.lookup i es of
                Just e -> do
                    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x { structs = Map.update (Just . Map.delete i) tn $ structs x },y) } 
                    a <- m
                    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x { structs = Map.update (Just . Map.insert i e) tn $ structs x },y) } 
                    return a
                Nothing -> m
            Nothing -> case Map.lookup tn (structs y) of
                Just es -> case Map.lookup i es of
                    Just e -> do
                        State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y { structs = Map.update (Just . Map.delete i) tn $ structs y }) } 
                        a <- m
                        State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y { structs = Map.update (Just . Map.insert i e) tn $ structs y }) } 
                        return a
                    Nothing -> m
                Nothing -> case Map.lookup tn (structs z) of
                    Just es -> case Map.lookup i es of
                        Just e -> do
                            State.modify $ \env -> env { recEnv = let z = recEnv env in z { structs = Map.update (Just . Map.delete i) tn $ structs z } } 
                            a <- m
                            State.modify $ \env -> env { recEnv = let z = recEnv env in z { structs = Map.update (Just . Map.insert i e) tn $ structs z } } 
                            return a
                        Nothing -> m
                    Nothing -> m
        Just (Left (Left pn),i) -> case Map.lookup pn (procedures x) of
            Just es -> case Map.lookup i es of
                Just e -> do
                    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x { procedures = Map.update (Just . Map.delete i) pn $ procedures x },y) } 
                    a <- m
                    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x { procedures = Map.update (Just . Map.insert i e) pn $ procedures x },y) } 
                    return a
                Nothing -> m
            Nothing -> case Map.lookup pn (procedures y) of
                Just es -> case Map.lookup i es of
                    Just e -> do
                        State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y { procedures = Map.update (Just . Map.delete i) pn $ procedures y }) } 
                        a <- m
                        State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y { procedures = Map.update (Just . Map.insert i e) pn $ procedures y }) } 
                        return a
                    Nothing -> m
                Nothing -> case Map.lookup pn (procedures z) of
                    Just es -> case Map.lookup i es of
                        Just e -> do
                            State.modify $ \env -> env { recEnv = let z = recEnv env in z { procedures = Map.update (Just . Map.delete i) pn $ procedures z } } 
                            a <- m
                            State.modify $ \env -> env { recEnv = let z = recEnv env in z { procedures = Map.update (Just . Map.insert i e) pn $ procedures z } } 
                            return a
                        Nothing -> m
                    Nothing -> m
        Just (Left (Right (funit -> on)),i) -> case Map.lookup on (operators x) of
            Just es -> case Map.lookup i es of
                Just e -> do
                    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x { operators = Map.update (Just . Map.delete i) on $ operators x },y) } 
                    a <- m
                    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x { operators = Map.update (Just . Map.insert i e) on $ operators x },y) } 
                    return a
                Nothing -> m
            Nothing -> case Map.lookup on (operators y) of
                Just es -> case Map.lookup i es of
                    Just e -> do
                        State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y { operators = Map.update (Just . Map.delete i) on $ operators y }) } 
                        a <- m
                        State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y { operators = Map.update (Just . Map.insert i e) on $ operators y }) } 
                        return a
                    Nothing -> m
                Nothing -> case Map.lookup on (operators z) of
                    Just es -> case Map.lookup i es of
                        Just e -> do
                            State.modify $ \env -> env { recEnv = let z = recEnv env in z { operators = Map.update (Just . Map.delete i) on $ operators z } } 
                            a <- m
                            State.modify $ \env -> env { recEnv = let z = recEnv env in z { operators = Map.update (Just . Map.insert i e) on $ operators z } } 
                            return a
                        Nothing -> m
                    Nothing -> m
        Nothing -> error $ "withoutEntry " ++ ppr e

decIsRec :: DecType -> Bool
decIsRec (DecType _ isfree _ _ hfs _ bfs _ _) = isfree

mkTpltDecRec :: (MonadIO m,Location loc) => loc -> DecType -> TcM m ModuleTcEnv
mkTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs p@(ProcType pl n@(Left pn) pargs pret panns body cl)) = do
    j <- newModuleTyVarId
    let recd = DecType j True ts hd hfrees emptyPureTDict Set.empty specs (ProcType pl (Left pn) pargs pret panns [] cl)
    let rece = EntryEnv (locpos l) (DecT recd)
    return $ mempty { procedures = Map.singleton pn $ Map.singleton j rece }
mkTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs p@(ProcType pl (Right op) pargs pret panns body cl)) = do
    j <- newModuleTyVarId
    let o = funit op
    let recd = DecType j True ts hd hfrees emptyPureTDict Set.empty specs (ProcType pl (Right op) pargs pret panns [] cl)
    let rece = EntryEnv (locpos l) (DecT recd)
    return $ mempty { operators = Map.singleton (funit op) $ Map.singleton j rece }
mkTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs s@(StructType sl sid@(TypeName _ sn) atts)) = do
    j <- newModuleTyVarId
    let recd = DecType j True ts hd hfrees emptyPureTDict Set.empty specs (StructType sl sid [])
    --es <- liftM ((!sn) . structs . snd . moduleEnv) State.get
    let rece = EntryEnv (locpos l) (DecT recd)
    return $ mempty { structs = Map.singleton sn $ Map.singleton j rece }

-- adds a recursive declaration for processing recursive constraints
--withTpltDecRec :: (ProverK Position m) => EntryEnv -> TcM m a -> TcM m a
--withTpltDecRec rece m = do
--    dec <- typeToDecType (entryLoc rece) (entryType rece)
--    case decTypeId dec of
--        Just (Left (Left pn),j) -> do
--            modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert j rece . maybe Map.empty id) pn (procedures env) }
--            x <- m
--            modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.delete j . maybe Map.empty id) pn (procedures env) }
--            return x
--        Just (Left (Right on),j) -> do
--            let o = funit on
--            modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert j rece . maybe Map.empty id) o (operators env) }
--            x <- m
--            modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.delete j . maybe Map.empty id) o (operators env) }
--            return x
--        Just (Right sn,j) -> do
--            modifyModuleEnv $ \env -> env { structs = Map.alter (Just . (\(es) -> (Map.insert j rece es)) . fromJust) sn (structs env) }
--            x <- m
--            modifyModuleEnv $ \env -> env { structs = Map.alter (Just . (\(es) -> (Map.delete j es)) . fromJust) sn (structs env) }
--            return x
--        Nothing -> error $ "withTpltDecRec: " ++ ppr rece
    
---- build an undirected graph between all variables related through substitutions or constraints
--dictVarGraph :: PureTDict -> Gr VarIdentifier ()
--dictVarGraph = undefined
--
---- selects all constraints that depend on a set of variables
--selectDependentCstrs :: Set VarIdentifier -> TcM m (Set LocIOCstr)
--selectDependentCstrs vs = do
--    dictVarGraph
    
buildCstrGraph :: (ProverK loc m) => loc -> Set LocIOCstr -> TcM m IOCstrGraph
buildCstrGraph l cstrs = do
    d <- concatTDict l NoCheckS =<< liftM tDict State.get
    let gr = tCstrs d
    let tgr = Graph.trc gr 
    let cs = mapSet unLoc cstrs
    let gr' = Graph.nfilter (\n -> any (\h -> Graph.hasEdge tgr (n,ioCstrId h)) cs) tgr
    let ns = nodes gr'
    let remHeadCstrs d = d { tCstrs = Graph.nfilter (\x -> not $ elem x ns) (Graph.trc $ tCstrs d) }
    State.modify $ \env -> env { tDict = map remHeadCstrs $ tDict env }
    return gr'
    
-- no free variable can be unbound
noFrees :: ProverK Position m => EntryEnv -> TcM m ()
noFrees e = do
    frees <- liftM localFrees State.get
    TSubsts ss <- getTSubsts (loc e)
    let vs = Set.difference frees $ Map.keysSet ss
    unless (Set.null vs) $ genTcError (loc e) $ text "variables" <+> pp vs <+> text "should not be free in" $+$ pp e
    
splitHead :: (ProverK loc m) => loc -> Set LocIOCstr -> InnerDecType -> TcM m (PureTDict,Set VarIdentifier,PureTDict,Set VarIdentifier)
splitHead l deps dec = do
    d <- liftM (head . tDict) State.get
    frees <- getFrees l
    freevars <- fvs $ toPureCstrs $ tCstrs d
    doc <- ppConstraints (tCstrs d)
    forM_ frees $ \v -> unless (Map.member v freevars) $ genTcError (locpos l) $ text "free variable" <+> pp v <+> text "not dependent on a constraint from" <+> pp d <+> text "in declaration" <+> pp dec
    hvs <- liftM Map.keysSet $ fvs $ Set.map (kCstr . unLoc) deps
    let hfrees = Set.intersection frees hvs
    let bfrees = Set.difference frees hfrees
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc deps) (Set.fromList $ map fst opens)
    let gr = Graph.trc $ tCstrs d
    let hgr = nmap (fmap kCstr) $ Graph.nfilter (\n -> any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    let bgr = differenceGr (nmap (fmap kCstr) gr) hgr
--    liftIO $ putStrLn $ "splitHead " ++ ppr hgr ++ "\n|\n" ++ ppr bgr
    return (PureTDict hgr (tSubsts d),hfrees,PureTDict bgr emptyTSubsts,bfrees)
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (ProverK loc m) => [(Constrained Var,IsVariadic)] -> Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc))
addTemplateStruct vars hdeps tn@(TypeName (Typed l (IDecT d)) n) = do
    solve l "addTemplateStruct"
    (hdict,hfrees,bdict,bfrees) <- splitHead l hdeps d
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    (hbsubsts,[]) <- appendTSubsts l NoCheckS (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateStruct" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
    ss <- getStructs
    case Map.lookup n ss of
        Just es -> tcError (locpos l) $ MultipleDefinedStructTemplate (pp n) (locpos $ entryLoc $ head $ Map.elems es)
        otherwise -> modifyModuleEnv $ \env -> env { structs = Map.insert n (Map.singleton i e) (structs env) }
    return $ TypeName (Typed l dt') n
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (ProverK loc m) => [(Constrained Var,IsVariadic)] -> [(Type,IsVariadic)] -> Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc))
addTemplateStructSpecialization vars specials hdeps tn@(TypeName (Typed l (IDecT d)) n) = do
    solve l "addTemplateStructSpecialization"
    (hdict,hfrees,bdict,bfrees) <- splitHead l hdeps d
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees specials d
    (hbsubsts,[]) <- appendTSubsts l NoCheckS (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateStructSpec" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
    modifyModuleEnv $ \env -> env { structs = Map.update (\s -> Just $ Map.insert i e s) n (structs env) }
    return $ TypeName (Typed l dt') n

-- | Defines a new struct type
newStruct :: (ProverK loc m) => Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc))
newStruct hdeps tn@(TypeName (Typed l (IDecT d)) n) = do
    addGDependencies $ Right $ Right n
    -- solve head constraints
    (_,recdict) <- tcProve l "newStruct head" $ addHeadTFlatCstrs l hdeps
    addHeadTDict l recdict
    i <- newModuleTyVarId
    -- add a temporary declaration for recursive invocations
    frees <- getFrees l
    d'@(StructType sl sid atts) <- substFromTDict "newStruct head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] $ StructType sl sid []
    let rece = EntryEnv (locpos l) recdt
    ss <- getStructs
    case Map.lookup n ss of
        Just es -> tcError (locpos l) $ MultipleDefinedStruct (pp n) (locpos $ entryLoc $ head $ Map.elems es)
        otherwise -> do
            modifyModuleEnv $ \env -> env { structs = Map.insert n (Map.singleton i rece) (structs env) }
            dirtyGDependencies $ Right $ Right n
    
            -- solve the body
            solveTop l "newStruct"
            dict <- liftM (head . tDict) State.get
            --i <- newModuleTyVarId
            d'' <- substFromTDict "newStruct body" (locpos l) dict False Map.empty d'
            let dt = DecT $ DecType i False [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] d''
            let e = EntryEnv (locpos l) dt
            liftIO $ putStrLn $ "newStruct: " ++ ppr l ++ " " ++ ppr e
            modifyModuleEnv $ \env -> env { structs = Map.insert n (Map.singleton i e) (structs env) }
            return $ TypeName (Typed l dt) n

data SubstMode = CheckS | NoFailS | NoCheckS
    deriving (Eq,Data,Typeable,Show)

addSubstM :: (ProverK loc m) => loc -> Bool -> SubstMode -> Var -> Type -> TcM m ()
addSubstM l dirty mode v@(VarName vt vn) t = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    when dirty $ tcCstrM_ l $ Unifies (loc v) (tyOf t)
    t' <- case mode of
        NoCheckS -> return t
        otherwise -> do
            substs <- getTSubsts l
            substFromTSubsts "addSubst" l substs False Map.empty t
    case mode of
        NoCheckS -> add t'
        otherwise -> do
            vns <- fvs t'
            if (varIdTok vn || Map.member vn vns)
                then do -- add verification condition
                    case mode of
                        NoFailS -> genTcError (locpos l) $ text "failed to add recursive substitution" <+> pp v <+> text "=" <+> pp t'
                        CheckS -> do
                            let tv = (varNameToType v)
                            addErrorM l (TypecheckerError (locpos l) . (EqualityException ("substitution with type")) (pp tv) (pp t') . Just) $ tcCstrM_ l $ Equals tv t'
                else add t'
  where
    add t' = do -- add substitution
--      liftIO $ putStrLn $ "addSubstM " ++ ppr v ++ " = " ++ ppr t'
        updateHeadTDict $ \d -> return ((),d { tSubsts = TSubsts $ Map.insert vn t' (unTSubsts $ tSubsts d) })
        removeFree vn
        when dirty $ dirtyGDependencies $ Left vn
        -- register variable assignment in the top-most open constraint
        State.modify $ \env -> env { openedCstrs = mapHead (mapSnd $ Set.insert vn) (openedCstrs env) }
    
newDomainTyVar :: (MonadIO m) => String -> SVarKind -> Maybe Doc -> TcM m SecType
newDomainTyVar str k doc = do
    n <- freeVarId str doc
    return $ SVar n k

newDimVar :: (MonadIO m) => Maybe Doc -> TcM m Expr
newDimVar doc = do
    n <- freeVarId "dim" doc
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newTypedVar :: (MonadIO m) => String -> a -> Maybe Doc -> TcM m (VarName VarIdentifier a)
newTypedVar s t doc = liftM (VarName t) $ freeVarId s doc

newVarOf :: (MonadIO m) => String -> Type -> Maybe Doc -> TcM m Type
newVarOf str TType doc = newTyVar doc
newVarOf str BType doc = liftM BaseT $ newBaseTyVar doc
newVarOf str (SType k) doc = liftM SecT $ newDomainTyVar str k doc
newVarOf str t doc | typeClass "newVarOf" t == TypeC = liftM (IdxT . varExpr) $ newTypedVar str t doc
newVarOf str (VAType b sz) doc = liftM VArrayT $ newArrayVar b sz doc

newArrayVar :: (MonadIO m) => Type -> Expr -> Maybe Doc -> TcM m VArrayType
newArrayVar b sz doc = do
    n <- freeVarId "varr" doc
    return $ VAVar n b sz

newTyVar :: (MonadIO m) => Maybe Doc -> TcM m Type
newTyVar doc = do
    n <- freeVarId "t" doc
    return $ ComplexT $ CVar n

newDecVar :: (MonadIO m) => Maybe Doc -> TcM m DecType
newDecVar doc = do
    n <- freeVarId "dec" doc
    return $ DVar n
    
newBaseTyVar :: (MonadIO m) => Maybe Doc -> TcM m BaseType
newBaseTyVar doc = do
    n <- freeVarId "b" doc
    return $ BVar n

newIdxVar :: (MonadIO m) => Maybe Doc -> TcM m Var
newIdxVar doc = do
    n <- freeVarId "idx" doc
    let v = VarName (BaseT index) n
    return v
    
newSizeVar :: (MonadIO m) => Maybe Doc -> TcM m Expr
newSizeVar doc = do
    n <- freeVarId "sz" doc
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newSizesVar :: (MonadIO m) => Expr -> Maybe Doc -> TcM m [(Expr,IsVariadic)]
newSizesVar dim doc = do
    n <- freeVarId "szs" doc
    let t = VAType (BaseT index) dim
    let v = VarName t n
    return [(RVariablePExpr t v,True)]
    
mkVariadicTyArray :: (MonadIO m) => IsVariadic -> Type -> TcM m Type
mkVariadicTyArray False t = return t
mkVariadicTyArray True t = do
    sz <- newSizeVar Nothing
    return $ VAType t sz

addValueM :: ProverK loc m => loc -> Bool -> SubstMode -> Var -> Expr -> TcM m ()
addValueM l dirty mode v e = addSubstM l dirty mode v (IdxT e)
    
--addValue :: (MonadIO m,Location loc) => loc -> VarIdentifier -> Expr -> TcM m ()
--addValue l v e = do
----    liftIO $ putStrLn $ "addValue " ++ ppr v ++ " " ++ ppr e
--    updateHeadTDict $ \d -> return ((),d { tSubsts = TSubsts $ Map.insert v (IdxT e) (unTSubsts $ tSubsts d) })
--    removeFree v
--
--addValueM :: (ProverK loc m) => Bool -> loc -> Var -> Expr -> TcM m ()
--addValueM checkTy l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
--addValueM checkTy l v@(VarName t n) e = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
--    when checkTy $ tcCstrM_ l $ Unifies t (loc e)
--    addValue l n e
--    addGDependencies $ Left n
--    dirtyGDependencies $ Left n

openCstr :: (MonadIO m,Location loc) => loc -> IOCstr -> TcM m ()
openCstr l o = do
    opts <- TcM $ lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "opened constraints"
        else State.modify $ \e -> e { openedCstrs = (o,Set.empty) : openedCstrs e }

closeCstr :: (MonadIO m) => TcM m ()
closeCstr = do
    State.modify $ \e -> e { openedCstrs = tail (openedCstrs e) }

resolveIOCstr_ :: ProverK loc m => loc -> IOCstr -> (TCstr -> IOCstrGraph -> Maybe (Context LocIOCstr ()) -> TcM m ShowOrdDyn) -> TcM m ()
resolveIOCstr_ l iok resolve = resolveIOCstr l iok resolve >> return ()

resolveIOCstr :: ProverK loc m => loc -> IOCstr -> (TCstr -> IOCstrGraph -> Maybe (Context LocIOCstr ()) -> TcM m ShowOrdDyn) -> TcM m ShowOrdDyn
resolveIOCstr l iok resolve = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated rest x -> do
            remove
            addHeadTDict l rest
            return x
        Erroneous err -> throwError err
        Unevaluated -> trySolve
  where
    trySolve = do
        openCstr l iok
        gr <- liftM (tCstrs . head . tDict) State.get
        let ctx = contextGr gr (ioCstrId iok)
        remove
        (x,rest) <- tcWith (locpos l) "resolveIOCstr" $ resolve (kCstr iok) gr ctx
        liftIO $ writeUniqRef (kStatus iok) $ Evaluated rest x
        closeCstr
        addHeadTDict l rest
        -- register constraints dependencies from the dictionary into the global state
        registerIOCstrDependencies iok gr ctx
        --liftIO $ putStrLn $ "resolveIOCstr close " ++ ppr (ioCstrId iok)
        return x
    remove = updateHeadTDict $ \d -> return ((),d { tCstrs = delNode (ioCstrId iok) (tCstrs d) })

registerIOCstrDependencies :: (MonadIO m) => IOCstr -> IOCstrGraph -> Maybe (Context LocIOCstr ()) -> TcM m ()
registerIOCstrDependencies iok gr ctx = do
    case ctx of
        Nothing -> return ()
        Just (deps,_,_,_) -> forM_ deps $ \(_,d) -> case lab gr d of
            Nothing -> return ()
            Just x -> addIODependency (unLoc x) (Set.singleton iok)

-- | adds a dependency on the given variable for all the opened constraints
addGDependencies :: (MonadIO m) => GIdentifier -> TcM m ()
addGDependencies v = do
    cstrs <- liftM openedCstrs State.get
    addGDependency v (map fst cstrs)
    
addGDependency :: (MonadIO m) => GIdentifier -> [IOCstr] -> TcM m ()
addGDependency v cstrs = do
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps v
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps v m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)

addIODependency :: (MonadIO m) => IOCstr -> Set IOCstr -> TcM m ()
addIODependency v cstrs = do
    deps <- liftM ioDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps (uniqId $ kStatus v)
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps (uniqId $ kStatus v) m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)

-- adds a dependency to the constraint graph
addIOCstrDependencies :: TDict -> Set LocIOCstr -> LocIOCstr -> Set LocIOCstr -> TDict
addIOCstrDependencies dict from iok to = dict { tCstrs = add $ tCstrs dict }
    where
    add gr = insLabEdges froms $ insLabEdges tos $ tryInsNode (gid iok,iok) gr 
    tos = map (\k -> ((gid iok,iok),(gid k,k),())) $ Set.toList to
    froms = map (\k -> ((gid k,k),(gid iok,iok),())) $ Set.toList from
    gid = ioCstrId . unLoc

addIOCstrDependenciesM :: (MonadIO m) => Bool -> Deps -> LocIOCstr -> Deps -> TcM m ()
addIOCstrDependenciesM filterDeps froms iok tos = do
    ns <- getCstrNodes
--    liftIO $ putStrLn $ "addIOCstrDependenciesM " ++ ppr (mapSet (ioCstrId . unLoc) froms) ++ " --> " ++ ppr (ioCstrId $ unLoc iok) ++ " --> " ++ ppr (mapSet (ioCstrId . unLoc) tos)
    let froms' = if filterDeps then Set.filter (flip Set.member ns . ioCstrId . unLoc) froms else froms
    let tos' = if filterDeps then Set.filter (flip Set.member ns . ioCstrId . unLoc) tos else tos
    updateHeadTDict $ \d -> return ((),addIOCstrDependencies d froms' iok tos')
    
getCstrNodes :: Monad m => TcM m (Set Int)
getCstrNodes = do
    dicts <- liftM tDict State.get
    return $ foldr (\d xs -> Set.fromList (nodes $ tCstrs d) `Set.union` xs) Set.empty dicts

addHeadTDict :: (ProverK loc m) => loc -> TDict -> TcM m ()
addHeadTDict l d = updateHeadTDict $ \x -> liftM ((),) $ appendTDict l NoFailS x d

addHeadTCstrs :: (ProverK loc m) => loc -> IOCstrGraph -> TcM m ()
addHeadTCstrs l ks = addHeadTDict l $ TDict ks Set.empty emptyTSubsts

addHeadTFlatCstrs :: (ProverK loc m) => loc -> Set LocIOCstr -> TcM m ()
addHeadTFlatCstrs l ks = addHeadTDict l $ TDict (Graph.mkGraph nodes []) Set.empty (TSubsts Map.empty)
    where nodes = map (\n -> (ioCstrId $ unLoc n,n)) $ Set.toList ks

getHyps :: (MonadIO m) => TcM m Deps
getHyps = do
    deps <- getDeps
    return $ Set.filter (isHypCstr . kCstr . unLoc) deps

getDeps :: (MonadIO m) => TcM m Deps
getDeps = do
    env <- State.get
    return $ globalDeps env `Set.union` localDeps env

tcWithCstrs :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,Set LocIOCstr)
tcWithCstrs l msg m = do
    (x,d) <- tcWith (locpos l) msg m
    addHeadTDict l d
    return (x,flattenIOCstrGraphSet $ tCstrs d)

cstrSetToGraph :: Location loc => loc -> Set IOCstr -> IOCstrGraph
cstrSetToGraph l xs = foldr (\x gr -> insNode (ioCstrId x,Loc (locpos l) x) gr) Graph.empty (Set.toList xs)

newTDictCstr :: (MonadIO m,Location loc) => loc -> TCstr -> TDict -> TcM m (IOCstr,TDict)
newTDictCstr l c dict = do
    iok <- liftIO $ newIOCstr c
    return (iok,dict { tCstrs = insNode (ioCstrId iok,Loc (locpos l) iok) (tCstrs dict) })

---- | Adds a new template constraint to the environment
newTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> TcM m IOCstr
newTemplateConstraint l c = do
    updateHeadTDict (newTDictCstr (locpos l) c)

--erroneousTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> SecrecError -> TcM m IOCstr
--erroneousTemplateConstraint l c err = do
--    updateHeadTDict (insertTDictCstr (locpos l) c $ Erroneous err)

removeCstr :: ProverK Position m => Unique -> TcM m ()
removeCstr i = do
    updateHeadTCstrs $ \gr -> return ((),Graph.delNode (hashUnique i) gr)

updateHeadTCstrs :: (Monad m) => (IOCstrGraph -> TcM m (a,IOCstrGraph)) -> TcM m a
updateHeadTCstrs upd = updateHeadTDict $ \d -> do
    (x,gr') <- upd (tCstrs d)
    return (x,d { tCstrs = gr' })

updateHeadTDict :: (Monad m) => (TDict -> TcM m (a,TDict)) -> TcM m a
updateHeadTDict upd = do
    e <- State.get
    (x,d') <- updHeadM upd (tDict e)
    let e' = e { tDict = d' }
    State.put e'
    return x

-- | forget the result for a constraint when the value of a variable it depends on changes
dirtyGDependencies :: (MonadIO m) => GIdentifier -> TcM m ()
dirtyGDependencies v = do
    --liftIO $ putStr $ "dirtyGDependencies " ++ ppr v
    opens <- liftM openedCstrs State.get
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps v
    case mb of
        Nothing -> return ()
        Just m -> do
            liftIO $ WeakMap.forM_ m $ \(u,x) -> do
                -- dirty other constraint dependencies
                dirtyIOCstrDependencies (map fst opens) x
    --liftIO $ putStrLn "\n"

dirtyIOCstrDependencies :: [IOCstr] -> IOCstr -> IO ()
dirtyIOCstrDependencies opens iok = do
    unless (elem iok opens) $ do
        --putStr $ " " ++ ppr (ioCstrId iok)
        writeUniqRef (kStatus iok) Unevaluated
    deps <- liftM ioDeps $ readIORef globalEnv
    mb <- WeakHash.lookup deps (uniqId $ kStatus iok)
    case mb of
        Nothing -> return ()
        Just m -> WeakMap.forM_ m $ \(u,x) -> dirtyIOCstrDependencies opens x

-- we need global const variables to distinguish them during typechecking
addConst :: MonadIO m => Scope -> Identifier -> TcM m VarIdentifier
addConst scope vi = do
    vi' <- freeVarId vi $ Just $ pp vi
    case scope of
        LocalScope -> State.modify $ \env -> env { localConsts = Map.insert vi vi' $ localConsts env }
        GlobalScope -> modifyModuleEnv $ \env -> env { globalConsts = Map.insert vi vi' $ globalConsts env }
--    addFree vi'
    return vi'

getPureClass :: Monad m => Bool -> Bool -> TcM m ProcClass
getPureClass isAnn isPure = do
    env <- State.get
    let vs = if isPure then Set.empty else Map.keysSet $ globalVariables env
    return $ Proc isAnn vs vs

globalVariables :: TcEnv -> Map VarIdentifier (Bool,EntryEnv)
globalVariables env = Map.unions [Map.map snd $ globalVars e1,Map.map snd $ globalVars e2]
    where
    (e1,e2) = moduleEnv env

envVariables :: TcEnv -> Map VarIdentifier (Bool,(Bool,EntryEnv))
envVariables env = Map.unions [Map.map (False,) $ localVars env,Map.map ((True,) . snd) $ globalVars e1,Map.map ((True,) . snd) $ globalVars e2]
    where
    (e1,e2) = moduleEnv env

tcWarn :: (Monad m) => Position -> TypecheckerWarn -> TcM m ()
tcWarn pos msg = do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton pos $ Set.singleton $ TypecheckerWarning pos msg

errWarn :: (Monad m) => SecrecError -> TcM m ()
errWarn msg = do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton (loc msg) $ Set.singleton $ ErrWarn msg

isChoice :: (ProverK loc m) => loc -> Unique -> TcM m Bool
isChoice l x = do
    d <- concatTDict l NoCheckS =<< liftM tDict State.get
    return $ Set.member (hashUnique x) $ tChoices d

addChoice :: (Monad m) => Unique -> TcM m ()
addChoice x = updateHeadTDict $ \d -> return ((),d { tChoices = Set.insert (hashUnique x) $ tChoices d })

bytes :: ComplexType
bytes = CType Public (TyPrim $ DatatypeUint8 ()) (indexExpr 1)

appendTDict :: (ProverK loc m) => loc -> SubstMode -> TDict -> TDict -> TcM m TDict
appendTDict l noFail (TDict u1 c1 ss1) (TDict u2 c2 ss2) = do
    let u12 = unionGr u1 u2
    (ss12,ks) <- appendTSubsts l noFail ss1 ss2
    u12' <- foldM (\gr k -> insertNewCstr l k gr) u12 ks
    return $ TDict u12' (Set.union c1 c2) ss12

appendTSubsts :: (ProverK loc m) => loc -> SubstMode -> TSubsts -> TSubsts -> TcM m (TSubsts,[TCstr])
appendTSubsts l NoCheckS (TSubsts ss1) (TSubsts ss2) = return (TSubsts $ Map.union ss1 ss2,[])
appendTSubsts l mode ss1 (TSubsts ss2) = foldM (addSubst mode) (ss1,[]) (Map.toList ss2)
  where
    addSubst :: (ProverK Position m) => SubstMode -> (TSubsts,[TCstr]) -> (VarIdentifier,Type) -> TcM m (TSubsts,[TCstr])
    addSubst mode (ss,ks) (v,t) = do
        t' <- substFromTSubsts "appendTSubsts" l ss False Map.empty t
        vs <- fvs t'
        if (varIdTok v || Map.member v vs)
            then do
                case mode of
                    NoFailS -> genTcError (locpos l) $ text "failed to add recursive substitution " <+> pp v <+> text "=" <+> pp t'
                    CheckS -> do
                        isAnn <- getAnn
                        isPure <- getPure
                        return (ss,TcK (Equals (varNameToType $ VarName (tyOf t') v) t') isAnn isPure : ks)
            else return (TSubsts $ Map.insert v t' (unTSubsts ss),ks)

substFromTSubsts :: (Typeable loc,VarsIdTcM m,Location loc,VarsId (TcM m) a) => String -> loc -> TSubsts -> Bool -> Map VarIdentifier VarIdentifier -> a -> TcM m a
substFromTSubsts msg l tys doBounds ssBounds = substProxy msg (substsProxyFromTSubsts l tys) doBounds ssBounds 
    
substsProxyFromTSubsts :: (Location loc,Typeable loc,Monad m) => loc -> TSubsts -> SubstsProxy VarIdentifier (TcM m)
substsProxyFromTSubsts (l::loc) (TSubsts tys) = SubstsProxy $ \proxy x -> do
    case Map.lookup x tys of
        Nothing -> return Nothing
        Just ty -> case proxy of
            (eq (typeRep :: TypeOf VarIdentifier) -> EqT) ->
                return $ fmap varNameId $ typeToVarName ty
            (eq (typeRep :: TypeOf Var) -> EqT) ->
                return $ typeToVarName ty
            (eq (typeRep :: TypeOf (SecTypeSpecifier VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    SecT s -> liftM Just $ secType2SecTypeSpecifier l s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (TemplateTypeArgument VarIdentifier (Typed loc))) -> EqT) ->
                liftM Just $ type2TemplateTypeArgument l ty
            (eq (typeRep :: TypeOf (TypeSpecifier VarIdentifier (Typed loc))) -> EqT) ->
                type2TypeSpecifier l ty
            (eq (typeRep :: TypeOf (DatatypeSpecifier VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    BaseT b -> liftM Just $ baseType2DatatypeSpecifier l b
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (VarName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToVarName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier Type)) -> EqT) ->
                return $ typeToDomainName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier ())) -> EqT) ->
                return $ fmap funit $ typeToDomainName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToDomainName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier Type)) -> EqT) ->
                return $ typeToTypeName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier ())) -> EqT) ->
                return $ fmap funit $ typeToTypeName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToTypeName ty
            (eq (typeRep :: TypeOf Type) -> EqT) ->
                return $ Just ty
            (eq (typeRep :: TypeOf SecType) -> EqT) ->
                case ty of
                    SecT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf VArrayType) -> EqT) ->
                case ty of
                    VArrayT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf DecType) -> EqT) ->
                case ty of
                    DecT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf ComplexType) -> EqT) ->
                case ty of
                    ComplexT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf BaseType) -> EqT) ->
                case ty of
                    BaseT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf Expr) -> EqT) ->
                case ty of
                    IdxT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (Expression VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    IdxT s -> return $ Just $ fmap (Typed l) s
                    otherwise -> return Nothing
            otherwise -> return Nothing
  where
    eq x proxy = eqTypeOf x (typeOfProxy proxy)

concatTDict :: (ProverK loc m) => loc -> SubstMode -> [TDict] -> TcM m TDict
concatTDict l noFail = Foldable.foldlM (appendTDict l noFail) emptyTDict

appendPureTDict :: (ProverK loc m) => loc -> SubstMode -> PureTDict -> PureTDict -> TcM m PureTDict
appendPureTDict l noFail (PureTDict u1 ss1) (PureTDict u2 ss2) = do
    (ss12,ks) <- appendTSubsts l noFail ss1 ss2
    let u12 = unionGr u1 u2
    u12' <- liftIO $ foldM (\gr k -> insNewNodeIO (Loc (locpos l) k) gr) u12 ks
    return $ PureTDict u12' ss12

insertNewCstr :: (MonadIO m,Location loc) => loc -> TCstr -> IOCstrGraph -> TcM m IOCstrGraph
insertNewCstr l c gr = do
    iok <- liftIO $ newIOCstr c
    return $ insNode (ioCstrId iok,Loc (locpos l) iok) gr

newIOCstr :: TCstr -> IO IOCstr
--newIOCstr c = liftM (IOCstr c) $ newUniqRef Unevaluated
newIOCstr c = do
    cstrs <- liftM gCstrs $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup cstrs c
    case mb of
        Nothing -> liftM (IOCstr c) $ newUniqRef Unevaluated
        Just (IOCstr _ st) -> return $ IOCstr c st

getTSubsts :: (ProverK loc m) => loc -> TcM m TSubsts
getTSubsts l = do
    env <- State.get
    let (x,y) = moduleEnv env
    let xs = Map.foldrWithKey (\k (mb,_) m -> maybe m (\e -> Map.insert k (IdxT e) m) mb) Map.empty (globalVars x)
    let ys = Map.foldrWithKey (\k (mb,_) m -> maybe m (\e -> Map.insert k (IdxT e) m) mb) Map.empty (globalVars y)
    d <- concatTDict l NoCheckS $ tDict env
    return $ TSubsts $ unTSubsts (tSubsts d) `Map.union` xs `Map.union` ys

substFromTDict :: (Vars VarIdentifier (TcM m) a,ProverK loc m) => String -> loc -> TDict -> Bool -> Map VarIdentifier VarIdentifier -> a -> TcM m a
substFromTDict msg l dict doBounds ssBounds = substFromTSubsts msg l (tSubsts dict) doBounds ssBounds
    
specializeM :: (Vars VarIdentifier (TcM m) a,ProverK loc m) => loc -> a -> TcM m a
specializeM l a = do
    ss <- getTSubsts l
    substFromTSubsts "specialize" l ss False Map.empty a

ppM :: (Vars VarIdentifier (TcM m) a,PP a,ProverK loc m) => loc -> a -> TcM m Doc
ppM l a = liftM pp $ specializeM l a

ppArrayRangesM :: (ProverK loc m) => loc -> [ArrayProj] -> TcM m Doc
ppArrayRangesM l = liftM (sepBy comma) . mapM (ppM l)

--removeTSubsts :: Monad m => Set VarIdentifier -> TcM m ()
--removeTSubsts vs = do
--    env <- State.get
--    let ds = tDict env
--    let remSub d = d { tSubsts = TSubsts $ Map.difference (unTSubsts $ tSubsts d) (Map.fromSet (const $ NoType "rem") vs) }
--    let ds' = map remSub ds
--    State.put $ env { tDict = ds' }

tcLocal :: ProverK loc m => loc -> String -> TcM m a -> TcM m a
tcLocal l msg m = do
    env <- State.get
    x <- m
    State.modify $ \e -> e { localConsts = localConsts env, localVars = localVars env, localDeps = localDeps env }
    return x

withRecs :: Monad m => ModuleTcEnv -> TcM m a -> TcM m a
withRecs rec m = do
    old <- liftM recEnv State.get
    State.modify $ \env -> env { recEnv = old `mappend` rec }
    x <- m
    State.modify $ \env -> env { recEnv = old }
    return x

askRecs :: Monad m => TcM m ModuleTcEnv
askRecs = liftM recEnv State.get

tcError :: (MonadIO m) => Position -> TypecheckerErr -> TcM m a
tcError pos msg = throwTcError $ TypecheckerError pos msg  

genTcError :: (MonadIO m) => Position -> Doc -> TcM m a
genTcError pos msg = throwTcError $ TypecheckerError pos $ GenTcError msg  

throwTcError :: (MonadIO m) => SecrecError -> TcM m a
throwTcError err = do
    (i,SecrecErrArr f) <- Reader.ask
    let err2 = f err
    ios <- liftM openedCstrs State.get
    let add (io,vs) = do
        -- write error to the constraint's result
        liftIO $ writeUniqRef (kStatus io) (Erroneous err2)
        -- dirty variables assigned by this constraint
        forM_ vs (dirtyGDependencies . Left)
    mapM_ add ios
    throwError err2     

-- a new dictionary
newDict l msg = do
    opts <- TcM $ lift Reader.ask
    size <- liftM (length . tDict) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "dictionaries"
        else do
            State.modify $ \e -> e { tDict = emptyTDict : tDict e }
--            liftIO $ putStrLn $ "newDict " ++ show msg ++ " " ++ show size

tcWith :: (VarsIdTcM m) => Position -> String -> TcM m a -> TcM m (a,TDict)
tcWith l msg m = do
    newDict l $ "tcWith " ++ msg
    x <- m
    d <- liftM (head . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (x:xs) = xs


addErrorM :: (MonadIO m,Location loc) => loc -> (SecrecError -> SecrecError) -> TcM m a -> TcM m a
addErrorM l err m = addErrorM' l (1,err) m

addErrorM' :: (MonadIO m,Location loc) => loc -> (Int,SecrecError -> SecrecError) -> TcM m a -> TcM m a
addErrorM' l (j,err) (TcM m) = do
    size <- liftM fst Reader.ask
    opts <- askOpts
    if (size + j) > constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "nested errors"
        else TcM $ RWS.withRWST (\(i,SecrecErrArr f) s -> ((i + j,SecrecErrArr $ f . err),s)) m

addErrorM'' :: (MonadIO m,Location loc) => loc -> (Int,SecrecErrArr) -> TcM m a -> TcM m a
addErrorM'' l (j,SecrecErrArr err) m = addErrorM' l (j,err) m