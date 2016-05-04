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
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
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

import Data.Graph.Inductive              as Graph
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

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as Pretty

import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap

import System.Mem.Weak.Exts as Weak

getAllVars scope = getVarsPred scope (const True)
getVars scope cl = getVarsPred scope (== cl)

-- | Gets the variables of a given type class
getVarsPred :: (MonadIO m) => Scope -> (TypeClass -> Bool) -> TcM m (Map VarIdentifier (Bool,EntryEnv))
getVarsPred GlobalScope f = do
    (x,y) <- liftM moduleEnv State.get
    let vs = globalVars x `Map.union` globalVars y
    return $ Map.filter (\(_,e) -> f $ typeClass "getVarsG" (entryType e)) vs
getVarsPred LocalScope f = do
    vs <- liftM vars State.get
    return $ Map.filterWithKey (\k (_,e) -> f $ typeClass ("getVarsL " ++ ppr k ++ ppr (locpos $ entryLoc e)) (entryType e)) vs

addVar :: (MonadIO m) => Scope -> VarIdentifier -> Bool -> EntryEnv -> TcM m ()
addVar GlobalScope n b e = modifyModuleEnv $ \env -> env { globalVars = Map.insert n (b,e) (globalVars env) }
addVar LocalScope n b e = modify $ \env -> env { localVars = Map.insert n (b,e) (localVars env) }

getFrees :: (Monad m) => TcM m (Set VarIdentifier)
getFrees = liftM localFrees State.get

-- replaces a constraint in the constraint graph by a constraint graph
replaceCstrWithGraph :: (MonadIO m,Location loc) => loc -> Int -> Set (LocIOCstr) -> IOCstrGraph -> Set (LocIOCstr) -> TcM m ()
replaceCstrWithGraph l kid ins gr outs = do
    let cs = flattenIOCstrGraph gr
--    liftIO $ putStrLn $ "replaceCstrWithGraph " ++ ppr kid ++ " for " ++ show (sepBy space $ map (pp . ioCstrId . unLoc) cs)
    updateHeadTDict $ \d -> return ((),d { tCstrs = unionGr gr $ delNode kid (tCstrs d) })
    forM_ cs $ \c -> addIOCstrDependenciesM (Set.filter (\x -> ioCstrId (unLoc x) /= kid) ins) c (Set.filter (\x -> ioCstrId (unLoc x) /= kid) outs)
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

checkVariable :: (MonadIO m,Location loc) => Bool -> Scope -> VarName VarIdentifier loc -> TcM m (VarName VarIdentifier (Typed loc))
checkVariable isConst scope (VarName l n) = do
    vs <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    consts <- getConsts
    let n' = case varIdUniq n of
                Nothing -> maybe n id (Map.lookup (varIdBase n) consts)
                otherwise -> n
    case Map.lookup n' vs of
        Just (b,e) -> do
            when (isConst && b) $ tcError (locpos l) $ AssignConstVariable (pp n')
            return $ VarName (Typed l $ entryType e) n'
        Nothing -> tcError (locpos l) $ VariableNotFound (pp n')

-- | Adds a new variable to the environment
newVariable :: (MonadIO m,ProverK loc m) => Scope -> VarName VarIdentifier (Typed loc) -> Maybe (Expression VarIdentifier (Typed loc)) -> Bool -> TcM m ()
newVariable scope v@(VarName (Typed l t) n) val isConst = do
    vars <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    case Map.lookup n vars of
        Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
        Nothing -> return ()
    addVar scope n isConst (EntryEnv (locpos l) t)
--    case scope of
--        LocalScope -> addFree n
--        otherwise -> return ()
    case val of
        Just e -> do
            unifiesExprTy l True (fmap typed $ varExpr v) (fmap typed e)
        Nothing -> return ()

addDeps :: (MonadIO m) => Scope -> Set (Loc Position IOCstr) -> TcM m ()
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

tcAddDeps :: (VarsIdTcM m,Location loc) => loc -> String -> TcM m a -> TcM m a
tcAddDeps l msg m = do
    (x,ks) <- tcWithCstrs l msg m
    forM_ ks $ addDep LocalScope
    return x
    
tryAddHypothesis :: (MonadIO m,Location loc) => loc -> Scope -> Set (Loc Position IOCstr) -> HypCstr -> TcM m ()
tryAddHypothesis l scope deps hyp = do
    opts <- askOpts
    when (checkAssertions opts) $ do
        iok <- updateHeadTDict $ \d -> insertTDictCstr (locpos l) (HypK hyp) Unevaluated d
        addDep scope $ Loc (locpos l) iok
        addIOCstrDependenciesM deps (Loc (locpos l) iok) Set.empty

-- | Adds a new domain variable to the environment
newDomainVariable :: (MonadIO m,Location loc) => Scope -> DomainName VarIdentifier (Typed loc) -> TcM m ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    ds <- getDomains
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (pp n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == KindC || k == VArrayC KindC)
            case Map.lookup n vars of
                Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
                Nothing -> addVar scope n False (EntryEnv (locpos l) t)

-- | Adds a new type variable to the environment
newTypeVariable :: (MonadIO m,Location loc) => Scope -> TypeName VarIdentifier (Typed loc) -> TcM m ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    ss <- getStructs
    case Map.lookup n ss of
        Just (b,es) -> tcError (locpos l) $ InvalidTypeVariableName (pp n) (map (locpos . entryLoc) (maybeToList b ++ Map.elems es))
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
            case Map.lookup n vars of
                Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
                Nothing -> addVar scope n False (EntryEnv (locpos l) t)

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
checkDomain :: (MonadIO m,Location loc) => DomainName VarIdentifier loc -> TcM m Type
checkDomain (DomainName l n) = do
    ds <- getDomains
    case Map.lookup n ds of
        Just e -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ SecT $ Private (DomainName () n) k
            otherwise -> genTcError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        Nothing -> do
            dvars <- getVarsPred LocalScope isDomain
            case Map.lookup n dvars of
                Just (_,e) -> return $ varNameToType $ VarName (entryType e) n
                Nothing -> tcError (locpos l) $ NotDefinedDomain (pp n)

-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: (MonadIO m,Location loc) => TypeName VarIdentifier loc -> TcM m ([EntryEnv])
checkType (TypeName l n) = do
    ss <- getStructs
    case Map.lookup n ss of
        Just (base,es) -> return (maybeToList base ++ Map.elems es)
        Nothing -> do
            vars <- getVarsPred LocalScope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
            case Map.lookup n vars of
                Just (_,e) -> return [ e { entryType = varNameToType (VarName (entryType e) n) } ] -- return the type variable
                Nothing -> tcError (locpos l) $ NotDefinedType (pp n)

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkNonTemplateType :: (MonadIO m,Location loc) => TypeName VarIdentifier loc -> TcM m Type
checkNonTemplateType tn@(TypeName l n) = do
    es <- checkType tn
    case es of
        [e] -> case entryType e of
            DecT d -> return $ BaseT $ TApp (funit tn) [] d
            t -> return t
        es -> tcError (locpos l) $ NoNonTemplateType (pp n)

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: (MonadIO m,Location loc) => TypeName VarIdentifier loc -> TcM m [EntryEnv]
checkTemplateType ty@(TypeName _ n) = do
    (es) <- checkType ty
    let check e = unless (isStructTemplate $ entryType e) $ tcError (locpos $ loc ty) $ NoTemplateType (pp n) (locpos $ entryLoc e) (pp $ entryType e)
    mapM_ check es
    return (es)

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: (MonadIO m,Location loc) => TemplateArgName VarIdentifier loc -> TcM m (TemplateArgName VarIdentifier (Typed loc))
checkTemplateArg (TemplateArgName l n) = do
    env <- getModuleEnv
    let ss = structs env
    let ds = domains env
    vs <- liftM vars State.get
    case (Map.lookup n ss,Map.lookup n ds,Map.lookup n vs) of
        (Just (base,es),Nothing,Nothing) -> case (maybeToList base ++ Map.elems es) of
            [e] -> if (isStructTemplate $ entryType e)
                then tcError (locpos l) $ NoNonTemplateType (pp n)
                else return $ TemplateArgName (Typed l $ entryType e) n
            es -> tcError (locpos l) $ NoNonTemplateType (pp n)
        (Nothing,Just e,Nothing) -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ TemplateArgName (Typed l $ SecT $ Private (DomainName () n) k) n
            otherwise -> genTcError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        (Nothing,Nothing,Just (b,e)) -> return $ TemplateArgName (Typed l $ varNameToType $ VarName (entryType e) n) n
        (mb1,mb2,mb3) -> tcError (locpos l) $ AmbiguousName (pp n) $ map (locpos . entryLoc) $ maybe [] (\(b,es) -> maybeToList b ++ Map.elems es) (mb1) ++ maybeToList (mb2) ++ maybeToList (fmap snd mb3)

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
addTemplateOperator :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps -> Op VarIdentifier (Typed loc) -> TcM m (Op VarIdentifier (Typed loc))
addTemplateOperator vars hdeps op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = funit op
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    (hbsubsts,[]) <- appendTSubsts (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateOp" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
--    liftIO $ putStrLn $ "addTemplateOp " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) dt')

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (ProverK loc m) => Deps -> Op VarIdentifier (Typed loc) -> TcM m (Op VarIdentifier (Typed loc))
newOperator hdeps op = do
    let Typed l t = loc op
    let o = funit op
    d <- typeToDecType l t
    (_,recdict) <- tcProve l "newOp head" $ addHeadTCstrs hdeps
    addHeadTDict recdict
    i <- newModuleTyVarId
    frees <- getFrees
    d' <- substFromTDict "newOp head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] emptyPureTDict Set.empty emptyPureTDict frees [] d'
    let rece = EntryEnv (locpos l) recdt
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert i rece . maybe Map.empty id) o (operators env) }
    dirtyGDependencies $ Right $ Left $ Right o
    
    solveStatic l
    dict <- liftM (head . tDict) State.get
    d'' <- substFromTDict "newOp body" l dict False Map.empty d'
    let td = DecT $ DecType i False [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] d''
    let e = EntryEnv (locpos l) td
--    liftIO $ putStrLn $ "addOp " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) td)
  
 -- | Checks that an operator exists.
checkOperator :: (VarsIdTcM m,Location loc) => ProcClass -> Op VarIdentifier loc -> TcM m [EntryEnv]
checkOperator cl@(Proc isAnn) op@(OpCast l t) = do
    addGDependencies $ Right $ Left $ Right $ funit op
    ps <- getOperators
    let cop = funit op
    -- select all cast declarations
    let casts = concatMap Map.elems $ Map.elems $ Map.filterWithKey (\k v -> isJust $ isOpCast k) ps
    return $ filter (\e -> isAnnProcClass (tyProcClass $ entryType e) <= isAnn) casts
checkOperator cl@(Proc isAnn) op = do
    addGDependencies $ Right $ Left $ Right $ funit op
    ps <- getOperators
    let cop = funit op
    case Map.lookup cop ps of
        Nothing -> tcError (locpos $ loc op) $ Halt $ NotDefinedOperator $ pp cop
        Just es -> return $ filter (\e -> isAnnProcClass (tyProcClass $ entryType e) <= isAnn) $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps -> ProcedureName VarIdentifier (Typed loc) -> TcM m (ProcedureName VarIdentifier (Typed loc))
addTemplateProcedure vars hdeps pn@(ProcedureName (Typed l t) n) = do
--    liftIO $ putStrLn $ "entering addTemplateProc " ++ ppr pn
    d <- typeToDecType l t
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    (hbsubsts,[]) <- appendTSubsts (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateProc" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
--    liftIO $ putStrLn $ "addTemplateProc " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ updLoc pn (Typed (unTyped $ loc pn) dt')

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (ProverK loc m) => Deps -> ProcedureName VarIdentifier (Typed loc) -> TcM m (ProcedureName VarIdentifier (Typed loc))
newProcedure hdeps pn@(ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    (_,recdict) <- tcProve l "newProc head" $ addHeadTCstrs hdeps
    addHeadTDict recdict
    i <- newModuleTyVarId
    frees <- getFrees
    d' <- substFromTDict "newProc head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] emptyPureTDict Set.empty emptyPureTDict frees [] d'
    let rece = EntryEnv (locpos l) recdt
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert i rece . maybe Map.empty id) n (procedures env) }
    dirtyGDependencies $ Right $ Left $ Left n
    
    solveStatic l
    dict <- liftM (head . tDict) State.get
    d'' <- substFromTDict "newProc body" l dict False Map.empty d'
    let dt = DecT $ DecType i False [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] d''
    let e = EntryEnv (locpos l) dt
--    liftIO $ putStrLn $ "addProc " ++ ppr (entryType e)
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ updLoc pn (Typed (unTyped $ loc pn) dt)
  
 -- | Checks that a procedure exists.
checkProcedure :: (MonadIO m,Location loc) => ProcClass -> ProcedureName VarIdentifier loc -> TcM m [EntryEnv]
checkProcedure cl@(Proc isAnn) pn@(ProcedureName l n) = do
    addGDependencies $ Right $ Left $ Left n
    ps <- getProcedures
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ Halt $ NotDefinedProcedure (pp n)
        Just es -> return $ filter (\e -> isAnnProcClass (tyProcClass $ entryType e) <= isAnn) $ Map.elems es

-- adds a recursive declaration for processing recursive constraints
withTpltDecRec :: (MonadIO m,Location loc) => loc -> DecType -> TcM m a -> TcM m a
withTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs p@(ProcType _ n@(Left pn) _ _ _ _ _)) m = do
    j <- newModuleTyVarId
    let recd = DecType j True ts hd hfrees emptyPureTDict bfrees specs p
    let rece = EntryEnv (locpos l) (DecT recd)
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.insert j rece . maybe Map.empty id) pn (procedures env) }
    x <- m
    modifyModuleEnv $ \env -> env { procedures = Map.alter (Just . Map.delete j . maybe Map.empty id) pn (procedures env) }
    return x
withTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs p@(ProcType _ n@(Right op) _ _ _ _ _)) m = do
    j <- newModuleTyVarId
    let o = funit op
    let recd = DecType j True ts hd hfrees emptyPureTDict bfrees specs p
    let rece = EntryEnv (locpos l) (DecT recd)
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.insert j rece . maybe Map.empty id) o (operators env) }
    x <- m
    modifyModuleEnv $ \env -> env { operators = Map.alter (Just . Map.delete j . maybe Map.empty id) o (operators env) }
    return x
withTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs s@(StructType _ (TypeName _ sn) _)) m = do
    j <- newModuleTyVarId
    let recd = DecType j True ts hd hfrees emptyPureTDict bfrees specs s
    (e,es) <- liftM ((!sn) . structs . snd . moduleEnv) State.get
    let rece = EntryEnv (locpos l) (DecT recd)
    modifyModuleEnv $ \env -> env { structs = Map.alter (Just . (\(e,es) -> (e,Map.insert j rece es)) . fromJust) sn (structs env) }
    x <- m
    modifyModuleEnv $ \env -> env { structs = Map.alter (Just . (\(e,es) -> (e,Map.delete j es)) . fromJust) sn (structs env) }
    return x

buildCstrGraph :: (ProverK Position m) => Set (LocIOCstr) -> TcM m (IOCstrGraph)
buildCstrGraph cstrs = do
    d <- concatTDict =<< liftM tDict State.get
    let gr = tCstrs d
    let tgr = Graph.trc gr 
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc cstrs) (Set.fromList opens)
    let gr' = Graph.nfilter (\n -> any (\h -> Graph.hasEdge tgr (n,ioCstrId h)) cs) tgr
    return gr'
    
splitHead :: (MonadIO m,Vars VarIdentifier (TcM m) Position) => Set (Loc Position IOCstr) -> TcM m (PureTDict,Set VarIdentifier,PureTDict,Set VarIdentifier)
splitHead deps = do
    d <- liftM (head . tDict) State.get
    frees <- getFrees
    hvs <- liftM Map.keysSet $ fvs $ Set.map (kCstr . unLoc) deps
    let hfrees = Set.intersection frees hvs
    let bfrees = Set.difference frees hfrees
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc deps) (Set.fromList opens)
    let gr = Graph.trc $ tCstrs d
    let hgr = nmap (fmap kCstr) $ Graph.nfilter (\n -> any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    let bgr = nmap (fmap kCstr) $ Graph.nfilter (\n -> not $ any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    return (PureTDict hgr (tSubsts d),hfrees,PureTDict bgr emptyTSubsts,bfrees)
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc))
addTemplateStruct vars hdeps tn@(TypeName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    (hbsubsts,[]) <- appendTSubsts (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateStruct" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
    ss <- getStructs
    case Map.lookup n ss of
        Just (Just base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate (pp n) (locpos $ loc base)
        otherwise -> modifyModuleEnv $ \env -> env { structs = Map.insert n (Just e,Map.empty) (structs env) }
    return $ updLoc tn (Typed (unTyped $ loc tn) dt')
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> [(Type,IsVariadic)] -> Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc))
addTemplateStructSpecialization vars specials hdeps tn@(TypeName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newModuleTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees specials d
    (hbsubsts,[]) <- appendTSubsts (pureSubsts hdict) (pureSubsts bdict)
    dt' <- substFromTSubsts "templateStructSpec" l hbsubsts False Map.empty dt
    let e = EntryEnv (locpos l) dt'
    modifyModuleEnv $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert i e s)) n (structs env) }
    return $ updLoc tn (Typed (unTyped $ loc tn) dt')

-- | Defines a new struct type
newStruct :: (ProverK loc m) => Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc))
newStruct hdeps tn@(TypeName (Typed l t) n) = do
    addGDependencies $ Right $ Right n
    d <- typeToDecType l t
    -- solve head constraints
    (_,recdict) <- tcProve l "newStruct head" $ addHeadTCstrs hdeps
    addHeadTDict recdict
    i <- newModuleTyVarId
    -- add a temporary declaration for recursive invocations
    frees <- getFrees
    d' <- substFromTDict "newStruct head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] emptyPureTDict Set.empty emptyPureTDict frees [] d'
    let rece = EntryEnv (locpos l) recdt
    modifyModuleEnv $ \env -> env { structs = Map.insert n (Just rece,Map.empty) (structs env) }
    dirtyGDependencies $ Right $ Right n
    
    -- solve the body
    solveStatic l
    dict <- liftM (head . tDict) State.get
    ss <- getStructs
    case Map.lookup n ss of
        Just (Just base,es) -> tcError (locpos l) $ MultipleDefinedStruct (pp n) (locpos $ entryLoc base)
        otherwise -> do
            i <- newModuleTyVarId
            d'' <- substFromTDict "newStruct body" (locpos l) dict False Map.empty d'
            let dt = DecT $ DecType i False [] emptyPureTDict Set.empty emptyPureTDict Set.empty [] d''
            let e = EntryEnv (locpos l) dt
            modifyModuleEnv $ \env -> env { structs = Map.insert n (Just e,Map.empty) (structs env) }
            return $ updLoc tn (Typed (unTyped $ loc tn) dt)

addSubstM :: (ProverK loc m) => loc -> Bool -> VarName VarIdentifier Type -> Type -> TcM m ()
addSubstM l dirty v t | varNameToType v == t = return ()
addSubstM l dirty v@(VarName vt vn) t = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    when dirty $ tcCstrM l $ Unifies (loc v) (tyOf t)
    substs <- getTSubsts
    t' <- substFromTSubsts "addSubst" l substs False Map.empty t
    vns <- fvs t'
    if Map.member vn vns
        then do -- add verification condition
            tcCstrM l $ Equals (varNameToType v) t'
        else do -- add substitution
            liftIO $ putStrLn $ "addSubstM " ++ ppr v ++ " = " ++ show t' ++ " " ++ ppr vns
            updateHeadTDict $ \d -> return ((),d { tSubsts = TSubsts $ Map.insert vn t' (unTSubsts $ tSubsts d) })
            when dirty $ dirtyGDependencies $ Left vn

constExpr :: ProverK loc m => SExpr VarIdentifier (Typed loc) -> TcM m (SExpr VarIdentifier (Typed loc))
constExpr e = do
    let Typed l t = loc e
    c <- newTypedVar "res" t $ Just $ pp e
    let cl = fmap (Typed l) c
    (ty,sz) <- type2TypeSpecifierNonVoid t
    let def = ConstStatement noloc $ ConstDeclaration noloc ty $ WrapNe $ ConstInitialization noloc cl sz (Just e)
    let st = StmtType (Set.singleton $ StmtReturn t)
    return $ LambdaExpr (Typed noloc t) [def,ReturnStatement (Typed noloc st) (Just $ varExpr cl)]

newDomainTyVar :: (MonadIO m) => SVarKind -> Maybe Doc -> TcM m SecType
newDomainTyVar k doc = do
    n <- freeVarId "d" doc
    return $ SVar n k

newDimVar :: (MonadIO m) => Maybe Doc -> TcM m (SExpr VarIdentifier Type)
newDimVar doc = do
    n <- freeVarId "dim" doc
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newTypedVar :: (MonadIO m) => String -> a -> Maybe Doc -> TcM m (VarName VarIdentifier a)
newTypedVar s t doc = liftM (VarName t) $ freeVarId s doc

newVarOf :: (MonadIO m) => String -> Type -> Maybe Doc -> TcM m Type
newVarOf str TType doc = newTyVar doc
newVarOf str BType doc = liftM BaseT $ newBaseTyVar doc
newVarOf str (SType k) doc = liftM SecT $ newDomainTyVar k doc
newVarOf str t doc | typeClass "newVarOf" t == TypeC = liftM (IdxT . varExpr) $ newTypedVar str t doc
newVarOf str (VAType b sz) doc = liftM VArrayT $ newArrayVar b sz doc

newArrayVar :: (MonadIO m) => Type -> SExpr VarIdentifier Type -> Maybe Doc -> TcM m VArrayType
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

newIdxVar :: (MonadIO m) => Maybe Doc -> TcM m (VarName VarIdentifier Type)
newIdxVar doc = do
    n <- freeVarId "idx" doc
    let v = VarName (BaseT index) n
    return v
    
newSizeVar :: (MonadIO m) => Maybe Doc -> TcM m (SExpr VarIdentifier Type)
newSizeVar doc = do
    n <- freeVarId "sz" doc
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newSizesVar :: (MonadIO m) => SExpr VarIdentifier Type -> Maybe Doc -> TcM m [(SExpr VarIdentifier Type,IsVariadic)]
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
    
addValue :: (MonadIO m,Location loc) => loc -> VarIdentifier -> SExpr VarIdentifier Type -> TcM m ()
addValue l v e = do
--    liftIO $ putStrLn $ "addValue " ++ ppr v ++ " " ++ ppr e
    updateHeadTDict $ \d -> return ((),d { tSubsts = TSubsts $ Map.insert v (IdxT e) (unTSubsts $ tSubsts d) })

addValueM :: (ProverK loc m) => Bool -> loc -> VarName VarIdentifier Type -> SExpr VarIdentifier Type -> TcM m ()
addValueM checkTy l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM checkTy l v@(VarName t n) e = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    when checkTy $ tcCstrM l $ Unifies t (loc e)
    addValue l n e
    addGDependencies $ Left n
    dirtyGDependencies $ Left n

openCstr :: (MonadIO m,Location loc) => loc -> IOCstr -> TcM m ()
openCstr l o = do
    opts <- TcM $ lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "opened constraints"
        else State.modify $ \e -> e { openedCstrs = o : openedCstrs e }

closeCstr :: (MonadIO m) => TcM m ()
closeCstr = do
    State.modify $ \e -> e { openedCstrs = tail (openedCstrs e) }

resolveIOCstr :: (MonadIO m,Location loc) => loc -> IOCstr -> (TCstr -> TcM m ShowOrdDyn) -> TcM m ShowOrdDyn
resolveIOCstr l iok resolve = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated x -> do
            remove
            return x
        Erroneous err -> throwError err
        Unevaluated -> trySolve
  where
    trySolve = do
        openCstr l iok
        t <- resolve $ kCstr iok
        liftIO $ writeUniqRef (kStatus iok) $ Evaluated t
        closeCstr
        -- register constraints dependencies from the dictionary into the global state
        registerIOCstrDependencies iok
        remove
        return t
    remove = updateHeadTDict $ \d -> return ((),d { tCstrs = delNode (ioCstrId iok) (tCstrs d) })

registerIOCstrDependencies :: (MonadIO m) => IOCstr -> TcM m ()
registerIOCstrDependencies iok = do
    gr <- liftM (tCstrs . head . tDict) State.get
    case contextGr gr (ioCstrId iok) of
        Nothing -> return ()
        Just (deps,_,_,_) -> forM_ deps $ \(_,d) -> case lab gr d of
            Nothing -> return ()
            Just x -> addIODependency (unLoc x) (Set.singleton iok)

-- | adds a dependency on the given variable for all the opened constraints
addGDependencies :: (MonadIO m) => GIdentifier -> TcM m ()
addGDependencies v = do
    cstrs <- liftM openedCstrs State.get
    addGDependency v cstrs
    
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
addIOCstrDependencies :: TDict -> Set (LocIOCstr) -> LocIOCstr -> Set (LocIOCstr) -> TDict
addIOCstrDependencies dict from iok to = dict { tCstrs = insLabEdges tos $ insLabEdges froms (tCstrs dict) }
    where
    tos = map (\k -> ((gid iok,iok),(gid k,k),())) $ Set.toList to
    froms = map (\k -> ((gid k,k),(gid iok,iok),())) $ Set.toList from
    gid = ioCstrId . unLoc

addIOCstrDependenciesM :: (MonadIO m) => Set (Loc Position IOCstr) -> Loc Position IOCstr -> Set (Loc Position IOCstr) -> TcM m ()
addIOCstrDependenciesM froms iok tos = do
--    liftIO $ putStrLn $ "addIOCstrDependenciesM " ++ ppr (mapSet (ioCstrId . unLoc) froms) ++ " --> " ++ ppr (ioCstrId $ unLoc iok) ++ " --> " ++ ppr (mapSet (ioCstrId . unLoc) tos)
    updateHeadTDict $ \d -> return ((),addIOCstrDependencies d froms iok tos)
    
addHeadTDict :: (ProverK Position m) => TDict -> TcM m ()
addHeadTDict d = updateHeadTDict $ \x -> liftM ((),) $ appendTDict x d

addHeadTCstrs :: (ProverK Position m) => Set (Loc Position IOCstr) -> TcM m ()
addHeadTCstrs ks = addHeadTDict $ TDict (Graph.mkGraph nodes []) Set.empty (TSubsts Map.empty)
    where nodes = map (\n -> (ioCstrId $ unLoc n,n)) $ Set.toList ks

getHyps :: (MonadIO m) => TcM m (Deps)
getHyps = do
    deps <- getDeps
    return $ Set.filter (isHypCstr . kCstr . unLoc) deps

getDeps :: (MonadIO m) => TcM m (Deps)
getDeps = do
    env <- State.get
    return $ globalDeps env `Set.union` localDeps env

tcWithCstrs :: (VarsIdTcM m,Location loc) => loc -> String -> TcM m a -> TcM m (a,Set (Loc Position IOCstr))
tcWithCstrs l msg m = do
    (x,d) <- tcWith (locpos l) msg m
    addHeadTDict d
    return (x,flattenIOCstrGraphSet $ tCstrs d)

cstrSetToGraph :: Location loc => loc -> Set IOCstr -> IOCstrGraph
cstrSetToGraph l xs = foldr (\x gr -> insNode (ioCstrId x,Loc (locpos l) x) gr) Graph.empty (Set.toList xs)

insertTDictCstr :: (MonadIO m,Location loc) => loc -> TCstr -> TCstrStatus -> TDict -> TcM m (IOCstr,TDict)
insertTDictCstr l c res dict = do
    iok <- liftIO $ newIOCstr c res
    return (iok,dict { tCstrs = insNode (ioCstrId iok,Loc (locpos l) iok) (tCstrs dict) })

---- | Adds a new template constraint to the environment
newTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> TcM m IOCstr
newTemplateConstraint l c = do
    updateHeadTDict (insertTDictCstr (locpos l) c Unevaluated)

erroneousTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> SecrecError -> TcM m IOCstr
erroneousTemplateConstraint l c err = do
    updateHeadTDict (insertTDictCstr (locpos l) c $ Erroneous err)

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
    cstrs <- liftM openedCstrs State.get
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps v
    case mb of
        Nothing -> return ()
        Just m -> do
            WeakMap.forGenericM_ m $ \(u,x) -> unless (elem x cstrs) $ do
                liftIO $ writeUniqRef (kStatus x) Unevaluated
                -- dirty other constraint dependencies
                dirtyIOCstrDependencies x

dirtyIOCstrDependencies :: (MonadIO m) => IOCstr -> TcM m ()
dirtyIOCstrDependencies iok = do
    deps <- liftM ioDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps (uniqId $ kStatus iok)
    case mb of
        Nothing -> return ()
        Just m -> liftIO $ WeakMap.forM_ m $ \(u,x) -> writeUniqRef (kStatus x) Unevaluated

-- we need global const variables to distinguish them during typechecking
addConst :: MonadIO m => Scope -> Identifier -> TcM m VarIdentifier
addConst scope vi = do
    vi' <- freeVarId vi Nothing
    case scope of
        LocalScope -> State.modify $ \env -> env { localConsts = Map.insert vi vi' $ localConsts env }
        GlobalScope -> modifyModuleEnv $ \env -> env { globalConsts = Map.insert vi vi' $ globalConsts env }
--    addFree vi'
    return vi'

vars :: TcEnv -> Map VarIdentifier (Bool,EntryEnv)
vars env = Map.unions [localVars env,globalVars e1,globalVars e2]
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

isChoice :: (ProverK Position m) => Unique -> TcM m Bool
isChoice x = do
    d <- concatTDict =<< liftM tDict State.get
    return $ Set.member (hashUnique x) $ tChoices d

addChoice :: (Monad m) => Unique -> TcM m ()
addChoice x = updateHeadTDict $ \d -> return ((),d { tChoices = Set.insert (hashUnique x) $ tChoices d })

bytes :: ComplexType
bytes = CType Public (TyPrim $ DatatypeUint8 ()) (indexSExpr 1) Nothing

appendTDict :: (ProverK Position m) => TDict -> TDict -> TcM m TDict
appendTDict (TDict u1 c1 ss1) (TDict u2 c2 ss2) = do
    let u12 = unionGr u1 u2
    (ss12,ks) <- appendTSubsts ss1 ss2
    u12' <- foldM (\gr k -> insertCstr (noloc::Position) k Unevaluated gr) u12 ks
    return $ TDict u12' (Set.union c1 c2) ss12

appendTSubsts :: (ProverK Position m) => TSubsts -> TSubsts -> TcM m (TSubsts,[TCstr])
appendTSubsts ss1 (TSubsts ss2) = foldM addSubst (ss1,[]) (Map.toList ss2)
  where
    addSubst :: (ProverK Position m) => (TSubsts,[TCstr]) -> (VarIdentifier,Type) -> TcM m (TSubsts,[TCstr])
    addSubst (ss,ks) (v,t) = do
        t' <- substFromTSubsts "appendTSubsts" (noloc::Position) ss False Map.empty t
        vs <- fvs t'
        if Map.member v vs
            then do
                return (ss,TcK (Equals (varNameToType $ VarName (tyOf t') v) t') : ks)
            else return (TSubsts $ Map.insert v t' (unTSubsts ss),ks)

substFromTSubsts :: (Typeable loc,VarsIdTcM m,Location loc,VarsId (TcM m) a) => String -> loc -> TSubsts -> Bool -> Map VarIdentifier VarIdentifier -> a -> TcM m a
substFromTSubsts msg l tys doBounds ssBounds = substProxy msg (substsProxyFromTSubsts l tys) doBounds ssBounds 
    
substsProxyFromTSubsts :: (Location loc,Typeable loc,Monad m) => loc -> TSubsts -> SubstsProxy VarIdentifier (TcM m)
substsProxyFromTSubsts (l::loc) (TSubsts tys) = SubstsProxy $ \proxy x -> do
    case Map.lookup x tys of
        Nothing -> return Nothing
        Just ty -> case proxy of
            (eq (typeRep :: TypeOf (VarName VarIdentifier Type)) -> EqT) ->
                return $ typeToVarName ty
            (eq (typeRep :: TypeOf (SecTypeSpecifier VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    SecT s -> liftM Just $ secType2SecTypeSpecifier s
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
            (eq (typeRep :: TypeOf (Expression VarIdentifier Type)) -> EqT) ->
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

concatTDict :: (ProverK Position m) => [TDict] -> TcM m TDict
concatTDict = Foldable.foldlM appendTDict emptyTDict

appendPureTDict :: (ProverK Position m) => PureTDict -> PureTDict -> TcM m PureTDict
appendPureTDict (PureTDict u1 ss1) (PureTDict u2 ss2) = do
    (ss12,ks) <- appendTSubsts ss1 ss2
    let u12 = unionGr u1 u2
    u12' <- liftIO $ foldM (\gr k -> insNewNodeIO (Loc noloc k) gr) u12 ks
    return $ PureTDict u12' ss12

insertCstr :: (MonadIO m,Location loc) => loc -> TCstr -> TCstrStatus -> IOCstrGraph -> TcM m IOCstrGraph
insertCstr l c res gr = do
    iok <- liftIO $ newIOCstr c res
    return $ insNode (ioCstrId iok,Loc (locpos l) iok) gr

newIOCstr :: TCstr -> TCstrStatus -> IO IOCstr
newIOCstr c res = do
    st <- newUniqRef res
    let io = IOCstr c st
    return io

getTSubsts :: (ProverK Position m) => TcM m TSubsts
getTSubsts = do
    env <- State.get
    d <- concatTDict $ tDict env
    return $ tSubsts d

substFromTDict :: (Typeable loc,VarsIdTcM m,Location loc,VarsId (TcM m) a) => String -> loc -> TDict -> Bool -> Map VarIdentifier VarIdentifier -> a -> TcM m a
substFromTDict msg l dict doBounds ssBounds = substFromTSubsts msg l (tSubsts dict) doBounds ssBounds
    
specializeM :: (Typeable loc,VarsId (TcM m) a,VarsIdTcM m,Location loc) => loc -> a -> TcM m a
specializeM l a = do
    ss <- getTSubsts
    substFromTSubsts "specialize" l ss False Map.empty a

ppM :: (Typeable loc,VarsId (TcM m) a,VarsIdTcM m,PP a,Location loc) => loc -> a -> TcM m Doc
ppM l a = liftM pp $ specializeM l a

ppArrayRangesM :: (Typeable loc,VarsIdTcM m,Location loc) => loc -> [ArrayProj] -> TcM m Doc
ppArrayRangesM l = liftM (sepBy comma) . mapM (ppM l)

removeTSubsts :: Monad m => Set VarIdentifier -> TcM m ()
removeTSubsts vs = do
    env <- State.get
    let ds = tDict env
    let remSub d = d { tSubsts = TSubsts $ Map.difference (unTSubsts $ tSubsts d) (Map.fromSet (const $ NoType "rem") vs) }
    let ds' = map remSub ds
    State.put $ env { tDict = ds' }

splitStaticCstrs :: IOCstrGraph -> (IOCstrGraph,[SCond VarIdentifier Type])
splitStaticCstrs gr = (Graph.nfilter (\x -> not $ elem x $ map fst nonstatics) gr,cs)
    where
    labs = labNodes gr
    nonstatics = filter (not . isStaticCstr . kCstr . unLoc . snd) labs
    cs = map (aux . kCstr . unLoc . snd) nonstatics
    aux (TcK (IsValid False c)) = c
    aux (DelayedK c _) = aux c

