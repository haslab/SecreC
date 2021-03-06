{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor, FunctionalDependencies, CPP #-}

module Language.SecreC.TypeChecker.Environment where

import Language.SecreC.IO
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
import {-# SOURCE #-} Language.SecreC.Transformation.Simplify
import {-# SOURCE #-} Language.SecreC.TypeChecker.Conversion
import Language.SecreC.Prover.Base

import qualified Data.Generics as Generics
import Data.IORef
import Data.Hashable
import Data.Either
import Data.Int
import Data.Word
import Data.Unique
import Data.Char
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

import Data.Graph.Inductive              as Graph hiding (mapSnd,mapFst)
import Data.Graph.Inductive.Graph        as Graph
import Data.Graph.Inductive.PatriciaTree as Graph
import Data.Graph.Inductive.Query.DFS    as Graph

import Control.Applicative
import Control.Monad.State.Strict as State hiding (mapAndUnzipM)
import Control.Monad.Reader as Reader hiding (mapAndUnzipM)
import Control.Monad.Writer.Strict as Writer hiding ((<>),mapAndUnzipM)
import Control.Monad.Trans.RWS.Strict (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Control.Monad.Except hiding (mapAndUnzipM)
import Control.DeepSeq as DeepSeq

import System.IO.Unsafe
import Unsafe.Coerce

import Safe

import Text.PrettyPrint as PP hiding (float,int,equals)
import qualified Text.PrettyPrint as Pretty hiding (equals)
import Text.Read (readMaybe)

#if INCREMENTAL
import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap
import System.Mem.Weak.Exts as Weak
#endif

import System.IO
import System.Exit
import qualified System.ProgressBar as Bar

decPos :: DecType -> Position
decPos = iDecPos . innerDec

innerDec :: DecType -> InnerDecType
innerDec (DecType i isRec ts hd bd specs idec) = idec

iDecPos :: InnerDecType -> Position
iDecPos d@(ProcType pl n pargs pret panns body cl) = pl
iDecPos d@(FunType isLeak pl n pargs pret panns body cl) = pl
iDecPos d@(StructType sl sid atts cl) = sl
iDecPos d@(AxiomType isLeak p qs pargs cl) = p
iDecPos d@(LemmaType isLeak pl n pargs panns body cl) = pl

withFrees :: ProverK loc m => loc -> TcM m a -> TcM m (a,Frees,Frees)
withFrees l m = do
    old <- State.gets localFrees
    --State.modify $! \env -> env { localFrees = Map.empty }
    x <- m
    new <- getFrees l
    State.modify $! \env -> env { localFrees = old }
    returnS (x,new `Map.difference` old,old `Map.difference` new)

onFrees :: ProverK loc m => loc -> TcM m a -> TcM m a
onFrees l m = do
    old <- State.gets localFrees
    State.modify $! \env -> env { localFrees = Map.empty }
    x <- m
    State.modify $! \env -> env { localFrees = old }
    returnS x


getDoSolve :: Monad m => TcM m Bool
getDoSolve = State.gets (\e -> length (tDict e) <= 1)

getDoAll :: Monad m => TcM m Bool
getDoAll = do
    env <- State.get
    returnS $ isNothing (inTemplate env)

--withInTemplate :: (ProverK Position m) => Maybe [TemplateTok] -> TcM m a -> TcM m a
--withInTemplate b m = do
--    old <- liftM inTemplate State.get
--    State.modify $! \env -> env { inTemplate = b }
--    x <- m
--    State.modify $! \env -> env { inTemplate = old }
--    returnS x

getHalt :: (ProverK Position m) => TcM m (TypecheckerErr -> TypecheckerErr)
getHalt = do
    doResolve <- getDoResolve
    let halt = if doResolve then id else Halt
    returnS halt

-- when we really need to resolve variables
getDoResolve :: Monad m => TcM m Bool
getDoResolve = do
    opts <- askOpts
    inCtx <- getInCtx
    returnS (inCtx || implicitContext opts == InferCtx)

isInlinableExpr :: Expression iden loc -> Bool
isInlinableExpr (UnaryExpr {}) = True
isInlinableExpr (BinaryExpr {}) = True
isInlinableExpr (ProcCallExpr {}) = True
isInlinableExpr e = False

unresolvedVariable :: (PP (TcM m) x,Variable x,ProverK loc m) => loc -> x -> TcM m b
unresolvedVariable l n = do
    doResolve <- getDoResolve
    let halt = if doResolve && not (isWritable n) then id else Halt
    ppn <- pp n
    tcError (locpos l) $! halt $! UnresolvedVariable (ppn)

chgInCtx :: Bool -> Maybe ([TemplateTok],Bool) -> Maybe ([TemplateTok],Bool)
chgInCtx True Nothing = Nothing
chgInCtx False Nothing = Nothing
chgInCtx b (Just (xs,_)) = Just (xs,b)

withInCtx :: ProverK Position m => Bool -> TcM m a -> TcM m a
withInCtx b m = do
    old <- getInCtx
    State.modify $! \env -> env { inTemplate = chgInCtx b (inTemplate env) }
    x <- m
    State.modify $! \env -> env { inTemplate = chgInCtx old (inTemplate env) }
    returnS x

getAllVars isAnn scope = getVarsPred isAnn scope (const True)
getVars isAnn scope cl = getVarsPred isAnn scope (== cl)

-- | Gets the variables of a given type class
getVarsPred :: (MonadIO m) => Bool -> Scope -> (TypeClass -> Bool) -> TcM m (Map GIdentifier (Bool,(Bool,Bool,EntryEnv)))
getVarsPred isAnn GlobalScope f = do
    (x,y) <- liftM moduleEnv State.get
    let vs = Map.map ((True,) . snd) $! globalVars x `Map.union` globalVars y
    returnS $ Map.filter (\(_,(_,b2,e)) -> b2 <= isAnn && f (typeClass "getVarsG" (entryType e))) vs
getVarsPred isAnn LocalScope f = do
    vs <- liftM (envVariables isAnn) State.get
    let aux k (_,(_,_,e)) = do
        ppk <- ppr k
        ppe <- ppr (locpos $! entryLoc e)
        returnS $ f $! typeClass ("getVarsL " ++ ppk ++ ppe) (entryType e)
    filterMapWithKeyM aux vs

addVar :: (ProverK loc m) => loc -> Scope -> GIdentifier -> Maybe Expr -> Bool -> Bool -> EntryEnv -> TcM m ()
addVar l GlobalScope n v isConst isAnn e = do
    dict <- liftM (headNe . tDict) State.get
    e' <- substFromTSubstsNoDec "addVar" l (tSubsts dict) False Map.empty e
    case v of
        Nothing -> modifyModuleEnv $! \env -> env { globalVars = Map.insert n (Nothing,(isConst,isAnn,e')) (globalVars env) }
        Just val -> do
            unifies l (loc val) (entryType e')
            val' <- substFromTSubstsNoDec "addVar" l (tSubsts dict) False Map.empty val
            modifyModuleEnv $! \env -> env { globalVars = Map.insert n (Just val',(isConst,isAnn,e')) (globalVars env) }
addVar l LocalScope n v isConst isAnn e = do
    modify $! \env -> env { localVars = Map.insert n (isConst,isAnn,e) (localVars env) }
    case v of
        Nothing -> returnS ()
        Just val -> assignsExprTy l (VarName (entryType e) n) val

dropLocalVar :: ProverK Position m => VarName GIdentifier loc -> TcM m ()
dropLocalVar v = modify $! \env -> env { localVars = Map.delete (varNameId v) $! localVars env }

--getVariadicFrees :: (ProverK loc m) => loc -> TcM m Frees
--getVariadicFrees l = liftM (Map.filter (\b -> b)) . getFrees l

getFrees :: (ProverK loc m) => loc -> TcM m Frees
getFrees l = do
    frees <- liftM localFrees State.get
    TSubsts ss <- getTSubsts l
    returnS $ Map.difference frees (Map.fromSet (const False) $! Map.keysSet ss)

chooseWriteVar :: ProverK loc m => loc -> VarIdentifier -> VarIdentifier -> TcM m Ordering
--chooseWriteVar l v1 v2 | not (varIdWrite v1) && varIdWrite v2 = returnS GT
--chooseWriteVar l v1 v2 | varIdWrite v1 && not (varIdWrite v2) = returnS LT
chooseWriteVar l v1 v2 = do
    vs <- getFrees l
    case (Map.lookup v1 vs,Map.lookup v2 vs) of
        (Just _,Nothing) -> returnS LT
        (Nothing,Just _) -> returnS GT
        otherwise -> returnS EQ

-- replaces a constraint in the constraint graph by a constraint graph
replaceCstrWithGraph :: (ProverK loc m) => loc -> Bool -> Int -> Set LocGCstr -> GCstrGraph -> Set LocGCstr -> TcM m ()
replaceCstrWithGraph l filterDeps kid ins gr outs = do
    let cs = flattenGCstrGraph gr
    --liftIO $! putStrLn $! "replaceCstrWithGraph " ++ ppr kid
    --    ++ " from " ++ show (sepBy space $! map (pp . gCstrId . unLoc) $! Set.toList ins)
    --    ++ " to " ++ show (sepBy space $! map (pp . gCstrId . unLoc) $! Set.toList outs)
    --    ++ " for " ++ show (sepBy space $! map (pp . gCstrId . unLoc) cs)
    updateHeadTDict l "replaceCstrWithGraph" $! \d -> returnS ((),d { tCstrs = unionGr gr $! delNode kid (tCstrs d) })
    forM_ cs $! \c -> addGCstrDependenciesM l filterDeps (Set.filter (\x -> gCstrId (unLoc x) /= kid) ins) c (Set.filter (\x -> gCstrId (unLoc x) /= kid) outs)
--    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--    liftIO $! putStrLn $! "replaceCstrWithGraph2 [" ++ show ss ++ "\n]"

withDeps :: MonadIO m => Scope -> TcM m a -> TcM m a
withDeps LocalScope m = do
    env <- State.get
    let l = localDeps env
    x <- m
    State.modify $! \env -> env { localDeps = l }
    returnS x
withDeps GlobalScope m = do
    env <- State.get
    let l = localDeps env
    let g = globalDeps env
    x <- m
    State.modify $! \env -> env { localDeps = l, globalDeps = g }
    returnS x

noLocalDeps :: MonadIO m => TcM m a -> TcM m (a,Set LocGCstr)
noLocalDeps m = do
    env <- State.get
    let l = localDeps env
    State.modify $! \env -> env { localDeps = Set.empty }
    x <- m
    newl <- State.gets localDeps
    State.modify $! \env -> env { localDeps = l }
    returnS (x,newl)

getConsts :: Monad m => TcM m (Map Identifier GIdentifier)
getConsts = do
    env <- State.get
    let (x,y) = moduleEnv env
    returnS $ Map.unions[localConsts env,globalConsts x,globalConsts y]

checkConst :: MonadIO m => GIdentifier -> TcM m GIdentifier
checkConst n@(VIden vn) = do
    consts <- getConsts
    let n' = case (varIdUniq vn) of
                Nothing -> maybe n id (Map.lookup (varIdBase vn) consts)
                otherwise -> n
    returnS n'

registerVar :: Monad m => Bool -> Bool -> GIdentifier -> Type -> TcM m ()
registerVar isGlobal isWrite (VIden v) t = if isWrite
    then chgDecClassM $! addDecClassVars emptyDecClassVars (Map.singleton v (t,isGlobal),isGlobal)
    else chgDecClassM $! addDecClassVars (Map.singleton v (t,isGlobal),isGlobal) emptyDecClassVars

checkVariable :: (ProverK loc m) => Bool -> Bool -> Bool -> Scope -> VarName VarIdentifier loc -> TcM m (VarName GIdentifier (Typed loc))
checkVariable isWrite cConst isAnn scope v@(VarName l n) = do
    vs <- getVarsPred isAnn scope isVariable
    n <- checkConst $! VIden n
    case Map.lookup n vs of
        Just (isGlobal,(isConst,bAnn,e)) -> do
            when cConst $! unless isConst $! do
                ppv <- pp v
                genTcError (locpos l) False $! text "expected variable" <+> ppv <+> text "to be a constant"
            unless isConst $! registerVar isGlobal isWrite n (entryType e) -- consts don't count as global variables for reads/writes
            when isGlobal $! do
                decK <- State.gets decKind
                when (decK == AKind || decK == LKind) $! do
                    ppv <- pp v
                    genTcError (locpos l) False $! text "cannot read/write global variable" <+> ppv <+> text "inside an axiom/lemma"
            when (isWrite && isConst) $! do
                ppn <- pp n
                tcError (locpos l) $! AssignConstVariable (ppn)
            --liftIO $! putStrLn $! "checkVariable " ++ ppr v ++ " " ++ ppr n
            returnS $ VarName (Typed l $! entryType e) n
        Nothing -> do
            ppn <- pp n
            tcError (locpos l) $! VariableNotFound (ppn)

-- | Adds a new variable to the environment
newVariable :: (ProverK loc m) => Scope -> Bool -> Bool -> VarName GIdentifier (Typed loc) -> Maybe (Expression GIdentifier (Typed loc)) -> TcM m ()
newVariable scope isConst isAnn v@(VarName (Typed l t) (VIden n)) val = do
    removeFree "newVariable" n
    vars <- getVarsPred isAnn scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    case Map.lookup (VIden n) vars of
        Just (_,(_,_,e)) -> do
            ppn <- pp n
            tcWarn (locpos l) $! ShadowedVariable (ppn) (locpos $! entryLoc e)
        Nothing -> returnS ()
    addVar l scope (VIden n) (fmap (fmap typed) val) isConst isAnn (EntryEnv (locpos l) t)

addDeps :: (MonadIO m) => String -> Scope -> Set LocGCstr -> TcM m ()
addDeps msg scope xs = forM_ xs $! \x -> addDep msg scope x

addDep :: (MonadIO m) => String -> Scope -> Loc Position GCstr -> TcM m ()
addDep msg GlobalScope hyp = do
    modify $! \env -> env { globalDeps = Set.insert hyp (globalDeps env) }
    debugTc $! liftIO $! putStrLn $! "added Global dependency " ++ msg ++ " " ++ pprid (gCstrId $! unLoc hyp)
addDep msg LocalScope hyp = do
    modify $! \env -> env { localDeps = Set.insert hyp (localDeps env) }
    debugTc $! liftIO $! putStrLn $! "added Local dependency " ++ msg ++ " " ++ pprid (gCstrId $! unLoc hyp)

tcNoDeps :: (VarsGTcM m) => TcM m a -> TcM m a
tcNoDeps m = do
    env <- State.get
    let g = globalDeps env
    let l = localDeps env
    State.modify $! \env -> env { globalDeps = Set.empty, localDeps = Set.empty }
    x <- m
    State.modify $! \env -> env { globalDeps = g, localDeps = l }
    returnS x

tcAddDeps :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a
tcAddDeps l msg m = do
    (x,ks) <- tcWithCstrs l msg m
    forM_ ks $! addDep (msg++" tcAddDeps") LocalScope
    returnS x
    
tryAddHypothesis :: (ProverK loc m) => loc -> String -> Scope -> (Options -> Bool) -> Set LocGCstr -> HypCstr -> TcM m ()
tryAddHypothesis l msg scope doCheck deps hyp = do
    opts <- askOpts
    when (doCheck opts) $! do
        st <- getCstrState
        iok <- updateHeadTDict l "tryAddHypothesis" $! \d -> newTDictCstr (locpos l) (HypK hyp st) d
        addDep (msg++" tryAddHypothesis") scope $! Loc (locpos l) iok
        addGCstrDependenciesM l True deps (Loc (locpos l) iok) Set.empty

-- | Adds a new kind variable to the environment
newKindVariable :: ProverK loc m => Bool -> Scope -> KindName GIdentifier (Typed loc) -> TcM m ()
newKindVariable isAnn scope (KindName (Typed l t) (VIden n)) = do
    removeFree "newKindVariable" n
    ds <- getKinds
    case Map.lookup (VIden n) ds of
        Just e -> do
            ppn <- pp n
            tcError (locpos l) $! InvalidKindVariableName (ppn) (locpos $! entryLoc e)
        Nothing -> do
            vars <- getVarsPred isAnn scope (\k -> k == KindStarC || k == VArrayC KindStarC)
            case Map.lookup (VIden n) vars of
                Just (_,(_,_,e)) -> do
                    ppn <- pp n
                    tcWarn (locpos l) $! ShadowedVariable (ppn) (locpos $! entryLoc e)
                Nothing -> addVar l scope (VIden n) Nothing False isAnn (EntryEnv (locpos l) t)

-- | Adds a new domain variable to the environment
newDomainVariable :: (ProverK loc m) => Bool -> Scope -> DomainName GIdentifier (Typed loc) -> TcM m ()
newDomainVariable isAnn scope (DomainName (Typed l t) (VIden n)) = do
    removeFree "newDomainVariable" n
    ds <- getDomains
    case Map.lookup (VIden n) ds of
        Just e -> do
            ppn <- pp n
            tcError (locpos l) $! InvalidDomainVariableName (ppn) (locpos $! entryLoc e)
        Nothing -> do
            vars <- getVarsPred isAnn scope (\k -> k == KindC || k == VArrayC KindC)
            case Map.lookup (VIden n) vars of
                Just (_,(_,_,e)) -> do
                    ppn <- pp n
                    tcWarn (locpos l) $! ShadowedVariable (ppn) (locpos $! entryLoc e)
                Nothing -> addVar l scope (VIden n) Nothing False isAnn (EntryEnv (locpos l) t)

-- | Adds a new type variable to the environment
newTypeVariable :: (ProverK loc m) => Bool -> Bool -> Scope -> TypeName GIdentifier (Typed loc) -> TcM m ()
newTypeVariable isAnn isLeak scope (TypeName (Typed l t) (VIden n)) = do
    removeFree "newTypeVariable" n
    ss <- getStructsByName (TIden n) False (const True) isAnn isLeak
    case ss of
        Just (es) -> do
            ppn <- pp n
            tcError (locpos l) $! InvalidTypeVariableName (ppn) (map (locpos . entryLoc) (Map.elems es))
        Nothing -> do
            vars <- getVarsPred isAnn scope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
            case Map.lookup (VIden n) vars of
                Just (_,(_,_,e)) -> do
                    ppn <- pp n
                    tcWarn (locpos l) $! ShadowedVariable (ppn) (locpos $! entryLoc e)
                Nothing -> addVar l scope (VIden n) Nothing False isAnn (EntryEnv (locpos l) t)

-- | Adds a new kind to the environment
newKind :: ProverK loc m => KindName GIdentifier (Typed loc) -> TcM m ()
newKind (KindName (Typed l t) n) = do
    ks <- getKinds
    case Map.lookup n ks of
        Just e -> do
            ppn <- pp n
            tcError (locpos l) $! MultipleDefinedKind (ppn) (locpos $! entryLoc e)
        Nothing -> do
            let e = EntryEnv (locpos l) t
            modifyModuleEnv $! \env -> env { kinds = Map.insert n e (kinds env) } 

-- | Adds a new domain to the environment
newDomain :: ProverK loc m => DomainName GIdentifier (Typed loc) -> TcM m ()
newDomain (DomainName (Typed l t) n) = do
    ds <- getDomains
    case Map.lookup n ds of
        Just e -> do
            ppn <- pp n
            tcError (locpos l) $! MultipleDefinedDomain (ppn) (locpos $! entryLoc e)
        Nothing -> do
            let e = EntryEnv (locpos l) t
            modifyModuleEnv $! \env -> env { domains = Map.insert n e (domains env) }

-- | Checks that a kind exists in scope
checkKind :: ProverK loc m => Bool -> KindName VarIdentifier loc -> TcM m (KindName GIdentifier (Typed loc))
checkKind isAnn (KindName l n) = do
    halt <- getHalt
    ks <- getKinds
    (n,t) <- case Map.lookup (TIden n) ks of
        Just e -> case entryType e of
            KType (Just NonPublicClass) -> returnS (TIden n,KindT $! PrivateK $! TIden n)
            otherwise -> do
                ppn <- pp n
                genTcError (locpos l) False $! text "Unexpected domain" <+> quotes (ppn) <+> text "without kind."
        Nothing -> do
            kvars <- getVarsPred isAnn LocalScope isKind
            n <- checkConst $! VIden n
            case Map.lookup n kvars of
                Just (_,(_,_,e)) -> returnS (n,varNameToType $! VarName (entryType e) n)
                Nothing -> do
                    ppn <- pp n
                    tcError (locpos l) $! halt $! NotDefinedKind (ppn)
    returnS $ KindName (Typed l t) n

-- | Checks if a domain exists in scope, and returnSs its type
-- Searches for both user-defined private domains and domain variables
checkDomain :: ProverK loc m => Bool -> DomainName VarIdentifier loc -> TcM m (DomainName GIdentifier (Typed loc))
checkDomain isAnn (DomainName l n) = do
    halt <- getHalt
    ds <- getDomains
    (n',t) <- case Map.lookup (TIden n) ds of
        Just e -> case entryType e of
            KindT (PrivateK k) -> returnS (TIden n,SecT $! Private (TIden n) k)
            otherwise -> do
                ppn <- pp n
                genTcError (locpos l) False $! text "Unexpected domain" <+> quotes (ppn) <+> text "without kind."
        Nothing -> do
            dvars <- getVarsPred isAnn LocalScope isDomain
            n <- checkConst $! VIden n
            case Map.lookup n dvars of
                Just (_,(_,_,e)) -> returnS (n,varNameToType $! VarName (entryType e) n)
                Nothing -> do
                    ppn <- pp n
                    tcError (locpos l) $! halt $! NotDefinedDomain (ppn)
    returnS $ DomainName (Typed l t) n'

checkStruct :: ProverK loc m => loc -> Bool -> (DecTypeK -> Bool) -> Bool -> Bool -> SIdentifier -> ModuleTyVarId -> TcM m DecType
checkStruct l withBody decK isAnn isLeak sid mid = do
    pp1 <- pp sid
    pp2 <- pp mid
    debugTc $! liftIO $! putStrLn $! show $! text "checkStruct:" <+> pp1 <+> pp2
    halt <- getHalt
    ss <- getStructsByName sid withBody decK isAnn isLeak
    case ss of
        Just es -> case Map.lookup mid es of
            Just e -> typeToDecType l (entryType e)
            Nothing -> do
                --ppk <- liftM vcat $! mapM (\(k,v) -> do { x <- pp k; y <- pp v; returnS $ x <+> text "->" <+> y }) $! Map.toList ss
                tcError (locpos l) $! halt $! NotDefinedType (pp1 <+> pp2)
        Nothing -> do
            --ppk <- liftM vcat $! mapM (\(k,v) -> do { x <- pp k; y <- pp v; returnS $ x <+> text "->" <+> y }) $! Map.toList ss
            tcError (locpos l) $! halt $! NotDefinedType (pp1 <+> pp2)
        
-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: (ProverK loc m) => (DecTypeK -> Bool) -> Bool -> Bool -> TypeName VarIdentifier loc -> TcM m [EntryEnv]
checkType decK isAnn isLeak (TypeName l n) = do
    halt <- getHalt
    ss <- getStructsByName (TIden n) False decK isAnn isLeak
    case ss of
        Just (es) -> returnS (Map.elems es)
        Nothing -> do
            ppn <- pp n
            --ppk <- liftM vcat $! mapM (\(k,v) -> do { x <- pp k; y <- pp v; returnS $ x <+> text "->" <+> y }) $! Map.toList ss
            tcError (locpos l) $! halt $! NotDefinedType (ppn)

checkTypeVariable :: (ProverK loc m) => Bool -> TypeName VarIdentifier loc -> TcM m (Maybe (TypeName GIdentifier (Typed loc)))
checkTypeVariable isAnn (TypeName l n) = do
    vars <- getVarsPred isAnn LocalScope isType
    n <- checkConst $! VIden n
    case Map.lookup n vars of
        Just (_,(_,_,e)) -> do
            let t = varNameToType (VarName (entryType e) n)
            returnS $ Just $! TypeName (Typed l t) n
        Nothing -> returnS Nothing

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkTypeName :: (ProverK loc m) => Bool -> TypeName VarIdentifier loc -> TcM m (TypeName GIdentifier (Typed loc))
checkTypeName isAnn tn@(TypeName l n) = do
    mb <- checkTypeVariable isAnn tn
    case mb of
        Just tn' -> returnS tn'
        Nothing -> do
            dec <- newDecVar False Nothing
            topTcCstrM_ l $! TDec False Nothing (TIden n) [] dec
            let ret = BaseT $! TApp (TIden n) [] dec
            returnS $ TypeName (Typed l ret) (TIden n)

--checkNonTemplateType :: (ProverK loc m) => Bool -> Bool -> TypeName VarIdentifier loc -> TcM m [EntryEnv]
--checkNonTemplateType isAnn isLeak ty@(TypeName l n) = do
--    es <- checkType isAnn isLeak ty
--    case es of
--        [e] -> case entryType e of
--            DecT d -> case d of
--                (DecType _ _ [] _ _ _ _ _ (StructType {})) -> returnS [e]
--                otherwise -> do
--                    ppn <- pp n
--                    tcError (locpos l) $! NoNonTemplateType (ppn)
--            t -> do
--                ppn <- pp n
--                tcError (locpos l) $! NoNonTemplateType (ppn)
--        es -> do
--            ppn <- pp n
--            tcError (locpos l) $! NoNonTemplateType (ppn)
--
---- | Checks if a template type exists in scope
---- Returns all template type declarations in scope, base template first
--checkTemplateType :: (ProverK loc m) => Bool -> Bool -> TypeName VarIdentifier loc -> TcM m [EntryEnv]
--checkTemplateType isAnn isLeak ty@(TypeName _ n) = do
--    es <- checkType isAnn isLeak ty
--    let check e = unless (isStructTemplate $! entryType e) $! do
--        ppn <- pp n
--        ppe <- pp (entryType e)
--        tcError (locpos $! loc ty) $! NoTemplateType (ppn) (locpos $! entryLoc e) ppe
--    mapM_ check es
--    returnS (es)

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: (ProverK loc m) => (DecTypeK -> Bool) -> Bool -> Bool -> TemplateArgName VarIdentifier loc -> TcM m (TemplateArgName GIdentifier (Typed loc))
checkTemplateArg decK isAnn isLeak (TemplateArgName l n) = do
    ss <- getStructsByName (TIden n) False decK isAnn isLeak
    ds <- getDomains
    vs <- liftM (envVariables isAnn) State.get
    vn <- checkConst $! VIden n
    case (ss,Map.lookup (TIden n) ds,Map.lookup vn vs) of
        (Just (es),Nothing,Nothing) -> case ( Map.elems es) of
            [e] -> if (isStructTemplate $! entryType e)
                then do
                    ppn <- pp n
                    tcError (locpos l) $! NoNonTemplateType (ppn)
                else returnS $ TemplateArgName (Typed l $! entryType e) (TIden n)
            es -> do
                ppn <- pp n
                tcError (locpos l) $! NoNonTemplateType (ppn)
        (Nothing,Just e,Nothing) -> case entryType e of
            KindT (PrivateK k) -> returnS $ TemplateArgName (Typed l $! SecT $! Private (TIden n) k) (TIden n)
            otherwise -> do
                ppn <- pp n
                genTcError (locpos l) False $! text "Unexpected domain" <+> quotes (ppn) <+> text "without kind."
        (Nothing,Nothing,Just (isGlobal,(b,b2,e))) -> do
            registerVar isGlobal False vn (entryType e)
            returnS $ TemplateArgName (Typed l $! varNameToType $! VarName (entryType e) vn) vn
        (mb1,mb2,mb3) -> do
            ppn <- pp n
            tcError (locpos l) $! AmbiguousName (ppn) $! map (locpos . entryLoc) $! maybe [] (\(es) -> Map.elems es) (mb1) ++ maybeToList (mb2) ++ maybeToList (fmap (thr3 . snd) mb3)

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: (ProverK loc m) => Op GIdentifier (Typed loc) -> [(Constrained Var,IsVariadic)] -> DecCtx -> DecCtx -> Deps -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))
addTemplateOperator recop vars hctx bctx hdeps op = do
    let o = funit op
    let (Typed l (DecT recdt)) = loc recop
    let Typed l (IDecT d) = loc op
    let selector = case iDecTyKind d of
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
    let did = fromJustNote "newOperator" (decTypeId recdt)
    let i = snd did
    let o = funit op
    solve l "addTemplateOperator"
    (hctx',bctx',(vars',d')) <- splitTpltHead l hctx bctx hdeps vars d
    d'' <- writeIDecVars l d'
    let dt' = DecT $! dropDecRecs $! DecType i (DecTypeOri False) vars' hctx' bctx' [] d''
    let e = EntryEnv (locpos l) dt'
    debugTc $! do
        pp1 <- ppr (entryType e)
        pph <- ppr hctx
        ppb <- ppr bctx
        liftIO $! putStrLn $! "addTemplateOp " ++ pp1 ++ " " ++ pph ++ " " ++ ppb
    modifyModuleEnv $! \env -> putLns selector env $! Map.alter (Just . Map.insert i e . maybe Map.empty id) (OIden o) $! getLns selector env
    returnS $ updLoc op (Typed (unTyped $! loc op) dt')

addOperatorToRec :: ProverK loc m => [(Constrained Var,IsVariadic)] -> Deps -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))
addOperatorToRec vars hdeps op = do
    let (Typed l (IDecT d)) = loc op
    let selector = case iDecTyKind d of
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
    let o = funit op
    (_,recdict) <- tcProve l "newOp head" $! addHeadTFlatCstrs l "newOp head" hdeps
    addHeadTDict l "newOp" recdict
    i <- newModuleTyVarId
    (hfrees,bfrees) <- splitHeadFrees l hdeps
    d' <- substFromTSubstsNoDec "newOp head" l (tSubsts recdict) False Map.empty d
    let recdt = DecT $! DecType i (DecTypeOri True) vars (implicitDecCtx { dCtxFrees = hfrees }) implicitDecCtx [] $! remIDecBody d'
    rece <- localTemplate l $! EntryEnv (locpos l) recdt
    modifyModuleEnv $! \env -> putLns selector env $! Map.alter (Just . Map.insert i rece . maybe Map.empty id) (OIden o) $! getLns selector env
    dirtyGDependencies (locpos l) $! OIden o
    returnS $ updLoc op $! Typed l recdt

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (ProverK loc m) => Op GIdentifier (Typed loc) -> DecCtx -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))
newOperator recop bctx op = do
    let o = funit op
    let (Typed l (DecT recdt@(DecType _ _ vars _ _ _ _))) = loc recop
    let (Typed _ (IDecT innerdect)) = loc op
    let selector = case iDecTyKind (innerDec recdt) of
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
    let did = fromJustNote "newOperator" (decTypeId recdt)
    let i = snd did
    bctx' <- addLineage did $! newDecCtx l "newOperator" bctx True
    dict <- liftM (headNe . tDict) State.get
    d'' <- tryRunSimplify simplifyInnerDecType =<< substFromTSubsts "newOp body" dontStop l (tSubsts dict) True Map.empty =<< writeIDecVars l innerdect
    let td = DecT $! dropDecRecs $! DecType i (DecTypeOri False) vars implicitDecCtx bctx' [] d''
    let e = EntryEnv (locpos l) td
--    noNormalFreesM e
    debugTc $! do
        ppe <- ppr (entryType e)
        liftIO $! putStrLn $! "addOp " ++ ppe
    modifyModuleEnv $! \env -> putLns selector env $! Map.alter (Just . Map.insert i e . maybe Map.empty id) (OIden o) $! getLns selector env
    returnS $ updLoc op (Typed (unTyped $! loc op) td)
  
isOpCastIden (OIden op) = isOpCast op
isOpCastIden n = Nothing
  
 -- | Checks that an operator exists.
checkOperator :: (ProverK loc m) => (DecTypeK -> Bool) -> Bool -> Bool -> DecKind -> Op GIdentifier loc -> TcM m [EntryEnv]
checkOperator decK isAnn isLeak k op@(OpCast l t) = do
    addGIdDependencies $! OIden $! funit op
    ps <- getEntriesByPred l (isJust . isOpCastIden) decK isAnn isLeak k
    -- select all cast declarations
    let casts = concatMap Map.elems ps
    returnS casts
checkOperator decK isAnn isLeak k op = do
    let cop = funit op
    addGIdDependencies $! OIden cop
    ps <- getEntriesByName (loc op) (OIden cop) decK isAnn isLeak k
    case ps of
        Nothing -> do
            pp1 <- pp op
            halt <- getHalt
            tcError (locpos $! loc op) $! halt $! NotDefinedOperator $! pp1
        Just es -> returnS $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedureFunction :: (ProverK loc m) => ProcedureName GIdentifier (Typed loc) -> [(Constrained Var,IsVariadic)] -> DecCtx -> DecCtx -> Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc))
addTemplateProcedureFunction recpn vars hctx bctx hdeps pn@(ProcedureName (Typed l (IDecT d)) n) = do
    let (Typed _ (DecT recdt)) = loc recpn
    let selector = case iDecTyKind d of
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
    let did = fromJustNote "addTemplateProcedure" (decTypeId recdt)
    let i = snd did
                    
--    liftIO $! putStrLn $! "entering addTemplateProc " ++ ppr pn
    solve l "addTemplateProcedure"
--    unresolvedQVars l "addTemplateProcedureFunction" vars
    (hctx',bctx',(vars',d')) <- splitTpltHead l hctx bctx hdeps vars d
    d'' <- writeIDecVars l d'
    let dt' = DecT $! dropDecRecs $! DecType i (DecTypeOri False) vars' hctx' bctx' [] d''
    let e = EntryEnv (locpos l) dt'
    debugTc $! do
        ppe <- ppr (entryType e)
        liftIO $! putStrLn $! "addTemplateProc " ++ ppe
    modifyModuleEnv $! \env -> putLns selector env $! Map.alter (Just . Map.insert i e . maybe Map.empty id) n $! getLns selector env
    returnS $ ProcedureName (Typed l dt') n

addFrees :: MonadIO m => String -> Frees -> TcM m ()
addFrees msg frees = forM_ (Map.toList frees) $! \(v,isVariadic) -> addFree msg v isVariadic

delFrees :: MonadIO m => String -> Frees -> TcM m ()
delFrees msg delfrees = forM_ (Map.toList delfrees) $! \(v,_) -> removeFree msg v

newDecCtx :: ProverK loc m => loc -> String -> DecCtx -> Bool -> TcM m DecCtx
newDecCtx l msg (DecCtx Nothing dict frees) doTop = do
    addHeadTDict l ("newDecCtx False"++msg) =<< fromPureTDict dict
    addFrees ("newDecCtx False"++msg) frees
    opts <- askOpts
    let doSolve = doTop || implicitContext opts == InferCtx
    if doSolve
        then solveTop l ("newDecCtx False"++msg)
        else solve l ("newDecCtx False"++msg)
    dict' <- liftM (headNe . tDict) State.get
    frees' <- getFrees l
    solved <- getSolved
    let ks = toPureCstrs (tCstrs dict') solved
    let recs = if doSolve then mempty else (tRec dict')
    when doSolve $ checkFrees l frees' ks dict'
    returnS $ DecCtx Nothing (PureTDict ks emptyTSubsts recs) frees'
newDecCtx l msg (DecCtx (Just recs) dict frees) doTop = do
    solveTop l ("newDecCtx True"++msg)
    d' <- liftM (headNe . tDict) State.get
    let d'' = substRecs recs d'
    frees' <- getFrees l
    checkFrees l frees' (pureCstrs dict) d''
    updateHeadTDict l ("newDecCtx True"++msg) $! const $! returnS $ ((),d'')
    returnS $ DecCtx (Just recs) dict frees

substRecs :: Data a => Map ModuleTyVarId VarIdentifier -> a -> a
substRecs recs = everywhere (mkT aux)
    where
    aux :: DecType -> DecType
    aux d = case decTypeTyVarId d of
        Just did -> case Map.lookup did recs of
            Just d' -> DVar d'
            Nothing -> d
        Nothing -> d

addTCstrGraphToRec :: ProverK loc m => loc -> TCstrGraph -> TcM m (Map ModuleTyVarId VarIdentifier)
addTCstrGraphToRec l g = do
    i <- newModuleTyVarId
    foldr (aux i) (returnS Map.empty) (map (unLoc . snd) $! Graph.labNodes g)
  where
    aux i k m = do
        xs <- addTCstrToRec l i k
        liftM (Map.union xs) m

addTCstrToRec :: ProverK loc m => loc -> ModuleTyVarId -> TCstr -> TcM m (Map ModuleTyVarId VarIdentifier)
addTCstrToRec l i (TcK k st) = addTcCstrToRec l i k st
addTCstrToRec l i k = do
    ppk <- pp k
    genTcError (locpos l) False $! text "addTCstrToRec" <+> ppk
    
addTcCstrToRec :: ProverK loc m => loc -> ModuleTyVarId -> TcCstr -> CstrState -> TcM m (Map ModuleTyVarId VarIdentifier)
addTcCstrToRec l i (PDec dk es n ts ps ret (DVar v)) st = do
    j <- newModuleTyVarId
    let (isRead,isWrite) = case cstrExprC st of
                                PureExpr -> (False,False)
                                ReadOnlyExpr -> (True,False)
                                ReadWriteExpr -> (True,True)
    let decclass = DecClass (cstrIsAnn st) True (Map.empty,isRead) (Map.empty,isWrite)
    (ps',substs) <- mapAndUnzipM (addPArgToRec l) ps
    let idec = case cstrDecK st of
                        PKind -> ProcType (locpos l) n ps' ret [] Nothing decclass
                        LKind -> LemmaType (cstrIsLeak st) (locpos l) n ps' [] Nothing decclass
                        FKind -> FunType (cstrIsLeak st) (locpos l) n ps' ret [] Nothing decclass
    let hctx = implicitDecCtx { dCtxDict = emptyPureTDict { pureSubsts = mconcat substs }}
    let dec = DecType j DecTypeCtx [] hctx implicitDecCtx (concat ts) idec
    env <- mkDecEnv l dec
    addHeadTDict l "addTcCstrToRec" $! TDict Graph.empty Set.empty emptyTSubsts env Map.empty
    returnS $ Map.singleton j v
addTcCstrToRec l i (TDec dk es n ts (DVar v)) st = do
    j <- newModuleTyVarId
    let (isRead,isWrite) = case cstrExprC st of
                                PureExpr -> (False,False)
                                ReadOnlyExpr -> (True,False)
                                ReadWriteExpr -> (True,True)
    let decclass = DecClass (cstrIsAnn st) True (Map.empty,isRead) (Map.empty,isWrite)
    let idec = StructType (locpos l) n Nothing decclass
    let dec = DecType j DecTypeCtx [] implicitDecCtx implicitDecCtx ts idec
    env <- mkDecEnv l dec
    addHeadTDict l "addTcCstrToRec" $! TDict Graph.empty Set.empty emptyTSubsts env Map.empty
    returnS $ Map.singleton j v
addTcCstrToRec l i k st = do
    ppk <- pp k
    genTcError (locpos l) False $! text "addTcCstrToRec" <+> ppk

addPArgToRec :: ProverK loc m => loc -> (IsConst,Either Expr Type,IsVariadic) -> TcM m ((IsConst,Var,IsVariadic),TSubsts)
addPArgToRec l (isConst,Right t,isVariadic) = do
    v0 <- freshVarId "parg" Nothing
    let v = v0 { varIdWrite = False }
    returnS ((isConst,VarName t $! VIden v,isVariadic),mempty)
addPArgToRec l (isConst,Left e,isVariadic) = do
    let t = loc e
    v0 <- freshVarId "cparg" Nothing
    let v = v0 { varIdWrite = False }
    let dict = if isConst then TSubsts (Map.singleton v (IdxT e)) else mempty
    returnS ((isConst,VarName t $! VIden v,isVariadic),dict)

addProcedureFunctionToRec :: ProverK loc m => [(Constrained Var,IsVariadic)] -> Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc))
addProcedureFunctionToRec vars hdeps pn@(ProcedureName (Typed l (IDecT d)) n) = do
    let selector = case iDecTyKind d of
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
                    LKind -> Lns lemmas (\x v -> x { lemmas = v })
    -- prove the head constraints first
    (_,recdict) <- tcProve l "newProc head" $! addHeadTFlatCstrs l "newProc head" hdeps
    addHeadTDict l "newProcedureFunction" recdict
    i <- newModuleTyVarId
    (hfrees,bfrees) <- splitHeadFrees l hdeps
    d' <- substFromTSubstsNoDec "newProc head" l (tSubsts recdict) False Map.empty d
    let recdt = DecT $! DecType i (DecTypeOri True) vars (implicitDecCtx { dCtxFrees = hfrees }) implicitDecCtx [] $! remIDecBody d'
    rece <- localTemplate l $! EntryEnv (locpos l) recdt
    modifyModuleEnv $! \env -> putLns selector env $! Map.alter (Just . Map.insert i rece . maybe Map.empty id) n $! getLns selector env
    dirtyGDependencies (locpos l) n
    debugTc $! do
        ppe <- ppr (entryType rece)
        ppd <- ppr recdict
        liftIO $! putStrLn $! "addProc rec" ++ pprid (decTypeTyVarId $! unDecT $! recdt) ++ " " ++ ppe ++ "\n" ++ ppd
    returnS $ ProcedureName (Typed l recdt) n

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedureFunction :: (ProverK loc m) => ProcedureName GIdentifier (Typed loc) -> DecCtx -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc))
newProcedureFunction recpn bctx pn@(ProcedureName (Typed l (IDecT innerdect)) n) = do
    let (Typed _ (DecT recdt@(DecType _ _ vars _ _ _ _))) = loc recpn
    let selector = case iDecTyKind (innerDec recdt) of
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
                    LKind -> Lns lemmas (\x v -> x { lemmas = v })
    let did = fromJustNote "newProcedureFunction" (decTypeId recdt)
    let i = snd did
    bctx' <- addLineage did $! newDecCtx l "newProcedureFunction" bctx True
    dict <- liftM (headNe . tDict) State.get
    
    wvars <- tpltVars vars
    let chg = writeVars wvars
    vars' <- chgVarId chg vars
    
    d'' <- tryRunSimplify simplifyInnerDecType =<< substFromTSubsts "newProc body" dontStop l (tSubsts dict) True Map.empty =<< writeIDecVars l innerdect
    let dt = dropDecRecs $! DecType i (DecTypeOri False) vars' implicitDecCtx bctx' [] d''
    let e = EntryEnv (locpos l) (DecT dt)
    debugTc $! do
        ppe <- ppr (entryType e)
        ppd <- ppr dict
        liftIO $! putStrLn $! "addProc " ++ pprid (decTypeTyVarId dt) ++ " " ++ ppe ++ "\n" ++ ppd
    modifyModuleEnv $! \env -> putLns selector env $! Map.alter (Just . Map.insert i e . maybe Map.empty id) n $! getLns selector env
    returnS $ ProcedureName (Typed l $! DecT dt) n

dropDecRecs :: DecType -> DecType
dropDecRecs (DecType i k ts hctx bctx vs b) = substRecs recs $! DecType i k ts hctx' bctx' vs b
    where
    hctx' = dropCtxRecs hctx
    bctx' = dropCtxRecs bctx
    recs = maybe Map.empty id (dCtxExplicit hctx) `Map.union` maybe Map.empty id (dCtxExplicit bctx)

dropCtxRecs :: DecCtx -> DecCtx
dropCtxRecs ctx = ctx { dCtxExplicit = fmap (const Map.empty) (dCtxExplicit ctx), dCtxDict = dropPureTDictRecs $! dCtxDict ctx }
dropPureTDictRecs :: PureTDict -> PureTDict
dropPureTDictRecs d = d { pureRec = mempty }

writeIDecVars :: ProverK loc m => loc -> InnerDecType -> TcM m InnerDecType
writeIDecVars l idec = do
    let args = iDecArgs idec
    vs <- liftM Set.unions $! mapM writeIDecVar args
    debugTc $! do
        ppvs <- ppr vs
        liftIO $! putStrLn $! "writeIDecVars " ++ ppvs
    let chg = writeVars vs
    idec' <- chgVarId chg idec
    returnS idec'
  where
    writeIDecVar :: ProverK Position m => (Bool,Var,IsVariadic) -> TcM m (Set VarIdentifier)
    writeIDecVar (isConst,v@(VarName _ (VIden vn)),isVariadic) = do
        vs <- usedVs' (loc v)
        if isConst || isVariadic then returnS (Set.insert vn vs) else returnS vs

newAxiom :: ProverK loc m => loc -> [(Constrained Var,IsVariadic)] -> Deps -> InnerDecType -> TcM m DecType
newAxiom l tvars hdeps d = do
    -- prove the head constraints first
    (_,recdict) <- tcProve l "newAxiom head" $! addHeadTFlatCstrs l "newAxiom head" hdeps
    addHeadTDict l "newAxiom" recdict
    i <- newModuleTyVarId
    frees <- getFrees l
    d' <- substFromTSubstsNoDec "newAxiom head" l (tSubsts recdict) False Map.empty d
    
    doc <- liftM (tCstrs . headNe . tDict) State.get >>= ppConstraints
    bctx' <- newDecCtx l "newAxiom" explicitDecCtx True
--    unresolvedQVars l "newAxiom" tvars
    dict <- liftM (headNe . tDict) State.get
    d'' <- tryRunSimplify simplifyInnerDecType =<< substFromTSubsts "newAxiom body" dontStop l (tSubsts dict) True Map.empty =<< writeIDecVars l d'
    let dt = dropDecRecs $! DecType i (DecTypeOri False) tvars implicitDecCtx bctx' [] d''
    let e = EntryEnv (locpos l) (DecT dt)
    debugTc $! do
        ppe <- ppr (entryType e)
        liftIO $! putStrLn $! "addAxiom " ++ pprid (decTypeTyVarId dt) ++ " " ++ ppe
    modifyModuleEnv $! \env -> env { axioms = Map.insert i e (axioms env) }
    returnS dt

--newLemma :: (ProverK loc m) => [(Constrained Var,IsVariadic)] -> Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc))
--newLemma vars hdeps pn@(ProcedureName (Typed l (IDecT d)) n) = do
----    liftIO $! putStrLn $! "entering newLemma " ++ ppr pn
--    solve l "addLemma"
----    unresolvedQVars l "newLemma" vars
--    (hctx',bctx',(vars',d')) <- splitTpltHead l hctx bctx hdeps vars d
--    i <- newModuleTyVarId
--    d'' <- writeIDecVars l d'
--    let dt' = DecT $! dropDecRecs $! DecType i (DecTypeOri False) vars' hctx' bctx' [] d''
--    let e = EntryEnv (locpos l) dt'
--    debugTc $! do
--        ppe <- ppr (entryType e)
--        liftIO $! putStrLn $! "newLemma " ++ ppe
--    modifyModuleEnv $! \env -> env { lemmas = Map.alter (Just . Map.insert i e . maybe Map.empty id) n $! lemmas env }
--    returnS $ ProcedureName (Typed l dt') n
    
 -- | Checks that a procedure exists.
checkProcedureFunctionLemma :: (ProverK loc m) => (DecTypeK -> Bool) -> Bool -> Bool -> DecKind -> ProcedureName GIdentifier loc -> TcM m [EntryEnv]
checkProcedureFunctionLemma decK isAnn isLeak k pn@(ProcedureName l n) = do
    addGIdDependencies n
    ps <- getEntriesByName l n decK isAnn isLeak k
    case ps of
        Nothing -> do
            pp1 <- pp isAnn
            pp2 <- pp isLeak
            pp3 <- pp k
            pp4 <- pp n
            halt <- getHalt
            tcError (locpos l) $! halt $! NotDefinedProcedure (pp1 <+> pp2 <+> pp3 <+> pp4)
        Just es -> returnS $ Map.elems es

getEntriesByName :: (ProverK loc m) => loc -> GIdentifier -> (DecTypeK -> Bool) -> Bool -> Bool -> DecKind -> TcM m (Maybe (Map ModuleTyVarId EntryEnv))
getEntriesByName l n onlyRecs isAnn isLeak k = do
    let aux = Map.filterWithKey (\k v -> k == n)
    liftM (Map.lookup n) $! getEntries l aux onlyRecs isAnn isLeak k
    
getEntriesByPred :: (ProverK loc m) => loc -> (GIdentifier -> Bool) -> (DecTypeK -> Bool) -> Bool -> Bool -> DecKind -> TcM m [Map ModuleTyVarId EntryEnv]
getEntriesByPred l p onlyRecs isAnn isLeak k = do
    let aux = Map.filterWithKey (\k v -> p k)
    liftM (Map.elems) $! getEntries l aux onlyRecs isAnn isLeak k

getEntries :: (ProverK loc m) => loc -> (Map GIdentifier (Map ModuleTyVarId EntryEnv) -> Map GIdentifier (Map ModuleTyVarId EntryEnv)) -> (DecTypeK -> Bool) -> Bool -> Bool -> DecKind -> TcM m (Map POId (Map ModuleTyVarId EntryEnv))
getEntries l filterf onlyRecs isAnn isLeak (FKind) = getFunctions filterf False onlyRecs isAnn isLeak
getEntries l filterf onlyRecs isAnn isLeak (TKind) = getFunctions filterf False onlyRecs isAnn isLeak
getEntries l filterf onlyRecs isAnn isLeak (AKind) = getFunctions filterf False onlyRecs isAnn isLeak
getEntries l filterf onlyRecs isAnn isLeak (LKind) = do
    xs <- getFunctions filterf False onlyRecs isAnn isLeak
    ys <- getLemmas filterf False onlyRecs isAnn isLeak 
    zs <- getProcedures (filterOnlyAnns . filterf) False onlyRecs True isLeak
    returnS $ Map.unionWith Map.union xs (Map.unionWith Map.union ys zs)
getEntries l filterf onlyRecs isAnn isLeak (PKind) = do
    xs <- getFunctions filterf False onlyRecs isAnn isLeak
    ys <- getLemmas filterf False onlyRecs isAnn isLeak 
    zs <- getProcedures (if isAnn then filterOnlyAnns else id . filterf) False onlyRecs True isLeak
    returnS $ Map.unionWith Map.union xs (Map.unionWith Map.union ys zs)
--getEntries l isAnn isLeak k = genTcError (locpos l) $! text "getEntries:" <+> text (show k)

filterOnlyAnns :: Map x (Map y EntryEnv) -> Map x (Map y EntryEnv)
filterOnlyAnns = Map.map filterOnlyAnns1
    where
    filterOnlyAnns1 :: (Map y EntryEnv) -> (Map y EntryEnv)
    filterOnlyAnns1 = Map.filter (\e -> isAnnDecClass $! decDecClass $! unDecT $! entryType e)

chgDecClassM :: Monad m => (DecClass -> DecClass) -> TcM m ()
chgDecClassM fcl = State.modify $! \env -> env { decClass = fcl $! decClass env }

entryLens :: (GIdentifier,ModuleTyVarId) -> DecKind -> Lns TcEnv [Maybe (Map ModuleTyVarId EntryEnv)]
entryLens (dn,i) k = Lns get put
    where
    get env = case (dn,k) of
        (tn,TKind) ->
            let (x,y) = moduleEnv env
                zs = fmap tRec $! tDict env
            in  map (Map.lookup tn . structs) (x:y:Foldable.toList zs)
        (pn,PKind) ->
            let (x,y) = moduleEnv env
                zs = fmap tRec $! tDict env
            in  map (Map.lookup pn . procedures) (x:y:Foldable.toList zs)
        (pn,FKind) ->
            let (x,y) = moduleEnv env
                zs = fmap tRec $! tDict env
            in  map (Map.lookup pn . functions) (x:y:Foldable.toList zs)
        (pn,LKind) ->
            let (x,y) = moduleEnv env
                zs = fmap tRec $! tDict env
            in  map (Map.lookup pn . lemmas) (x:y:Foldable.toList zs)
    put env (x':y':zs') | length zs' == length (Foldable.toList $! tDict env) = case (dn,k) of
        (tn,TKind) ->
            let (x,y) = moduleEnv env
                upd a' a = a { structs = Map.alter (const a') tn $! structs a }
            in  env { moduleEnv = (upd x' x,upd y' y), tDict = mapDict upd zs' $! tDict env }
        (pn,PKind) ->
            let (x,y) = moduleEnv env
                upd a' a = a { procedures = Map.alter (const a') pn $! procedures a }
            in  env { moduleEnv = (upd x' x,upd y' y), tDict = mapDict upd zs' $! tDict env }
        (pn,FKind) ->
            let (x,y) = moduleEnv env
                upd a' a = a { functions = Map.alter (const a') pn $! functions a }
            in  env { moduleEnv = (upd x' x,upd y' y), tDict = mapDict upd zs' $! tDict env }
        (pn,LKind) ->
            let (x,y) = moduleEnv env
                upd a' a = a { lemmas = Map.alter (const a') pn $! lemmas a }
            in  env { moduleEnv = (upd x' x,upd y' y), tDict = mapDict upd zs' $! tDict env }
    put env xs' = error "unsupported view in entryLens"
    mapDict upd zs' d = fromListNe $! map (\(z',d) -> d { tRec = upd z' $! tRec d }) $! zip zs' (Foldable.toList d)

findListLens :: (a -> Bool) -> Lns [Maybe a] (Maybe (a,Int))
findListLens p = Lns (get 0) put
    where
    get i [] = Nothing
    get i (Nothing:xs) = get (succ i) xs
    get i (Just x:xs) = if p x then Just (x,i) else get (succ i) xs
    put xs Nothing = xs
    put (Just x:xs) (Just (x',0)) = Just x' : xs
    put (x:xs) (Just (x',i)) = x : put xs (Just (x',pred i))
    put xs v = error $! "findListLens unsupported view"

indexLens :: Int -> Lns [a] a
indexLens i = Lns (get i) (put i)
    where
    get 0 (x:xs) = x
    get i (x:xs) = get (pred i) xs
    get i xs = error "get indexLens"
    put 0 (x:xs) x' = x':xs
    put i (x:xs) x' = x : put (pred i) xs x'
    put i xs x' = error "put indexLens"

withoutEntry :: Monad m => EntryEnv -> TcM m a -> TcM m a
withoutEntry e m = do
    let DecT d = entryType e
    let k = (decTyKind d)
    env <- State.get
    case decTypeId d of
        Just did@(dn,i) -> do
            let lns = entryLens did k `compLns` findListLens (Map.member i)
            case getLns lns env of
                Nothing -> m
                Just (es,trace) -> do
                    case Map.lookup i es of
                        Just e -> do
                            let lns2 = entryLens did k `compLns` indexLens trace
                            State.modify $! \env -> putLns lns env $! Just (Map.delete i es,trace)
                            a <- m
                            State.modify $! \env -> putLns lns2 env $! Just $! Map.insert i e $! fromJustNote "withoutEntry" $! getLns lns2 env
                            returnS a
                        Nothing -> m
        Nothing -> m

decIsOriginal :: DecType -> Bool
decIsOriginal (DecType _ (DecTypeOri _) _ _ _ _ _) = True
decIsOriginal _ = False

decIsInst :: DecType -> Bool
decIsInst (DecType _ (DecTypeInst {}) _ _ _ _ _) = True
decIsInst _ = False

mkDecEnv :: (MonadIO m,Location loc) => loc -> DecType -> TcM m ModuleTcEnv
mkDecEnv l d@(DecType i _ ts hd bd specs p@(ProcType pl n pargs pret panns body cl)) = do
    let e = EntryEnv (locpos l) (DecT d)
    returnS $ mempty { procedures = Map.singleton (funit n) $! Map.singleton i e }
mkDecEnv l d@(DecType i _ ts hd bd specs p@(FunType isLeak pl n pargs pret panns body cl)) = do
    let e = EntryEnv (locpos l) (DecT d)
    returnS $ mempty { functions = Map.singleton (funit n) $! Map.singleton i e }
mkDecEnv l d@(DecType i _ ts hd bd specs s@(StructType sl sid atts cl)) = do
    let e = EntryEnv (locpos l) (DecT d)
    returnS $ mempty { structs = Map.singleton sid $! Map.singleton i e }
mkDecEnv l d@(DecType i _ ts hd bd specs a@(AxiomType isLeak pa pargs panns cl)) = do
    let e = EntryEnv (locpos l) (DecT d)
    returnS $ mempty { axioms = Map.singleton i e }
mkDecEnv l d@(DecType i _ ts hd bd specs p@(LemmaType isLeak pl pn pargs panns body cl)) = do
    let e = EntryEnv (locpos l) (DecT d)
    returnS $ mempty { lemmas = Map.singleton (funit pn) $! Map.singleton i e }
    
topCstrs :: ProverK loc m => loc -> TcM m (Set LocGCstr)
topCstrs l = do
    cs <- liftM (flattenGCstrGraphSet . tCstrs . headNe . tDict) State.get
    opens <- dependentCstrs l []
    returnS $ cs `Set.difference` opens
    
dependentCstrs :: ProverK loc m => loc -> [Int] -> TcM m (Set LocGCstr)
dependentCstrs l kids = do
    opens <- getOpensSet
    gr <- getCstrs
    returnS $ Set.fromList $! map (fromJustNote "dependentCstrs" . Graph.lab gr) $! reachablesGr (kids++Set.toList opens) gr

getDropFromTail :: Monad m=> TcM m Bool
#if INCREMENTAL
getDropFromTail = State.gets (not . solveToCache)
#else
getDropFromTail = returnS True
#endif

buildCstrGraph :: (ProverK loc m) => loc -> Set Int -> TcM m GCstrGraph
buildCstrGraph l cstrs = do
    dropFromTail <- getDropFromTail
    tops <- topCstrs l
    let tops' = mapSet (gCstrId . unLoc) tops
    let cstrs' = Set.union tops' cstrs
    --liftIO $! putStrLn $! "buildCstrGraph: " ++ show (sepBy space (map (pp) $! Set.toList cstrs))
    d <- concatTDict l (SubstMode NoCheckS False) =<< liftM tDict State.get
    let gr = tCstrs d
    let tgr = Graph.trc gr 
    let gr' = Graph.nfilter (\n -> any (\h -> Graph.hasEdge tgr (n,h)) cstrs') tgr
    let ns = nodes gr'
    -- filter out undesired constraints
    let remHeadCstrs d = if dropFromTail then d { tCstrs = Graph.nfilter (\x -> not $! elem x ns) (Graph.trc $! tCstrs d) } else d
    State.modify $! \env -> env { tDict = let (d:ds) = Foldable.toList (tDict env) in fromListNe (d { tCstrs = gr' } : map remHeadCstrs ds) }
--    mgr <- State.gets (foldr unionGr Graph.empty . map tCstrs . tail . tDict)
--    doc <- ppConstraints mgr
--    liftIO $! putStrLn $! "buildCstrGraphTail: " ++ show doc
    returnS gr'
    
noNormalFrees :: Frees -> Bool
noNormalFrees = Map.null . Map.filter (\b -> not b)
    
-- no non-variadic free variable can be unbound
noNormalFreesM :: ProverK Position m => EntryEnv -> TcM m ()
noNormalFreesM e = do
    opts <- askOpts
    when (debugCheck opts) $! do
        frees <- liftM (Map.keysSet . Map.filter (\b -> not b) . localFrees) State.get
        TSubsts ss <- getTSubsts (loc e)
        let vs = Set.difference frees (Map.keysSet ss)
        unless (Set.null vs) $! do
            ppvs <- pp vs
            ppe <- pp e
            genTcError (loc e) False $! text "variables" <+> ppvs <+> text "should not be free in" $+$ ppe
        
splitHeadFrees :: (ProverK loc m) => loc -> Set LocGCstr -> TcM m (Frees,Frees)
splitHeadFrees l deps = do
    frees <- getFrees l
    hvs <- usedVs $! Set.map (kCstr . unLoc) deps
    let hfrees = Map.intersection frees (Map.fromSet (const False) hvs)
    let bfrees = Map.difference frees hfrees
    returnS (hfrees,bfrees)
    
mapToFun :: Eq a => Map a a -> (a -> a)
mapToFun xs = Map.foldrWithKey (\k v f -> \x -> if k==x then v else f x) id xs
    
writeVars :: Set VarIdentifier -> (VarIdentifier -> VarIdentifier)
writeVars xs = Set.foldr (\v f -> \x -> if v==x then v{varIdRead=True,varIdWrite=True} else f x) id xs
    
tpltVars :: ProverK Position m => [(Constrained Var,IsVariadic)] -> TcM m (Set VarIdentifier)
tpltVars [] = returnS Set.empty
tpltVars ((unConstrained -> v@(VarName t (VIden n)),_):xs) = do
    vs <- usedVs' t
    vs' <- tpltVars xs
    returnS $ Set.insert n (Set.union vs vs')
    
splitTpltHead :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> DecCtx -> DecCtx -> Set LocGCstr -> [(Constrained Var,IsVariadic)] -> a -> TcM m (DecCtx,DecCtx,([(Constrained Var,IsVariadic)],a))
splitTpltHead l hctx bctx deps vars dec = do
    d <- liftM (headNe . tDict) State.get
    let cstrs = tCstrs d
    
    frees <- getFrees l
    debugTc $! do
        ppfs <- ppr frees
        liftIO $! putStrLn $! "splitTpltHeadFrees " ++ ppfs
    hvs <- usedVs $! Set.map (kCstr . unLoc) deps
    let hfrees = Map.intersection frees (Map.fromSet (const False) hvs)
    let bfrees = Map.difference frees hfrees
    opens <- getOpensSet
    let cs = Set.difference (mapSet (gCstrId . unLoc) deps) opens
    let gr = Graph.trc cstrs
    let hgr = Graph.nfilter (\n -> any (\h -> Graph.hasEdge gr (n,h)) cs) gr
    let bgr = differenceGr gr hgr
--    liftIO $! putStrLn $! "splitHead " ++ ppr hgr ++ "\n|\n" ++ ppr bgr
    let headDict = TDict hgr Set.empty emptyTSubsts (tRec d) (tSolved d)
    let bodyDict = TDict bgr Set.empty emptyTSubsts mempty Map.empty
    hctx' <- tcNew (locpos l) "split head" $! onFrees l $! do
        addHeadTDict l "split head" headDict
        addFrees "splitTpltHead" hfrees
        newDecCtx l "split head" hctx False
    bctx' <- tcNew (locpos l) "split body" $! onFrees l $! do
        addHeadTDict l "split body" bodyDict
        addFrees "splitTpltBody" bfrees
        newDecCtx l "split body" bctx False
    
    hbsubsts <- getTSubsts l
    wvars <- tpltVars vars
    let chg = writeVars wvars
    debugTc $! do
        pps <- ppr wvars
        wvars' <- chgVarId chg (mapSet VIden wvars :: Set GIdentifier)
        pps' <- ppr wvars'
        liftIO $! putStrLn $! "writeTpltVars: " ++ pps ++ " --> " ++ pps'
        ppss <- pp hbsubsts
        liftIO $! putStrLn $! "splitSubsts: " ++ show ppss
    vars' <- substFromTSubsts "splitHead" dontStop l hbsubsts False Map.empty vars >>= chgVarId chg
    dec' <- substFromTSubsts "splitHead" dontStop l hbsubsts False Map.empty dec >>= chgVarId chg
    hctx'' <- substFromTSubsts "splitHead" dontStop l hbsubsts False Map.empty hctx' >>= chgVarId chg
    bctx'' <- substFromTSubsts "splitHead" dontStop l hbsubsts False Map.empty bctx' >>= chgVarId chg
        
    returnS (hctx'',bctx'',(vars',dec'))
    
checkFrees :: (Vars GIdentifier (TcM m) x,ProverK loc m,PP (TcM m) d) => loc -> Frees -> x -> d -> TcM m ()
checkFrees l frees x dict = do
    opts <- askOpts
    when (debugCheck opts) $ do
        freevars <- usedVs' x
        forM_ (Map.keys $! Map.filter (\b -> not b) $! frees) $! \v -> unless (Set.member v freevars) $! do
            ppv <- pp v
            ppd <- pp dict
            genTcError (locpos l) False $! text "free variable" <+> ppv <+> text "not dependent on a constraint from" <+> ppd
        
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (ProverK loc m) => TypeName GIdentifier (Typed loc) -> [(Constrained Var,IsVariadic)] -> DecCtx -> DecCtx -> Deps -> TypeName GIdentifier (Typed loc) -> TcM m (TypeName GIdentifier (Typed loc))
addTemplateStruct rectn vars hctx bctx hdeps tn@(TypeName (Typed l (IDecT d)) n) = do
    let (Typed l (DecT recdt)) = loc rectn
    let did = fromJustNote "newStruct" (decTypeId recdt)
    let i = snd did
    
    solve l "addTemplateStruct"
--    unresolvedQVars l "addTemplateStruct" vars
    (hctx',bctx',(vars',d')) <- splitTpltHead l hctx bctx hdeps vars d
    let dt' = DecT $! dropDecRecs $! DecType i (DecTypeOri False) vars' hctx' bctx' [] d'
    let e = EntryEnv (locpos l) dt'
    ss <- getStructsByName n False (const True) (tyIsAnn dt') (isLeakType dt')
    case ss of
        Just es -> do
            ppn <- pp n
            tcError (locpos l) $! MultipleDefinedStructTemplate (ppn) (locpos $! entryLoc $! head $! Map.elems es)
        otherwise -> modifyModuleEnv $! \env -> env { structs = Map.insert n (Map.singleton i e) (structs env) }
    debugTc $! do
        ppe <- ppr (entryType e)
        liftIO $! putStrLn $! "addTemplateStruct " ++ ppe
    returnS $ TypeName (Typed l dt') n
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (ProverK loc m) => TypeName GIdentifier (Typed loc) -> [(Constrained Var,IsVariadic)] -> [(Type,IsVariadic)] -> DecCtx -> DecCtx -> Deps -> TypeName GIdentifier (Typed loc) -> TcM m (TypeName GIdentifier (Typed loc))
addTemplateStructSpecialization rectn vars specials hctx bctx hdeps tn@(TypeName (Typed l (IDecT d)) n) = do
    let (Typed l (DecT recdt)) = loc rectn
    let did = fromJustNote "newStruct" (decTypeId recdt)
    let i = snd did
    
    solve l "addTemplateStructSpecialization"
--    unresolvedQVars l "addTemplateStructSpecialization" vars
    (hctx',bctx',(vars',(specials',d'))) <- splitTpltHead l hctx bctx hdeps vars (specials,d)
    let dt' = DecT $! dropDecRecs $! DecType i (DecTypeOri False) vars' hctx' bctx' specials' d'
    let e = EntryEnv (locpos l) dt'
    modifyModuleEnv $! \env -> env { structs = Map.update (\s -> Just $! Map.insert i e s) n (structs env) }
    returnS $ TypeName (Typed l dt') n

addStructToRec :: ProverK loc m => [(Constrained Var,IsVariadic)] -> Deps -> TypeName GIdentifier (Typed loc) -> TcM m (TypeName GIdentifier (Typed loc))
addStructToRec vars hdeps tn@(TypeName (Typed l (IDecT d)) n) = do
    addGIdDependencies n
    -- solve head constraints
    (_,recdict) <- tcProve l "newStruct head" $! addHeadTFlatCstrs l "newStruct head" hdeps
    addHeadTDict l "newStruct" recdict
    i <- newModuleTyVarId
    -- add a temporary declaration for recursive invocations
    (hfrees,bfrees) <- splitHeadFrees l hdeps
    d' <- substFromTSubstsNoDec "newStruct head" l (tSubsts recdict) False Map.empty d
    let recdt = DecT $! DecType i (DecTypeOri True) vars (implicitDecCtx { dCtxFrees = hfrees }) implicitDecCtx [] $! remIDecBody d'
    let rece = EntryEnv (locpos l) recdt
    ss <- getStructsByName n False (const True) (tyIsAnn recdt) (isLeakType recdt)
    case ss of
        Just es -> do
            ppn <- pp n
            tcError (locpos l) $! MultipleDefinedStruct (ppn) (locpos $! entryLoc $! head $! Map.elems es)
        otherwise -> do
            modifyModuleEnv $! \env -> env { structs = Map.insert n (Map.singleton i rece) (structs env) }
            dirtyGDependencies (locpos l) n
            returnS $ TypeName (Typed l recdt) n

-- | Defines a new struct type
newStruct :: (ProverK loc m) => TypeName GIdentifier (Typed loc) -> DecCtx -> TypeName GIdentifier (Typed loc) -> TcM m (TypeName GIdentifier (Typed loc))
newStruct rectn bctx tn@(TypeName (Typed l (IDecT innerdect)) n) = do
    let (Typed l (DecT recdt)) = loc rectn
    let did = fromJustNote "newStruct" (decTypeId recdt)
    let i = snd did
    -- solve the body
    bctx' <- addLineage did $! newDecCtx l "newStruct" bctx True
    dict <- liftM (headNe . tDict) State.get
    --i <- newModuleTyVarId
    d'' <- tryRunSimplify simplifyInnerDecType =<< substFromTSubsts "newStruct body" dontStop (locpos l) (tSubsts dict) True Map.empty innerdect
    let dt = DecT $! dropDecRecs $! DecType i (DecTypeOri False) [] implicitDecCtx bctx' [] d''
    let e = EntryEnv (locpos l) dt
    debugTc $! do
        ppl <- ppr l
        ppe <- ppr e
        liftIO $! putStrLn $! "newStruct: " ++ ppl ++ " " ++ ppe
    --noNormalFreesM e
    modifyModuleEnv $! \env -> env { structs = Map.insert n (Map.singleton i e) (structs env) }
    returnS $ TypeName (Typed l dt) n

data SubstMode = SubstMode { substCheck :: SubstCheck, substDirty :: Bool }
    deriving (Eq,Data,Typeable,Show)

data SubstCheck = CheckS | NoFailS | NoCheckS
    deriving (Eq,Data,Typeable,Show)

getTSubsts :: (ProverK loc m) => loc -> TcM m TSubsts
getTSubsts l = do
    env <- State.get
    let (x,y) = moduleEnv env
    let xs = Map.foldrWithKey (\(VIden k) (mb,_) m -> maybe m (\e -> Map.insert k (IdxT e) m) mb) Map.empty (globalVars x)
    let ys = Map.foldrWithKey (\(VIden k) (mb,_) m -> maybe m (\e -> Map.insert k (IdxT e) m) mb) Map.empty (globalVars y)
    d <- concatTDict l (SubstMode NoCheckS False) $! tDict env
    returnS $ TSubsts $! unTSubsts (tSubsts d) `Map.union` xs `Map.union` ys

addTpltTok :: ProverK loc m => loc -> Var -> TcM m ()
addTpltTok l v = State.modify $! \env -> env { inTemplate = maybe (Just ([v],False)) (Just . mapFst (v:)) (inTemplate env) }

hasAmbiguousTpltTok :: ProverK loc m => loc -> (Var -> Bool) -> TcM m Bool
hasAmbiguousTpltTok l p = do
    mb <- State.gets inTemplate
    case mb of
        Nothing -> returnS False
        Just (toks,_) -> do
            let toks1 = filter (\x -> p x && isAmbiguous (varNameToType x)) toks
            returnS $ not $! List.null toks1

hasAmbiguousTpltTokClass :: ProverK loc m => loc -> TypeClass -> TcM m Bool
hasAmbiguousTpltTokClass l cl = hasAmbiguousTpltTok l $! \v -> typeClass "swap" (varNameToType v) == cl

hasAmbiguousTpltTokVars :: ProverK loc m => loc -> (TypeClass -> Bool) -> Set VarIdentifier -> TcM m Bool
hasAmbiguousTpltTokVars l pcl vs = hasAmbiguousTpltTok l aux
    where
    aux x = case varNameId x of
        VIden v -> Set.member v vs && pcl (typeClass "ambiguous" $! varNameToType x)
        otherwise -> False

isAmbiguous :: Type -> Bool
isAmbiguous (SecT s) = isAmbiguousSec s
isAmbiguous (KindT k) = isAmbiguousKind k
isAmbiguous (BaseT b) = isAmbiguousBase b
isAmbiguous (IdxT n) = isAmbiguousDim n

isAmbiguousSec :: SecType -> Bool
isAmbiguousSec Public = False
isAmbiguousSec (Private {}) = False
isAmbiguousSec (SVar _ k) = isAmbiguousKind k

isAmbiguousKind :: KindType -> Bool
isAmbiguousKind PublicK = False
isAmbiguousKind (PrivateK _) = False
isAmbiguousKind (KVar _ cl) = isAmbiguousKindClass cl

isAmbiguousKindClass :: Maybe KindClass -> Bool
isAmbiguousKindClass Nothing = True
isAmbiguousKindClass (Just NonPublicClass) = False

isAmbiguousBase :: BaseType -> Bool
isAmbiguousBase b = False

isAmbiguousDim :: Expr -> Bool
isAmbiguousDim n = True

doCheck :: Options -> SubstMode -> SubstCheck
doCheck opts c = case substCheck c of
    CheckS -> CheckS
    otherwise -> if debugCheck opts then substCheck c else NoCheckS

addSubstM :: (ProverK loc m) => loc -> SubstMode -> Var -> Type -> TcM m ()
addSubstM l mode v@(VarName vt (VIden vn)) t = do
    opts <- askOpts
    ppv <- pp v
    addErrorM l (TypecheckerError (locpos l) . GenTcError (text "failed to add substitution" <+> ppv) . Just) $! do
        when (substDirty mode) $! tcCstrM_ l $! Unifies (loc v) (tyOf t)
        t' <- case doCheck opts mode of
            NoCheckS -> returnS t
            otherwise -> do
                substs <- getTSubsts l
                substFromTSubstsNoDec ("addSubst "++show ppv) l substs False Map.empty t
        case doCheck opts mode of
            NoCheckS -> add l (substDirty mode) t'
            otherwise -> do
                vns <- usedVs t'
                if (Set.member vn vns)
                    then do -- add verification condition
                        case doCheck opts mode of
                            NoFailS -> do
                                ppv <- pp v
                                ppvns <- pp vns
                                ppt' <- pp t'
                                genTcError (locpos l) False $! text "failed to add recursive substitution" <+> ppv <+> text "=" <+> ppt' <+> text "with" <+> ppvns
                            CheckS -> do
                                let tv = (varNameToType v)
                                pptv <- pp tv
                                ppt' <- pp t'
                                addErrorM l (TypecheckerError (locpos l) . (UnificationException ("substitution with type")) (pptv) (ppt') . Just) $! tcCstrM_ l $! Equals tv t'
                    else add l (substDirty mode) t'
  where
    add :: ProverK loc m => loc -> Bool -> Type -> TcM m ()
    add l dirty t' = do -- add substitution
        debugTc $! do
            ppv <- ppr v
            ppt' <- ppr t'
            liftIO $! putStrLn $! "addSubstM " ++ ppv ++ " = " ++ ppt'
        replaceSubstM l True vn t'
        removeFree "addSubstM" vn
        when dirty $! dirtyGDependencies (locpos l) $! VIden vn
        -- register variable assignment in the top-most open constraint
        State.modify $! \env -> env { openedCstrs = mapHead (mapSnd $! Set.insert vn) (openedCstrs env) }

replaceSubstM :: ProverK loc m => loc -> Bool -> VarIdentifier -> Type -> TcM m ()
replaceSubstM l True v t = addHeadTDict l "addSubstM" $! emptyTDict { tSubsts = TSubsts $! Map.singleton v t }
replaceSubstM l False v t = updateHeadTDict l "addSubstM" $! \d -> returnS ((),d { tSubsts = TSubsts $! Map.insert v t (unTSubsts $! tSubsts d) })

newDomainTyVar :: (MonadIO m) => String -> KindType -> IsVariadic -> Maybe Doc -> TcM m SecType
newDomainTyVar str k isVariadic doc = do
    n <- freeVarId "newDomainTyVar" str isVariadic doc
    returnS $ SVar n k

newKindVar :: (MonadIO m) => String -> Maybe KindClass -> IsVariadic -> Maybe Doc -> TcM m KindType
newKindVar str isPrivate isVariadic doc = do
    n <- freeVarId "newKindVar" str isVariadic doc
    returnS $ KVar n isPrivate

newDimVar :: (MonadIO m) => IsVariadic -> Maybe Doc -> TcM m Expr
newDimVar isVariadic doc = do
    n <- liftM VIden $! freeVarId "newDimVar" "dim" isVariadic doc
    let v = VarName (BaseT index) n
    returnS (RVariablePExpr (BaseT index) v)

newTypedVar :: (MonadIO m) => String -> a -> IsVariadic -> Maybe Doc -> TcM m (VarName GIdentifier a)
newTypedVar s t isVariadic doc = liftM (VarName t) $! liftM VIden $! freeVarId "newTypedVar" s isVariadic doc

newVarOf :: (MonadIO m) => String -> Type -> IsVariadic -> Maybe Doc -> TcM m Type
newVarOf str (TType b) isVariadic doc = newTyVar b isVariadic doc
newVarOf str (BType c) isVariadic doc = liftM BaseT $! newBaseTyVar c isVariadic doc
newVarOf str (KindT k) isVariadic doc = liftM SecT $! newDomainTyVar str k isVariadic doc
newVarOf str t isVariadic doc | typeClass "newVarOf" t == TypeC = liftM (IdxT . varExpr) $! newTypedVar str t isVariadic doc
newVarOf str (VAType b sz) isVariadic doc = liftM VArrayT $! newArrayVar b sz isVariadic doc

newArrayVar :: (MonadIO m) => Type -> Expr -> IsVariadic -> Maybe Doc -> TcM m VArrayType
newArrayVar b sz isVariadic doc = do
    n <- freeVarId "newArrayVar" "varr" isVariadic doc
    returnS $ VAVar n b sz

newTyVar :: (MonadIO m) => Bool -> IsVariadic -> Maybe Doc -> TcM m Type
newTyVar isNotVoid isVariadic doc = do
    n <- freeVarId "newTyVar" "t" isVariadic doc
    returnS $ ComplexT $! CVar n isNotVoid

newDecVar :: (MonadIO m) => IsVariadic -> Maybe Doc -> TcM m DecType
newDecVar isVariadic doc = do
    n <- freeVarId "newDecVar" "dec" isVariadic doc
    returnS $ DVar n
    
newBaseTyVar :: (MonadIO m) => Maybe DataClass -> IsVariadic -> Maybe Doc -> TcM m BaseType
newBaseTyVar c isVariadic doc = do
    n <- freeVarId "newBaseTyVar" "b" isVariadic doc
    returnS $ BVar n c

newIdxVar :: (MonadIO m) => IsVariadic -> Maybe Doc -> TcM m Var
newIdxVar isVariadic doc = do
    n <- liftM VIden $! freeVarId "newIdxVar" "idx" isVariadic doc
    let v = VarName (BaseT index) n
    returnS v
    
newSizeVar :: (MonadIO m) => IsVariadic -> Maybe Doc -> TcM m Expr
newSizeVar isVariadic doc = do
    n <- liftM VIden $! freeVarId "newSizeVar" "sz" isVariadic doc
    let v = VarName (BaseT index) n
    returnS (RVariablePExpr (BaseT index) v)

--newSizesVar :: (MonadIO m) => Expr -> Maybe Doc -> TcM m [(Expr,IsVariadic)]
--newSizesVar dim doc = do
--    n <- freeVarId "szs" doc
--    let t = VAType (BaseT index) dim
--    let v = VarName t n
--    returnS [(RVariablePExpr t v,True)]
    
mkVariadicTyArray :: (MonadIO m) => IsVariadic -> Bool -> Type -> TcM m Type
mkVariadicTyArray False isTok t = returnS t
mkVariadicTyArray True isTok t = do
    sz <- if isTok then sizeToken else newSizeVar True Nothing
    returnS $ VAType t sz

addValueM :: ProverK loc m => loc -> SubstMode -> Var -> Expr -> TcM m ()
addValueM l mode v e = addSubstM l mode v (IdxT e)

openCstr :: (MonadIO m,Location loc) => loc -> GCstr -> TcM m ()
openCstr l o = do
    opts <- TcM $! lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $! ConstraintStackSizeExceeded $! ppid (constraintStackSize opts) <+> text "opened constraints"
        else State.modify $! \e -> e { openedCstrs = (o,Set.empty) : openedCstrs e }

closeCstr :: (MonadIO m) => TcM m ()
closeCstr = do
    State.modify $! \e -> e { openedCstrs = tail (openedCstrs e) }

#if INCREMENTAL 
addCstrCache :: (ProverK loc m) => loc -> CstrCache -> TcM m ()
addCstrCache l delays = do
    solve <- State.gets solveToCache
    if solve
        then State.modify $! \e -> e { cstrCache = Map.union (cstrCache e) delays }
        else liftIO $! forM_ (Map.toList delays) $! \(Loc l iok,st) -> writeIdRef (kStatus iok) st
#endif


getSolved :: ProverK Position m => TcM m (Map LocGCstr Bool)
getSolved = State.gets (mconcat . Foldable.toList . fmap tSolved . tDict)

resolveGCstr_ :: ProverK loc m => loc -> GCstr -> (TCstr -> GCstrGraph -> Maybe (Context LocGCstr ()) -> TcM m ShowOrdDyn) -> TcM m ()
resolveGCstr_ l iok resolve = do
    solved <- getSolved
    if (isJust $! Map.lookup (Loc (locpos l) iok) solved)
        then removeCstr l iok
        else resolveGCstr l iok resolve >> returnS ()
  where
    resolveGCstr :: ProverK loc m => loc -> GCstr -> (TCstr -> GCstrGraph -> Maybe (Context LocGCstr ()) -> TcM m ShowOrdDyn) -> TcM m ShowOrdDyn
    resolveGCstr l iok resolve = do
#if INCREMENTAL
        st <- readCstrStatus (locpos l) iok
        case st of
            Evaluated rest (frees,delfrees) infer x -> do
                removeCstr l iok
                solvedCstr l iok infer
                addHeadTDict l "resolveIOCstr" rest
                addFrees ("resolveIOCstr "++show (gCstrId iok)) frees
                delFrees ("resolveIOCstr "++show (gCstrId iok)) delfrees
                debugTc $! do
                    ppiok <- ppr (gCstrId iok)
                    pprest <- ppr rest
                    liftIO $! putStrLn $! "restored constraint " ++ ppiok ++ "\n" ++ pprest
                returnS x
            Erroneous err -> throwError err
            Unevaluated -> trySolve
#else
        trySolve
#endif
      where
        trySolve = do
            openCstr l iok
            gr <- liftM (tCstrs . headNe . tDict) State.get
            let ctx = contextGr gr (gCstrId iok)
            ((x,rest),frees,delfrees) <- withFrees l $! tcWith (locpos l) "resolveIOCstr" $! resolve (kCstr iok) gr ctx
            removeCstr l iok
            solvedCstr l iok False
            closeCstr
#if INCREMENTAL
            writeCstrStatus (locpos l) iok $! Evaluated rest (frees,delfrees) False x
#else
            writeCstrSol (locpos l) iok x
#endif
            addHeadTDict l "writeTCstrStatus" rest
            addFrees ("resolveIOCstr "++show (gCstrId iok)) frees
            delFrees ("resolveIOCstr "++show (gCstrId iok)) delfrees
            liftIO $! registerGCstrDependencies iok gr ctx
            --liftIO $! putStrLn $! "resolveIOCstr close " ++ ppr (gCstrId iok)
            returnS x

solvedCstr :: ProverK loc m => loc -> GCstr -> Bool -> TcM m ()
solvedCstr l iok infer = updateHeadTDict l "solved" $! \env -> returnS ((),env { tSolved = Map.insertWith (max) (Loc (locpos l) iok) infer (tSolved env) })

removeCstr :: ProverK loc m => loc -> GCstr -> TcM m ()
removeCstr l iok = do
    updateHeadTDict l "remove resolveIOCstr" $! \d -> returnS ((),d { tCstrs = delNode (gCstrId iok) (tCstrs d) })

-- register constraints dependencies from the dictionary into the global state
registerGCstrDependencies :: GCstr -> GCstrGraph -> Maybe (Context LocGCstr ()) -> IO ()
#if INCREMENTAL
registerGCstrDependencies iok gr ctx = do
    case ctx of
        Nothing -> returnS ()
        Just (deps,_,_,_) -> forM_ deps $! \(_,d) -> case lab gr d of
            Nothing -> returnS ()
            Just x -> addGDependency (unLoc x) (Set.singleton iok)
#else
registerGCstrDependencies iok gr ctx = returnS ()
#endif

-- | adds a dependency on the given variable for all the opened constraints
addGIdDependencies :: (MonadIO m) => GIdentifier -> TcM m ()
#if INCREMENTAL
addGIdDependencies v = do
    cstrs <- getOpens
    --liftIO $! putStrLn $! "addGDependencies: " ++ ppr v ++ " " ++ show (sepBy space (map (pp . gCstrId) cstrs))
    addGIdDependency v cstrs
#else
addGIdDependencies v = returnS ()
#endif
    
addGIdDependency :: (MonadIO m) => GIdentifier -> [GCstr] -> TcM m ()
#if INCREMENTAL
addGIdDependency v cstrs = do
    deps <- liftM tDeps $! liftIO $! readIORef globalEnv
    mb <- liftIO $! WeakHash.lookup deps v
    m <- case mb of
        Nothing -> liftIO $! WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps v m (MkWeak $! mkWeakKey m) >> returnS m
        Just m -> returnS m
    liftIO $! forM_ cstrs $! \k -> WeakMap.insertWithMkWeak m (modTyId $! uniqId $! kStatus k) k (MkWeak $! mkWeakKey $! kStatus k)
#else
addGIdDependency v cstrs = returnS ()
#endif

addGDependency :: GCstr -> Set GCstr -> IO ()
#if INCREMENTAL
addGDependency v cstrs = do
    deps <- liftM ioDeps $! readIORef globalEnv
    mb <- WeakHash.lookup deps (modTyId $! uniqId $! kStatus v)
    m <- case mb of
        Nothing -> WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps (modTyId $! uniqId $! kStatus v) m (MkWeak $! mkWeakKey m) >> returnS m
        Just m -> returnS m
    forM_ cstrs $! \k -> WeakMap.insertWithMkWeak m (modTyId $! uniqId $! kStatus k) k (MkWeak $! mkWeakKey $! kStatus k)
#else
addGDependency v cstrs = returnS ()
#endif

-- adds a dependency to the constraint graph
addGCstrDependencies :: TDict -> Set LocGCstr -> LocGCstr -> Set LocGCstr -> TDict
addGCstrDependencies dict from iok to = dict { tCstrs = add $! tCstrs dict }
    where
    add gr = insLabEdges froms $! insLabEdges tos $! tryInsNode (gid iok,iok) gr 
    tos = map (\k -> ((gid iok,iok),(gid k,k),())) $! Set.toList to
    froms = map (\k -> ((gid k,k),(gid iok,iok),())) $! Set.toList from
    gid = gCstrId . unLoc

addGCstrDependenciesM :: (ProverK loc m) => loc -> Bool -> Deps -> LocGCstr -> Deps -> TcM m ()
addGCstrDependenciesM l filterDeps froms iok tos = do
    ns <- getCstrNodes
--    liftIO $! putStrLn $! "addIOCstrDependenciesM " ++ ppr (mapSet (gCstrId . unLoc) froms) ++ " --> " ++ ppr (gCstrId $! unLoc iok) ++ " --> " ++ ppr (mapSet (gCstrId . unLoc) tos)
    let froms' = if filterDeps then Set.filter (flip Set.member ns . gCstrId . unLoc) froms else froms
    let tos' = if filterDeps then Set.filter (flip Set.member ns . gCstrId . unLoc) tos else tos
    updateHeadTDict l "addIOCstrDependenciesM" $! \d -> returnS ((),addGCstrDependencies d froms' iok tos')
    
getCstrNodes :: Monad m => TcM m (Set Int)
getCstrNodes = do
    dicts <- liftM tDict State.get
    returnS $ foldr (\d xs -> Set.fromList (nodes $! tCstrs d) `Set.union` xs) Set.empty dicts

getCstrs :: Monad m => TcM m GCstrGraph
getCstrs = State.gets (foldr unionGr Graph.empty . map tCstrs . Foldable.toList . tDict)

addHeadTDict :: (ProverK loc m) => loc -> String -> TDict -> TcM m ()
addHeadTDict l msg d = updateHeadTDict l (msg ++ " addHeadTDict") $! \x -> liftM ((),) $! appendTDict l (SubstMode NoFailS False) x d

addHeadTDictDirty :: (ProverK loc m) => loc -> String -> TDict -> TcM m ()
addHeadTDictDirty l msg d = updateHeadTDict l (msg ++ " addHeadTDict") $! \x -> liftM ((),) $! appendTDict l (SubstMode NoFailS True) x d

addHeadTCstrs :: (ProverK loc m) => loc -> String -> GCstrGraph -> TcM m ()
addHeadTCstrs l msg ks = addHeadTDict l (msg++" addHeadTFlatCstrs") $! TDict ks Set.empty emptyTSubsts mempty Map.empty

addHeadTFlatCstrs :: (ProverK loc m) => loc -> String -> Set LocGCstr -> TcM m ()
addHeadTFlatCstrs l msg ks = addHeadTDict l (msg++" addHeadTFlatCstrs") $! TDict (Graph.mkGraph nodes []) Set.empty (TSubsts Map.empty) mempty Map.empty
    where nodes = map (\n -> (gCstrId $! unLoc n,n)) $! Set.toList ks

getHyps :: (MonadIO m) => TcM m Deps
getHyps = do
    deps <- getDeps
    returnS $ Set.filter (isHypCstr . kCstr . unLoc) deps

getDeps :: (MonadIO m) => TcM m Deps
getDeps = do
    env <- State.get
    returnS $ globalDeps env `Set.union` localDeps env

tcWithCstrs :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,Set LocGCstr)
tcWithCstrs l msg m = do
    (x,d) <- tcWith (locpos l) msg m
    addHeadTDict l (msg++" tcWithCstrs") d
    returnS (x,flattenGCstrGraphSet $! tCstrs d)

cstrSetToGraph :: Location loc => loc -> Set GCstr -> GCstrGraph
cstrSetToGraph l xs = foldr (\x gr -> insNode (gCstrId x,Loc (locpos l) x) gr) Graph.empty (Set.toList xs)

newTDictCstr :: (MonadIO m,Location loc) => loc -> TCstr -> TDict -> TcM m (GCstr,TDict)
newTDictCstr l c dict = do
    iok <- newGCstr c
    returnS (iok,dict { tCstrs = insNode (gCstrId iok,Loc (locpos l) iok) (tCstrs dict) })

---- | Adds a new template constraint to the environment
newTemplateConstraint :: (ProverK loc m) => loc -> TCstr -> TcM m GCstr
newTemplateConstraint l c = do
    updateHeadTDict l "newTemplateConstraint" (newTDictCstr (locpos l) c)

--erroneousTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> SecrecError -> TcM m IOCstr
--erroneousTemplateConstraint l c err = do
--    updateHeadTDict (insertTDictCstr (locpos l) c $! Erroneous err)

updateHeadTCstrs :: (ProverK loc m) => loc -> String -> (GCstrGraph -> TcM m (a,GCstrGraph)) -> TcM m a
updateHeadTCstrs l msg upd = updateHeadTDict l (msg ++ ":updateHeadTCstrs") $! \d -> do
    (x,gr') <- upd (tCstrs d)
    returnS (x,d { tCstrs = gr' })

updateHeadTDict :: (ProverK loc m) => loc -> String -> (TDict -> TcM m (a,TDict)) -> TcM m a
updateHeadTDict l msg upd = do
    e <- State.get
    (x,d') <- updHeadNeM upd (tDict e)
    let e' = e { tDict = d' }
    State.put e'
    returnS x

-- | forget the result for a constraint when the value of a variable it depends on changes
dirtyGDependencies :: (MonadIO m) => Position -> GIdentifier -> TcM m ()
#if INCREMENTAL
dirtyGDependencies p v = do
    debugTc $! do
        ppv <- ppr v
        liftIO $! putStr $! "dirtyGDependencies " ++ ppv
    opens <- getOpens
    deps <- liftM tDeps $! liftIO $! readIORef globalEnv
    mb <- liftIO $! WeakHash.lookup deps v
    case mb of
        Nothing -> returnS ()
        Just m -> do
            WeakMap.forGenericM_ m $! \(u,x) -> do
                -- dirty other constraint dependencies
                dirtyIOCstrDependencies p opens x
    debugTc $! liftIO $! putStrLn "\n"
#else
dirtyGDependencies p v = returnS ()
#endif

dirtyGCstrDependencies :: MonadIO m => Position -> [GCstr] -> GCstr -> TcM m ()
#if INCREMENTAL
dirtyGCstrDependencies p opens iok = do
    unless (elem iok opens) $! do
        debugTc $! liftIO $! putStr $! " " ++ pprid (gCstrId iok)
        writeCstrStatus p iok Unevaluated
        --writeIdRef (kStatus io) Unevaluated
    deps <- liftIO $! liftM ioDeps $! readIORef globalEnv
    mb <- liftIO $! WeakHash.lookup deps (modTyId $! uniqId $! kStatus iok)
    case mb of
        Nothing -> returnS ()
        Just m -> WeakMap.forGenericM_ m $! \(u,x) -> dirtyIOCstrDependencies p opens x
#else
dirtyGCstrDependencies p opens iok = returnS ()
#endif

-- we need global const variables to distinguish them during typechecking
addConst :: MonadIO m => Scope -> (Bool,Bool) -> IsVariadic -> Identifier -> TcM m GIdentifier
addConst scope (isRead,isWrite) isVariadic vi = do
    let isTok = not isRead && not isWrite
    doc <- pp $! if isTok then vi++"Tok" else vi
    vi' <- freeVarId "addConst" vi isVariadic $! Just doc
    let vi'' = if isTok then tokVar vi' else vi' { varIdRead = isRead, varIdWrite = isWrite }
    case scope of
        LocalScope -> State.modify $! \env -> env { localConsts = Map.insert vi (VIden vi'') $! localConsts env }
        GlobalScope -> modifyModuleEnv $! \env -> env { globalConsts = Map.insert vi (VIden vi'') $! globalConsts env }
    returnS $ VIden vi''

--getPureClass :: Monad m => Bool -> Bool -> TcM m DecClass
--getPureClass isAnn isPure = do
--    env <- State.get
--    let vs = if isPure then Map.empty else Map.map (entryType . thr3) $! globalVariables env
--    returnS $ DecClass isAnn vs vs

globalVariables :: TcEnv -> Map GIdentifier (Bool,Bool,EntryEnv)
globalVariables env = Map.unions [Map.map snd $! globalVars e1,Map.map snd $! globalVars e2]
    where
    (e1,e2) = moduleEnv env

envVariables :: Bool -> TcEnv -> Map GIdentifier (Bool,(Bool,Bool,EntryEnv))
envVariables isAnn env = Map.filter (\(x,(y,z,e)) -> z <= isAnn) $! Map.unions [Map.map (False,) $! localVars env,Map.map ((True,) . snd) $! globalVars e1,Map.map ((True,) . snd) $! globalVars e2]
    where
    (e1,e2) = moduleEnv env

tcWarn :: (Monad m) => Position -> TypecheckerWarn -> TcM m ()
tcWarn pos msg = do
    i <- getModuleCount
    TcM $! lift $! tell $! ScWarns $! Map.singleton i $! Map.singleton pos $! Set.singleton $ DeepSeq.force $ TypecheckerWarning pos msg

errWarn :: (Monad m) => SecrecError -> TcM m ()
errWarn msg = do
    i <- getModuleCount
    TcM $! lift $! tell $! ScWarns $! Map.singleton i $! Map.singleton (loc msg) $! Set.singleton $! DeepSeq.force $ ErrWarn msg

isChoice :: (ProverK loc m) => loc -> Unique -> TcM m Bool
isChoice l x = do
    d <- concatTDict l (SubstMode NoCheckS False) =<< liftM tDict State.get
    returnS $ Set.member (hashUnique x) $! tChoices d

addChoice :: (ProverK loc m) => loc -> Unique -> TcM m ()
addChoice l x = updateHeadTDict l "addChoice" $! \d -> returnS ((),d { tChoices = Set.insert (hashUnique x) $! tChoices d })

bytes :: ComplexType
bytes = CType Public (TyPrim $! DatatypeUint8 ()) (indexExpr 1)

appendTDict :: (ProverK loc m) => loc -> SubstMode -> TDict -> TDict -> TcM m TDict
appendTDict l noFail (TDict u1 c1 ss1 rec1 solved1) (TDict u2 c2 ss2 rec2 solved2) = do
    let u12 = unionGr u1 u2
    (ss12,ks) <- appendTSubsts l noFail ss1 ss2
    u12' <- foldM (\gr k -> insertNewCstr l k gr) u12 ks
    returnS $ TDict u12' (Set.union c1 c2) ss12 (mappend rec1 rec2) (Map.unionWith max solved1 solved2)

unionTSubsts :: ProverK Position m => TSubsts -> TSubsts -> TcM m (TSubsts,[TCstr])
unionTSubsts (TSubsts ss1) (TSubsts ss2) = do
    (ss3,ks) <- foldM aux (ss1,[]) (Map.toList ss2)
    returnS (TSubsts ss3,ks)
  where
    aux :: ProverK Position m => (Map VarIdentifier Type,[TCstr]) -> (VarIdentifier,Type) -> TcM m (Map VarIdentifier Type,[TCstr])
    aux (xs,ks) (v,t) = case Map.lookup v xs of
        Nothing -> returnS (Map.insert v t xs,ks)
        Just t' -> do
            st <- getCstrState
            let k = if t==t' then [] else [TcK (Unifies t t') st]
            returnS (xs,k ++ ks)

appendTSubsts :: (ProverK loc m) => loc -> SubstMode -> TSubsts -> TSubsts -> TcM m (TSubsts,[TCstr])
appendTSubsts l mode@(SubstMode c s) ss1 ss2 = do
    opts <- askOpts
    let c' = doCheck opts mode
    appendTSubsts' l (SubstMode c' s) ss1 ss2
  where
    appendTSubsts' l (SubstMode NoCheckS _) (TSubsts ss1) (TSubsts ss2) = returnS (TSubsts $! Map.union ss1 ss2,[])
    appendTSubsts' l mode ss1 (TSubsts ss2) = foldM (addSubst l mode) (ss1,[]) (Map.toList ss2)
      where
        addSubst :: (ProverK loc m) => loc -> SubstMode -> (TSubsts,[TCstr]) -> (VarIdentifier,Type) -> TcM m (TSubsts,[TCstr])
        addSubst l mode (ss,ks) (v,t) = do
            t' <- substFromTSubstsNoDec ("appendTSubsts "++show (substCheck mode)) l ss False Map.empty t
            vs <- usedVs t'
            if (Set.member v vs)
                then do
                    case substCheck mode of
                        NoFailS -> do
                            ppv <- pp v
                            ppt' <- pp t'
                            genTcError (locpos l) False $! text "failed to add recursive substitution " <+> ppv <+> text "=" <+> ppt'
                        CheckS -> do
                            st <- getCstrState
                            returnS (ss,TcK (Equals (varNameToType $! VarName (tyOf t') $! VIden v) t') st : ks)
                else do
                    when (substDirty mode) $! dirtyGDependencies (locpos l) $! VIden v
                    (ss3,ks3) <- unionTSubsts (TSubsts $! Map.singleton v t') ss
                    returnS (ss3,ks++ks3)

substFromTSubstsNoDec :: (VarsG (TcM m) a,ProverK loc m) => String -> loc -> TSubsts -> Bool -> Map GIdentifier GIdentifier -> a -> TcM m a
substFromTSubstsNoDec msg l ss doBounds ssBounds x = do
    substFromTSubsts msg stopOnDecType l ss doBounds ssBounds x

substFromTSubstsDec :: (ProverK loc m) => String -> loc -> TSubsts -> Bool -> Map GIdentifier GIdentifier -> DecType -> TcM m DecType
substFromTSubstsDec msg l x doBounds ssBounds (DecType i isRec ts hctx bctx specs b) = do
    i' <- substFromTSubstsNoDec msg l x doBounds ssBounds i
    isRec' <- substFromTSubstsNoDec msg l x doBounds ssBounds isRec
    ts' <- substFromTSubstsNoDec msg l x doBounds ssBounds ts
    hctx' <- substFromTSubstsNoDec msg l x doBounds ssBounds hctx
    bctx' <- substFromTSubstsNoDec msg l x doBounds ssBounds bctx
    specs' <- substFromTSubstsNoDec msg l x doBounds ssBounds specs
    b' <- substFromTSubstsNoDec msg l x doBounds ssBounds b
    returnS $ DecType i' isRec' ts' hctx' bctx' specs' b'

substFromTSubsts :: (VarsG (TcM m) a,ProverK loc m) => String -> StopProxy (TcM m) -> loc -> TSubsts -> Bool -> Map GIdentifier GIdentifier -> a -> TcM m a
substFromTSubsts msg stop l tys doBounds ssBounds x = if tys == emptyTSubsts
    then returnS x
    else {-returnSSess Nothing (Just msg) $! -} substProxy msg stop (substsProxyFromTSubsts l tys) doBounds ssBounds x
    
substsProxyFromTSubsts :: ProverK loc m => loc -> TSubsts -> SubstsProxy GIdentifier (TcM m)
substsProxyFromTSubsts (l::loc) (TSubsts tys) = SubstsProxy $ \proxy x -> do
    case x of
        VIden v -> case Map.lookup v tys of
            Nothing -> return Nothing
            Just ty -> case proxy of
                (eq (typeRep :: TypeOf GIdentifier) -> EqT) ->
                    return $ fmap varNameId $ typeToVarName ty
                (eq (typeRep :: TypeOf Var) -> EqT) ->
                    return $ typeToVarName ty
                (eq (typeRep :: TypeOf (SecTypeSpecifier GIdentifier (Typed loc))) -> EqT) ->
                    case ty of
                        SecT s -> liftM Just $ secType2SecTypeSpecifier l s
                        otherwise -> return Nothing
                (eq (typeRep :: TypeOf (TemplateTypeArgument GIdentifier (Typed loc))) -> EqT) ->
                    liftM Just $ type2TemplateTypeArgument l ty
                (eq (typeRep :: TypeOf (TypeSpecifier GIdentifier (Typed loc))) -> EqT) ->
                    type2TypeSpecifier l ty
                (eq (typeRep :: TypeOf (DatatypeSpecifier GIdentifier (Typed loc))) -> EqT) ->
                    case ty of
                        BaseT b -> liftM Just $ baseType2DatatypeSpecifier l b
                        otherwise -> return Nothing
                (eq (typeRep :: TypeOf (VarName GIdentifier (Typed loc))) -> EqT) ->
                    return $ fmap (fmap (Typed l)) $ typeToVarName ty
                (eq (typeRep :: TypeOf (DomainName GIdentifier Type)) -> EqT) ->
                    return $ typeToDomainName ty
                (eq (typeRep :: TypeOf (DomainName GIdentifier ())) -> EqT) ->
                    return $ fmap funit $ typeToDomainName ty
                (eq (typeRep :: TypeOf (DomainName GIdentifier (Typed loc))) -> EqT) ->
                    return $ fmap (fmap (Typed l)) $ typeToDomainName ty
                (eq (typeRep :: TypeOf (KindName GIdentifier Type)) -> EqT) ->
                    return $ typeToKindName ty
                (eq (typeRep :: TypeOf (KindName GIdentifier ())) -> EqT) ->
                    return $ fmap funit $ typeToKindName ty
                (eq (typeRep :: TypeOf (KindName GIdentifier (Typed loc))) -> EqT) ->
                    return $ fmap (fmap (Typed l)) $ typeToKindName ty
                (eq (typeRep :: TypeOf (TypeName GIdentifier Type)) -> EqT) ->
                    return $ typeToTypeName ty
                (eq (typeRep :: TypeOf (TypeName GIdentifier ())) -> EqT) ->
                    return $ fmap funit $ typeToTypeName ty
                (eq (typeRep :: TypeOf (TypeName GIdentifier (Typed loc))) -> EqT) ->
                    return $ fmap (fmap (Typed l)) $ typeToTypeName ty
                (eq (typeRep :: TypeOf SecType) -> EqT) ->
                    case ty of
                        SecT s -> return $ Just s
                        otherwise -> return Nothing
                (eq (typeRep :: TypeOf KindType) -> EqT) ->
                    case ty of
                        KindT s -> return $ Just s
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
                (eq (typeRep :: TypeOf (Expression GIdentifier (Typed loc))) -> EqT) ->
                    case ty of
                        IdxT s -> return $ Just $ fmap (Typed l) s
                        otherwise -> return Nothing
                (eq (typeRep :: TypeOf Type) -> EqT) ->
                    return $ Just ty
                otherwise -> return Nothing
        otherwise -> return Nothing
  where
    eq x proxy = eqTypeOf x (typeOfProxy proxy)

concatTDict :: (ProverK loc m) => loc -> SubstMode -> NeList TDict -> TcM m TDict
concatTDict l noFail = Foldable.foldlM (appendTDict l noFail) emptyTDict

mergeHeadDecCtx :: ProverK loc m => loc -> DecCtx -> DecCtx -> TcM m DecCtx
mergeHeadDecCtx l (DecCtx _ d1 f1) (DecCtx b d2 f2) = do
    d12 <- appendPureTDict l (SubstMode NoCheckS False) d1 d2
    returnS $ DecCtx b d12 (f1 `mappend` f2)

appendPureTDict :: (ProverK loc m) => loc -> SubstMode -> PureTDict -> PureTDict -> TcM m PureTDict
appendPureTDict l noFail (PureTDict u1 ss1 rec1) (PureTDict u2 ss2 rec2) = do
    (ss12,ks) <- appendTSubsts l noFail ss1 ss2
    let u12 = unionGr u1 u2
    u12' <- liftIO $! foldM (\gr k -> insNewNodeIO (Loc (locpos l) k) gr) u12 ks
    returnS $ PureTDict u12' ss12 (mappend rec1 rec2)

insertNewCstr :: (MonadIO m,Location loc) => loc -> TCstr -> GCstrGraph -> TcM m GCstrGraph
insertNewCstr l c gr = do
    iok <- newGCstr c
    returnS $ insNode (gCstrId iok,Loc (locpos l) iok) gr

newGCstr :: MonadIO m => TCstr -> TcM m GCstr
#if INCREMENTAL
newGCstr c = do
    cstrs <- liftM gCstrs $! liftIO $! readIORef globalEnv
    mb <- liftIO $! WeakHash.lookup cstrs c
    case mb of
        Nothing -> do
            mn <- newModuleTyVarId
            liftM (IOCstr c) $! liftIO $! newIdRef mn Unevaluated
        Just (IOCstr _ st) -> returnS $ IOCstr c st
#else
newGCstr c = do
    mn <- newModuleTyVarId
    returnS $ IdCstr c mn
#endif
    
specializeM :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> a -> TcM m a
specializeM l a = do
    ss <- getTSubsts l
    substFromTSubstsNoDec "specialize" l ss False Map.empty a

ppM :: (Vars GIdentifier (TcM m) a,PP (TcM m) a,ProverK loc m) => loc -> a -> TcM m Doc
ppM l a = pp =<< specializeM l a

ppArrayRangesM :: (ProverK loc m) => loc -> [ArrayProj] -> TcM m Doc
ppArrayRangesM l = liftM (sepBy comma) . mapM (ppM l)

tcLocal :: ProverK loc m => loc -> String -> TcM m a -> TcM m a
tcLocal l msg m = do
    env <- State.get
    let dropTest v (_,b) = if b then True else isJust (Map.lookup (VIden v) (localVars env))
    let dropLocals (xs,b) = (Map.filterWithKey dropTest xs,b)
    x <- m
    --debugTc $! do
    --    ppl <- ppr l
    --    DecClass _ _ rs ws <- State.gets decClass
    --    prs <- pp rs
    --    pws <- pp ws
    --    liftIO $! putStrLn $! "tcLocal 1" ++ msg ++ ppl ++ " " ++ show prs ++ " : " ++ show pws
    State.modify $! \e -> e
        { localConsts = localConsts env, localVars = localVars env, localDeps = localDeps env
        , decClass = let DecClass isAnn isInline rs ws = decClass e in DecClass isAnn isInline (dropLocals rs) (dropLocals ws)
        }
    --debugTc $! do
    --    ppl <- ppr l
    --    DecClass _ _ rs ws <- State.gets decClass
    --    prs <- pp rs
    --    pws <- pp ws
    --    liftIO $! putStrLn $! "tcLocal 2" ++ msg ++ ppl ++ " " ++ show prs ++ " : " ++ show pws
    returnS x

tcError :: (MonadIO m) => Position -> TypecheckerErr -> TcM m a
tcError pos msg = throwTcError pos $! TypecheckerError pos msg  

genTcError :: (MonadIO m) => Position -> Bool -> Doc -> TcM m a
genTcError pos doHalt msg = do
    let halt = if doHalt then Halt else id
    throwTcError pos $! TypecheckerError pos $! halt $! GenTcError msg Nothing

throwTcError :: (Location loc,MonadIO m) => loc -> SecrecError -> TcM m a
throwTcError l err = do
    (i,SecrecErrArr f) <- Reader.ask
    let err2 = f err
    ios <- liftM openedCstrs State.get
    debugTc $! liftIO $! putStrLn $! "throwTcError " ++ show (map (pprid . gCstrId . fst) ios)
#if INCREMENTAL
    let add (io,vs) = do
        -- write error to the constraint's result
        writeCstrStatus (locpos l) io (Erroneous err2)
        --liftIO $! writeIdRef (kStatus io) (Erroneous err2)
        -- dirty variables assigned by this constraint
        forM_ vs (dirtyGDependencies (locpos l) . VIden)
    mapM_ add ios
#endif
    throwError $ DeepSeq.force err2     

-- a new dictionary
newDict l msg = do
    opts <- TcM $! lift Reader.ask
    size <- liftM (length . tDict) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $! ConstraintStackSizeExceeded $! ppid (constraintStackSize opts) <+> text "dictionaries"
        else do
            State.modify $! \e -> e { tDict = ConsNe emptyTDict (tDict e) }
--            liftIO $! putStrLn $! "newDict " ++ show msg ++ " " ++ show size

tcWith :: (VarsGTcM m) => Position -> String -> TcM m a -> TcM m (a,TDict)
tcWith l msg m = do
    newDict l $! "tcWith " ++ msg
    x <- m
    d <- liftM (headNe . tDict) State.get
    State.modify $! \e -> e { tDict = dropDict (tDict e) }
    returnS (x,d)
  where
    dropDict (ConsNe x xs) = xs

tcNew :: (VarsGTcM m) => Position -> String -> TcM m a -> TcM m a
tcNew l msg m = do
    (x,d) <- tcWith l msg m
    addHeadTDict l msg d
    returnS x

onlyAnn :: ProverK loc m => loc -> Doc -> TcM m a -> TcM m a
onlyAnn l doc m = do
    isAnn <- getAnn
    unless isAnn $! genTcError (locpos l) False $! text "can only typecheck" <+> doc <+> text "inside annotations"
    x <- m
    returnS x

onlyLeak :: ProverK loc m => loc -> Doc -> TcM m a -> TcM m a
onlyLeak l doc m = do
    isLeak <- getLeak
    unless isLeak $! genTcError (locpos l) False $! text "can only typecheck" <+> doc <+> text "inside a leakage annotation"
    x <- m
    returnS x

--nonTok v = varIdTok v == False
tokVar v = v { varIdRead = False, varIdWrite = False }

getDecClass :: Monad m => TcM m DecClass
getDecClass = State.gets decClass

withDecClassVars :: Monad m => TcM m a -> TcM m (a,DecClassVars,DecClassVars)
withDecClassVars m = do
    DecClass isAnn isInline rs ws <- getDecClass
    State.modify $! \env -> env { decClass = DecClass isAnn isInline (mkEmpty rs) (mkEmpty ws) }
    x <- m
    new <- getDecClass
    State.modify $! \env -> env { decClass = addDecClassVars rs ws new }
    returnS (x,decClassReads new,decClassWrites new)
  where
    mkEmpty xs = (Map.empty,isGlobalDecClassVars xs)

checkLeak :: ProverK loc m => loc -> Bool -> TcM m a -> TcM m (Bool,a)
checkLeak l False m = do
    isLeak <- getLeak
    x <- m
    returnS (isLeak,x)
checkLeak l True m = do
    isLeak <- getLeak
    k <- getKind
    if isLeak
        then liftM (True,) m
        else case k of
            PKind -> liftM (True,) $! withLeak True m
            LKind -> liftM (True,) $! withLeak True m
            otherwise -> do
                ppk <- pp k
                genTcError (locpos l) False $! text "leakage annotation not supported in" <+> ppk

checkLeakMb :: ProverK loc m => loc -> Maybe Bool -> TcM m a -> TcM m (Maybe Bool,a)
checkLeakMb l Nothing m = do
    isLeak <- getLeak
    x <- m
    returnS (lkgBool isLeak,x)
checkLeakMb l (Just isOut) m = do
    isLeak <- getLeak
    k <- getKind
    if isLeak
        then liftM (Just isOut,) m
        else case k of
            PKind -> liftM (Just isOut,) $! withLeak True m
            LKind -> liftM (Just isOut,) $! withLeak True m
            otherwise -> do
                ppk <- pp k
                genTcError (locpos l) False $! text "leakage annotation not supported in" <+> ppk

getOpens :: MonadIO m => TcM m [GCstr]
getOpens = State.gets (map fst . openedCstrs)

getOpensSet :: MonadIO m => TcM m (Set Int)
getOpensSet = do
    opens <- State.gets (map (gCstrId . fst) . openedCstrs)
    returnS (Set.fromList opens)

withCstrState :: (Location loc,MonadIO m) => loc -> CstrState -> TcM m a -> TcM m a
withCstrState l st m =
    withAnn (cstrIsAnn st) $!
        withDef (cstrIsDef st) $!
            withExprC (cstrExprC st) $!
                withLeak (cstrIsLeak st) $!
                    withKind (cstrDecK st) $!
                        withLineage (cstrLineage st) $!
                            addErrorM'' l (cstrErr st) m

withLineage :: MonadIO m => Lineage -> TcM m a -> TcM m a
withLineage new m = do
    old <- State.gets lineage
    State.modify $! \env -> env { lineage = new }
    debugTc $! do
        ppline <- liftM (sepBy colon) . mapM pp =<< getLineage
        liftIO $! putStrLn $! "lineage: " ++ show ppline
    x <- m
    State.modify $! \env -> env { lineage = old }
    returnS x

addLineage :: MonadIO m => (GIdentifier,ModuleTyVarId) -> TcM m a -> TcM m a
addLineage i m = do
    old <- State.gets lineage
    State.modify $! \env -> env { lineage = i:old }
    debugTc $! do
        ppline <- liftM (sepBy colon) . mapM pp =<< getLineage
        liftIO $! putStrLn $! "lineage: " ++ show ppline
    x <- m
    State.modify $! \env -> env { lineage = old }
    returnS x

addErrorM :: (MonadIO m,Location loc) => loc -> (SecrecError -> SecrecError) -> TcM m a -> TcM m a
addErrorM l err m = addErrorM' l (1,err) m

addErrorM' :: (MonadIO m,Location loc) => loc -> (Int,SecrecError -> SecrecError) -> TcM m a -> TcM m a
addErrorM' l (j,err) (TcM m) = do
    size <- liftM fst Reader.ask
    opts <- askOpts
    if (size + j) > constraintStackSize opts
        then tcError (locpos l) $! ConstraintStackSizeExceeded $! ppid (constraintStackSize opts) <+> text "nested errors"
        else TcM $! RWS.withRWST (\(i,SecrecErrArr f) s -> ((i + j,SecrecErrArr $ f . err),s)) m

addErrorM'' :: (MonadIO m,Location loc) => loc -> (Int,SecrecErrArr) -> TcM m a -> TcM m a
addErrorM'' l (j,SecrecErrArr err) m = addErrorM' l (j,err) m

decTypeArgs :: DecType -> [(Constrained Type,IsVariadic)]
decTypeArgs (DecType _ _ args _ _ [] body) =
    -- a base template uses the base arguments
    map (mapFst (fmap varNameToType)) args
decTypeArgs (DecType _ _ args _ _ specials body) =
    -- a specialization uses the specialized arguments
    map (mapFst (flip Constrained Nothing)) specials

chgVarId :: Vars GIdentifier m a => (VarIdentifier -> VarIdentifier) -> a -> m a
chgVarId f x = State.evalStateT (chgVarIdM f x) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)

chgVarIdM :: Vars GIdentifier m a => (VarIdentifier -> VarIdentifier) -> a -> VarsM GIdentifier m a
chgVarIdM f x = do
    mbiden <- State.lift $! substL x
    x' <- case mbiden of -- try to substitute first
        Nothing -> returnS x
        Just (v::GIdentifier) -> do
            v' <- case v of
                VIden vi -> returnS $ VIden $! f vi
                otherwise -> returnS v
            State.lift $! unSubstL x v' 
    traverseVars (chgVarIdM f) x'

class Variable var where
    isReadable :: var -> Bool
    isWritable :: var -> Bool

class Variable var => ToVariable x var | x -> var where
    getVar :: x -> Maybe var
    fromVar :: var -> x
    tryResolve :: ProverK loc m => loc -> var -> TcM m (Maybe x)
    
isTok :: Variable var => var -> Bool
isTok v = not (isReadable v) && not (isWritable v)

tokVars :: Variable var => Set var -> Set var
tokVars = Set.filter isTok

getReadableVar :: ToVariable x var => x -> Maybe var
getReadableVar = maybe Nothing (\v -> if isReadable v then Just v else Nothing) . getVar
getWritableVar :: ToVariable x var => x -> Maybe var
getWritableVar = maybe Nothing (\v -> if isWritable v then Just v else Nothing) . getVar
getNonWritableVar :: ToVariable x var => x -> Maybe var
getNonWritableVar = maybe Nothing (\v -> if isWritable v then Nothing else Just v) . getVar
getTokVar :: ToVariable x var => x -> Maybe var
getTokVar = maybe Nothing (\v -> if isTok v then Just v else Nothing) . getVar

readable2 :: (ToVariable x1 var1,ToVariable x2 var2,ProverK loc m) => (x1 -> x2 -> TcM m b) -> loc -> x1 -> x2 -> TcM m b
readable2 = readable2' True True
    where
    readable2' True r2 go l e1@(getReadableVar -> Just v1) e2 = do
        mb <- tryResolve l v1
        case mb of
            Just e1' -> readable2' True r2 go l e1' e2
            Nothing -> readable2' False r2 go l e1 e2
    readable2' r1 True go l e1 e2@(getReadableVar -> Just v2) = do
        mb <- tryResolve l v2
        case mb of
            Just e2' -> readable2' r1 True go l e1 e2'
            Nothing -> readable2' r1 False go l e1 e2
    readable2' r1 r2 go l e1 e2 = go e1 e2

readable2List :: ProverK Position m => [x -> TcM m (Maybe x)] -> (x -> x -> TcM m b) -> x -> x -> TcM m b
readable2List [] f x y = f x y
readable2List (g:gs) f x y = readable2Generic g g (\x y -> readable2List gs f x y) x y

readable2Generic :: (ProverK Position m) => (x1 -> TcM m (Maybe x1)) -> (x2 -> TcM m (Maybe x2)) -> (x1 -> x2 -> TcM m b) -> x1 -> x2 -> TcM m b
readable2Generic read1 read2 = readable2' True True
    where
    readable2' True r2 go e1 e2 = do
        mb1 <- read1 e1
        case mb1 of
            Just e1' -> readable2' True r2 go e1' e2
            Nothing -> readable2' False r2 go e1 e2
    readable2' r1 True go e1 e2 = do
        mb2 <- read2 e2
        case mb2 of
            Just e2' -> readable2' r1 True go e1 e2'
            Nothing -> readable2' r1 False go e1 e2
    readable2' r1 r2 go e1 e2 = go e1 e2

readable1 :: (ToVariable x var,ProverK loc m) => (x -> TcM m b) -> loc -> x -> TcM m b
readable1 = readable1' True
    where
    readable1' True go l e1@(getReadableVar -> Just v1) = do
        mb <- tryResolve l v1
        case mb of
            Just e1' -> readable1' True go l e1'
            Nothing -> readable1' False go l e1
    readable1' r1 go l e1 = go e1

assignable :: (ToVariable x var,ProverK loc m) => (x -> TcM m b) -> (var -> TcM m b) -> (var -> TcM m b) -> loc -> var -> TcM m b
assignable bound ass go l v = assignable' True l v
    where
    assignable' True l v@(isReadable -> True) = do
        mb <- tryResolve l v
        case mb of
            Nothing -> assignable' False l v
            Just x' -> bound x'
    assignable' r l v@(isWritable -> True) = ass v
    assignable' r l x = go x


instance Variable (VarName VarIdentifier Type) where
    isReadable (VarName _ n) = varIdRead n
    isWritable (VarName _ n) = varIdWrite n

instance ToVariable Expr (VarName VarIdentifier Type) where
    getVar (RVariablePExpr _ (VarName t1 (VIden n1))) = Just $! VarName t1 n1
    getVar _ = Nothing
    fromVar (VarName t1 n1) = RVariablePExpr t1 $! VarName t1 $! VIden n1
    tryResolve l (VarName t1 n1) = liftM (fmap (fmap typed)) $! tryResolveEVar l n1 t1

instance Variable (VarIdentifier) where
    isReadable (v1) = varIdRead v1
    isWritable (v1) = varIdWrite v1

instance Variable (VarIdentifier,b) where
    isReadable (v1,k1) = varIdRead v1
    isWritable (v1,k1) = varIdWrite v1
    
instance Variable (VarIdentifier,b,c) where
    isReadable (v1,_,_) = varIdRead v1
    isWritable (v1,_,_) = varIdWrite v1

instance ToVariable SecType (VarIdentifier,KindType) where
    getVar (SVar v1 k1) = Just (v1,k1)
    getVar s = Nothing
    fromVar (v1,k1) = SVar v1 k1
    tryResolve l (v1,k1) = tryResolveSVar l v1 k1

instance ToVariable ComplexType (VarIdentifier,Bool) where
    getVar (CVar v1 k1) = Just (v1,k1)
    getVar s = Nothing
    fromVar (v1,k1) = CVar v1 k1
    tryResolve l (v1,k1) = tryResolveCVar l v1 k1

instance ToVariable DecType VarIdentifier where
    getVar (DVar v1) = Just v1
    getVar s = Nothing
    fromVar (v1) = DVar v1
    tryResolve l (v1) = tryResolveDVar l v1

instance ToVariable BaseType (VarIdentifier,Maybe DataClass) where
    getVar (BVar v1 k1) = Just (v1,k1)
    getVar s = Nothing
    fromVar (v1,k1) = BVar v1 k1
    tryResolve l (v1,k1) = tryResolveBVar l v1 k1

instance ToVariable KindType (VarIdentifier,Maybe KindClass) where
    getVar (KVar v1 k1) = Just (v1,k1)
    getVar s = Nothing
    fromVar (v1,k1) = KVar v1 k1
    tryResolve l (v1,k1) = tryResolveKVar l v1 k1

instance ToVariable VArrayType (VarIdentifier,Type,Expr) where
    getVar (VAVar v1 b1 sz1) = Just (v1,b1,sz1)
    getVar s = Nothing
    fromVar (v1,b1,sz1) = VAVar v1 b1 sz1
    tryResolve l (v1,b1,sz1) = tryResolveVAVar l v1 b1 sz1

-- | Does a constraint depend on global template, procedure or struct definitions?
-- I.e., can it be overloaded?
isGlobalCstr :: VarsGTcM m => TCstr -> TcM m Bool
isGlobalCstr k = do
    b1 <- everything orM (mkQ (returnS False) isGlobalCheckCstr) k
    b2 <- everything orM (mkQ (returnS False) isGlobalHypCstr) k
    b3 <- everything orM (mkQ (returnS False) isGlobalTcCstr) k
    returnS (b1 || b2 || b3)

isGlobalCheckCstr :: VarsGTcM m => CheckCstr -> TcM m Bool
isGlobalCheckCstr _ = returnS True

isGlobalHypCstr :: VarsGTcM m => HypCstr -> TcM m Bool
isGlobalHypCstr _ = returnS True

isResolveTcCstr :: TcCstr -> Bool
isResolveTcCstr (Resolve {}) = True
isResolveTcCstr _ = False

isGlobalTcCstr :: VarsGTcM m => TcCstr -> TcM m Bool
isGlobalTcCstr (Resolve {}) = returnS True
isGlobalTcCstr (TDec {}) = returnS True
isGlobalTcCstr (PDec {}) = returnS True
isGlobalTcCstr (SupportedPrint {}) = returnS True
isGlobalTcCstr k@(Coerces {}) = isMultipleSubstsTcCstr k
isGlobalTcCstr _ = returnS False

isMultipleSubstsCstr :: VarsGTcM m => TCstr -> TcM m Bool
isMultipleSubstsCstr k = everything orM (mkQ (returnS False) isMultipleSubstsTcCstr) k

isDelayableCstr :: VarsGTcM m => TCstr -> TcM m Bool
isDelayableCstr k = everything orM (mkQ (returnS False) mk) k
    where
    mk x = do
        is1 <- isMultipleSubstsTcCstr x
        returnS (is1 || isResolveTcCstr x)

isMultipleSubstsTcCstr :: VarsGTcM m => TcCstr -> TcM m Bool
--isMultipleSubstsTcCstr (MultipleSubstitutions _ _ [k]) = returnS False
isMultipleSubstsTcCstr (PDec _ es _ _ _ _ _) = do
    returnS $ length es >= 1
isMultipleSubstsTcCstr (TDec _ es _ _ _) = do
    returnS $ length es >= 1
isMultipleSubstsTcCstr (Coerces ts _ _) = do
    xs <- usedVs' ts
    if Set.null xs then returnS False else returnS True
isMultipleSubstsTcCstr _ = returnS False

usedVs' :: (ProverK Position m,Vars GIdentifier (TcM m) x) => x -> TcM m (Set VarIdentifier)
usedVs' x = do
    vs <- usedVs x
    ss <- getTSubsts (noloc::Position)
    vvs <- forM (Set.toList vs) $! \v -> case Map.lookup v (unTSubsts ss) of
        Nothing -> returnS $ Set.singleton v
        Just t -> usedVs' t
    returnS $ Set.unions vvs

writtenVs' :: (ProverK Position m,Vars GIdentifier (TcM m) x) => x -> TcM m (Set VarIdentifier)
writtenVs' x = do
    vs <- writtenVs x
    ss <- getTSubsts (noloc::Position)
    vvs <- forM (Set.toList vs) $! \v -> case Map.lookup v (unTSubsts ss) of
        Nothing -> returnS $ Set.singleton v
        Just t -> usedVs' t
    returnS $ Set.unions vvs

priorityTCstr :: VarsGTcM m => TCstr -> TCstr -> TcM m Ordering
priorityTCstr (TcK c1 _) (TcK c2 _) = priorityTcCstr c1 c2
priorityTCstr (HypK x _) (HypK y _) = returnS $ compare x y
priorityTCstr (CheckK x _) (CheckK y _) = returnS $ compare x y
priorityTCstr (TcK {}) y  = returnS LT
priorityTCstr x (TcK {})  = returnS GT
priorityTCstr (HypK {}) y = returnS LT
priorityTCstr x (HypK {}) = returnS GT

priorityTcCstr :: VarsGTcM m => TcCstr -> TcCstr -> TcM m Ordering
priorityTcCstr k1 k2 = do
    mul1 <- isMultipleSubstsTcCstr k1
    mul2 <- isMultipleSubstsTcCstr k2
    case (mul1,mul2) of
        (True,False) -> returnS GT
        (False,True) -> returnS LT
        (True,True) -> priorityMultipleSubsts k1 k2
        (False,False) -> do
            isGlobal1 <- isGlobalTcCstr k1
            isGlobal2 <- isGlobalTcCstr k2
            case (isGlobal1,isGlobal2) of
                (True,False) -> returnS GT
                (False,True) -> returnS LT
                otherwise -> do
                    let isValid1 = isValidTcCstr k1
                    let isValid2 = isValidTcCstr k2
                    case (isValid1,isValid2) of
                        (True,False) -> returnS GT
                        (False,True) -> returnS LT
                        otherwise -> returnS $ compare k1 k2

isDecTcCstr :: TcCstr -> Maybe (Maybe [EntryEnv])
isDecTcCstr (TDec _ es _ _ _) = Just es
isDecTcCstr (PDec _ es _ _ _ _ _) = Just es
isDecTcCstr _ = Nothing

priorityMultipleSubsts :: ProverK Position m => TcCstr -> TcCstr -> TcM m Ordering
priorityMultipleSubsts c1 c2 = do
    is1 <- isMultipleSubstsTcCstr c1
    is2 <- isMultipleSubstsTcCstr c2
    case (is1,is2) of
        (True,False) -> returnS GT
        (False,True) -> returnS LT
        otherwise -> priorityMultipleSubsts' c1 c2
  where
    priorityMultipleSubsts' (isDecTcCstr -> Just es1) (isDecTcCstr -> Just es2) = returnS $ compare (length es1) (length es2)
    priorityMultipleSubsts' (isDecTcCstr -> Just es1) c2 = returnS LT
    priorityMultipleSubsts' c1 (isDecTcCstr -> Just es2) = returnS GT
    priorityMultipleSubsts' c1@(Coerces vs1 _ _) c2@(Coerces vs2 _ _) = do
        x1 <- usedVs vs1
        x2 <- usedVs vs2
        case compare (Set.size x1) (Set.size x2) of
            LT -> returnS LT
            GT -> returnS GT
            EQ -> returnS $ compare c1 c2

cstrScope :: VarsGTcM m => TCstr -> TcM m SolveScope
cstrScope k = do
    isAll <- isDelayableCstr k
    if isAll
        then returnS SolveAll
        else do
            isGlobal <- isGlobalCstr k
            if isGlobal
                then returnS SolveGlobal
                else returnS SolveLocal

getKinds :: ProverK Position m => TcM m (Map GIdentifier EntryEnv)
getKinds = do
    let aux env = mempty { kinds = kinds env }
    getModuleField True aux kinds
getGlobalVars :: ProverK Position m => TcM m (Map GIdentifier (Maybe Expr,(Bool,Bool,EntryEnv)))
getGlobalVars = do
    let aux env = mempty { globalVars = globalVars env }
    getModuleField True aux globalVars
getGlobalConsts :: ProverK Position m => TcM m (Map Identifier GIdentifier)
getGlobalConsts = do
    let aux env = mempty { globalConsts = globalConsts env }
    getModuleField True aux globalConsts
getDomains :: ProverK Position m => TcM m (Map GIdentifier EntryEnv)
getDomains = do
    let aux env = mempty { domains = domains env }
    getModuleField True aux domains

getStructsByName :: ProverK Position m => SIdentifier -> Bool -> (DecTypeK -> Bool) -> Bool -> Bool -> TcM m (Maybe (Map ModuleTyVarId EntryEnv))
getStructsByName n withBody decK isAnn isLeak = do
    let aux = Map.filterWithKey (\k v -> k == n)
    liftM (Map.lookup n) $! getStructs aux withBody decK isAnn isLeak

getStructs :: ProverK Position m => (Map SIdentifier (Map ModuleTyVarId EntryEnv) -> Map SIdentifier (Map ModuleTyVarId EntryEnv)) -> Bool -> (DecTypeK -> Bool) -> Bool -> Bool -> TcM m (Map GIdentifier (Map ModuleTyVarId EntryEnv))
getStructs filterf withBody decK isAnn isLeak = do
    let filterstructs env = mempty { structs = filterf $! structs env }
    liftM (filterAnns isAnn isLeak decK) $! getModuleField withBody filterstructs structs
getProcedures :: ProverK Position m => (Map POId (Map ModuleTyVarId EntryEnv) -> Map POId (Map ModuleTyVarId EntryEnv)) -> Bool -> (DecTypeK -> Bool) -> Bool -> Bool -> TcM m (Map POId (Map ModuleTyVarId EntryEnv))
getProcedures filterf withBody decK isAnn isLeak = do
    let filterprocs env = mempty { procedures = filterf $! procedures env }
    liftM (filterAnns isAnn isLeak decK) $! getModuleField withBody filterprocs procedures
getFunctions :: ProverK Position m => (Map POId (Map ModuleTyVarId EntryEnv) -> Map POId (Map ModuleTyVarId EntryEnv)) -> Bool -> (DecTypeK -> Bool) -> Bool -> Bool -> TcM m (Map POId (Map ModuleTyVarId EntryEnv))
getFunctions filterf withBody decK isAnn isLeak = do
    let filterfunctions env = mempty { functions = filterf $! functions env }
    liftM (filterAnns isAnn isLeak decK) $! getModuleField withBody filterfunctions functions
getLemmas :: ProverK Position m => (Map GIdentifier (Map ModuleTyVarId EntryEnv) -> Map GIdentifier (Map ModuleTyVarId EntryEnv)) -> Bool -> (DecTypeK -> Bool) -> Bool -> Bool -> TcM m (Map GIdentifier (Map ModuleTyVarId EntryEnv))
getLemmas filterf withBody decK isAnn isLeak = do
    let filterlemmas env = mempty { lemmas = filterf $! lemmas env }
    liftM (filterAnns isAnn isLeak decK) $! getModuleField withBody filterlemmas lemmas
getAxioms :: ProverK Position m => (Map ModuleTyVarId EntryEnv -> Map ModuleTyVarId EntryEnv) -> (DecTypeK -> Bool) -> Bool -> Bool -> TcM m (Map ModuleTyVarId EntryEnv)
getAxioms filterf decK isAnn isLeak = do
    let filteraxioms env = mempty { axioms = filterf $! axioms env }
    liftM (filterAnns1 isAnn isLeak decK) $! getModuleField True filteraxioms axioms    

getEntry :: ProverK Position m => Maybe GIdentifier -> ModuleTyVarId -> DecKind -> Bool -> TcM m (Maybe EntryEnv)
getEntry Nothing tid AKind withBody = do
    let filterf = Map.filterWithKey (\k v -> k == tid)
    let aux env = mempty { axioms = filterf $! axioms env } 
    ss <- getModuleField withBody aux axioms
    returnS $ Map.lookup tid ss
getEntry (Just pn) tid k withBody = do
    
    let selector = case k of
                    TKind -> Lns structs (\x v -> x { structs = v }) 
                    FKind -> Lns functions (\x v -> x { functions = v }) 
                    PKind -> Lns procedures (\x v -> x { procedures = v })
                    LKind -> Lns lemmas (\x v -> x { lemmas = v })
    
    let filterf = Map.filterWithKey (\k v -> k == pn) . Map.map (Map.filterWithKey (\k v -> k == tid))
    let aux env = putLns selector mempty $! filterf $! getLns selector env
    ss <- getModuleField withBody aux (getLns selector)
    case Map.lookup pn ss of
        Nothing -> do
            debugTc $! do
                pptid <- ppr tid
                ppss <- liftM (sepBy space) $! mapM pp $! Map.keys ss
                liftIO $! putStrLn $! "getEntry: cannot find " ++ show pptid ++ " in " ++ show ppss
            returnS Nothing
        Just es -> case Map.lookup tid es of
            Nothing -> do
                debugTc $! do
                    pptid <- ppr tid
                    ppss1 <- liftM (sepBy space) $! mapM pp $! Map.keys es
                    ppss2 <- liftM (sepBy space) $! mapM pp $! concatMap Map.keys $! Map.elems ss
                    liftIO $! putStrLn $! "getEntry: cannot find " ++ show pptid ++ " in " ++ show ppss1 ++ " nor in " ++ show ppss2
                returnS Nothing
            Just e -> returnS $ Just e

getModuleField :: (ProverK Position m) => Bool -> (ModuleTcEnv -> ModuleTcEnv) -> (ModuleTcEnv -> x) -> TcM m x
getModuleField withBody filterf f = do
    (x,y) <- State.gets moduleEnv
    z <- getRecs withBody filterf
    let xyz = mappend (filterf x) (mappend (filterf y) z)
    returnS $ f xyz

-- get only the recursive declarations for the lineage
getRecs :: ProverK Position m => Bool -> (ModuleTcEnv -> ModuleTcEnv) -> TcM m ModuleTcEnv
getRecs withBody filterf = do
    lineage <- getLineage
    debugTc $! do
        ppline <- liftM (sepBy comma) $! mapM pp lineage
        liftIO $! putStrLn $! "getRecs: " ++ show ppline
    State.gets (mconcat . Foldable.toList . fmap (filterf . tRec) . tDict) >>= filterRecModuleTcEnv lineage withBody

filterRecModuleTcEnv :: ProverK Position m => Lineage -> Bool -> ModuleTcEnv -> TcM m ModuleTcEnv
filterRecModuleTcEnv lineage withBody env = do
    structs' <- filterRecBody lineage withBody (structs env)
    procedures' <- filterRecBody lineage withBody (procedures env)
    functions' <- filterRecBody lineage withBody (functions env)
    lemmas' <- filterRecBody lineage withBody (lemmas env)
    returnS $ env { structs = structs', procedures = procedures', functions = functions', lemmas = lemmas' }

filterRecBody :: ProverK Position m => Lineage -> Bool -> Map x (Map ModuleTyVarId EntryEnv) -> TcM m (Map x (Map ModuleTyVarId EntryEnv))
filterRecBody lineage withBody xs = mapM filterLineage xs
    where
    filterLineage = processRecs lineage withBody -- Map.map remDictBody . Map.filter (isLineage lin)
    --isLineage lin (EntryEnv l (DecT d)) = case decTypeId d of
    --    Nothing -> False
    --    Just x -> List.elem x lin

processRecs :: ProverK Position m => Lineage -> Bool -> Map ModuleTyVarId EntryEnv -> TcM m (Map ModuleTyVarId EntryEnv)
processRecs lin withBody = Map.foldrWithKey go (returnS Map.empty)
    where
    remBody = if withBody then id else remEntryBody
    remEntryBody (EntryEnv l (DecT d)) = EntryEnv l $! DecT $! remDecBody d
    remEntryDict (EntryEnv l (DecT d)) = EntryEnv l $! DecT $! remDecDict d
    go k e@(EntryEnv l (DecT d)) mxs = case decTypeId d of
        Nothing -> liftM (Map.insert k e) mxs -- non-specialized decs go unchanged
        Just x -> if List.elem x lin
            then liftM (Map.insert k (remEntryDict $! remBody e)) mxs -- remove body and dictionary of recursive invocations
            else do
                isMono <- isMonomorphicDec d
                if isMono
                    then liftM (Map.insert k e) mxs -- monomorphic invocations go unchanged
                    else mxs -- drop non-lineage non-monomorphic recursive entries

isMonomorphicDec :: (ProverK Position m) => DecType -> TcM m Bool
isMonomorphicDec d@(DecType _ _ targs _ _ specs _) = do
    vs <- liftM (Set.filter (not . isTok)) $! usedVs' (targs,specs)
    debugTc $! do
        ppd <- ppr d
        ppvs <- ppr vs
        liftIO $! putStrLn $! "isMonomorphicDec: " ++ ppvs ++ " " ++ ppd
    returnS $ Set.null vs

isSMTError :: SecrecError -> Bool
isSMTError = Generics.everything (||) (Generics.mkQ False aux)
    where
    aux :: TypecheckerErr -> Bool
    aux (SMTException {}) = True
    aux _ = False

defaultInline :: Monad m => TcM m a -> TcM m a
defaultInline m = do
    k <- State.gets decKind
    let inline = case k of
                    PKind -> False
                    FKind -> True
                    LKind -> False
                    AKind -> False
                    TKind -> False
    withInline inline m

decClassAnn :: DecClass -> Bool
decClassAnn (DecClass isAnn _ _ _) = isAnn

withInline :: Monad m => Bool -> TcM m a -> TcM m a
withInline k m = do
    DecClass isAnn isInline ls rs <- liftM decClass State.get
    State.modify $! \env -> env { decClass = DecClass isAnn k ls rs }
    x <- m
    State.modify $! \env -> env { decClass = let (DecClass isAnn' _ ls' rs') = decClass env in DecClass isAnn' isInline ls' rs' }
    returnS x

chgDecClass :: (DecClass -> DecClass) -> DecType -> DecType
chgDecClass f (DecType x1 x2 x3 x4 x5 x6 cl) = DecType x1 x2 x3 x4 x5 x6 (chgIDecClass f cl)

chgDecClassInline :: Bool -> DecClass -> DecClass
chgDecClassInline b (DecClass isAnn _ ls rs) = DecClass isAnn b ls rs

chgDecInline :: Bool -> DecType -> DecType
chgDecInline b = chgDecClass (chgDecClassInline b)

chgIDecClass :: (DecClass -> DecClass) -> InnerDecType -> InnerDecType
chgIDecClass f d@(ProcType pl n pargs pret panns body cl) = ProcType pl n pargs pret panns body (f cl)
chgIDecClass f d@(FunType isLeak pl n pargs pret panns body cl) = FunType isLeak pl n pargs pret panns body (f cl)
chgIDecClass f d@(StructType sl sid atts cl) = StructType sl sid atts (f cl)
chgIDecClass f d@(AxiomType isLeak p qs pargs cl) = AxiomType isLeak p qs pargs (f cl)
chgIDecClass f d@(LemmaType isLeak pl n pargs panns body cl) = LemmaType isLeak pl n pargs panns body (f cl)

lemmaDecBody :: DecType -> Maybe (Maybe [Statement GIdentifier (Typed Position)])
lemmaDecBody (DecType _ _ _ _ _ _ (LemmaType _ _ _ _ _ b _)) = b
lemmaDecBody t = error $! "lemmaDecBody: " ++ show t

stopOnDecType :: StopProxy m
stopOnDecType = StopProxy $ \proxy x -> case proxy of
    (eq (typeRep :: TypeOf DecType) -> EqT) -> returnS True
    otherwise -> returnS False
  where eq x proxy = eqTypeOf x (typeOfProxy proxy)
  
getOriginalDec :: ProverK loc m => loc -> DecType -> TcM m DecType
getOriginalDec l d@(DecType _ (DecTypeOri _) _ _ _ _ b) = returnS d
getOriginalDec l d@(DecType _ (DecTypeCtx) _ _ _ _ b) = returnS d
getOriginalDec l d@(DecType j (DecTypeInst i _) _ _ _ _ (StructType sl sid _ cl)) = do
    checkStruct l True (const True) (isAnnDecClass cl) (isLeakDec d) sid i
getOriginalDec l d@(DecType j (DecTypeInst i _) _ _ _ _ (FunType _ _ n _ _ _ _ cl)) = do
    es <- case n of
        PIden pn -> checkProcedureFunctionLemma (const True) (isAnnDecClass cl) (isLeakDec d) FKind (ProcedureName l $! PIden pn)
        OIden op -> checkOperator (const True) (isAnnDecClass cl) (isLeakDec d) FKind op
    let mb = List.find (testDec i) es
    case mb of
        Just e -> returnS $ unDecT $! entryType e
        Nothing -> do
            ppd <- pp d
            genTcError (locpos l) False $! text "could not find original function declaration for" <+> ppd
getOriginalDec l d@(DecType j (DecTypeInst i _) _ _ _ _ (ProcType _ n _ _ _ _ cl)) = do
    es <- case n of
        PIden pn -> checkProcedureFunctionLemma (const True) (isAnnDecClass cl) (isLeakDec d) PKind (ProcedureName l $! PIden pn)
        OIden op -> checkOperator (const True) (isAnnDecClass cl) (isLeakDec d) PKind op
    let mb = List.find (testDec i) es
    case mb of
        Just e -> returnS $ unDecT $! entryType e
        Nothing -> do
            ppd <- pp d
            genTcError (locpos l) False $! text "could not find original procedure declaration for" <+> ppd
getOriginalDec l d@(DecType j (DecTypeInst i _) _ _ _ _ (LemmaType _ _ n _ _ _ cl)) = do
    es <- case n of
        PIden pn -> checkProcedureFunctionLemma (const True) (isAnnDecClass cl) (isLeakDec d) LKind (ProcedureName l $! PIden pn)
        OIden op -> checkOperator (const True) (isAnnDecClass cl) (isLeakDec d) LKind op
    let mb = List.find (testDec i) es
    case mb of
        Just e -> returnS $ unDecT $! entryType e
        Nothing -> do
            ppd <- pp d
            genTcError (locpos l) False $! text "could not find original lemma declaration for" <+> ppd

testDec j e = case entryType e of
    DecT d -> isOriginalDecTypeKind (decTypeKind d) && decTypeTyVarId d == Just j

isOriginalDecTypeKind :: DecTypeK -> Bool
isOriginalDecTypeKind (DecTypeOri _) = True
isOriginalDecTypeKind _ = False

tcProgress :: ProverK Position m => Maybe Position -> Maybe String -> TcM m a -> TcM m a
tcProgress l msg m = do
    opts <- askOpts
    (oldmsg,oldp) <- State.gets progressBar
    let newmsg = maybe oldmsg id msg
    let newp = maybe oldp (posLine) l
    
    when (progress opts) $! do
        State.modify $! \env -> env { progressBar = (newmsg,newp) }
    
        sz <- liftM consolesize $! shellyOutput False True "tput" ["cols"]
        let msgsz::Integer = round (realToFrac sz * 0.3 :: Float)
        let barsz::Integer = round (realToFrac sz * 0.7 :: Float)
        
        total <- State.gets (maybe (-1) id . fmap snd . fst . moduleCount)
        liftIO $! Bar.hProgressBar stderr (Bar.msg $! pad msgsz newmsg) lbl barsz (fromIntegral newp) (fromIntegral total)
    x <- m
    
    when (progress opts) $! do
        State.modify $! \env -> env { progressBar = (oldmsg,newp) }

    returnS x
  where
    lbl x y = Bar.exact x y ++ " " ++ Bar.percentage x y
    consolesize :: Status -> Int
    consolesize (Status (Left x)) = maybe 100 id (readMaybe $! filter (not . isSpace) $! show x)
    consolesize (Status (Right err)) = 100
    pad n str = take (fromEnum n) $! str ++ repeat ' '


tcDie :: MonadIO m => Bool -> TcM m a -> TcM m a
tcDie False m = m
tcDie True m = catchError m $! \e -> do
    ppe <- ppr e
    liftIO $! die ppe

--tcBlock :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> TcM m a -> TcM m a
--tcBlock l m = tcGenBlock l "block" False Nothing m

---- | TypeChecks a code block
--tcGenBlock :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> String -> Bool -> Maybe ModuleCount -> TcM m a -> TcM m a
--tcGenBlock l msg doReset count m = tcDie doReset $! returnSSess (Just $! locpos l) (Just msg) $! do
--    olde <- State.get
--    oldge <- liftIO $! if doReset then liftM Just backupGlobalEnv else returnS Nothing
--    oldti <- liftIO $! if doReset then liftM Just backupTyVarId else returnS Nothing
--    when doReset $! State.modify $! \e -> e { cstrCache = Map.empty, openedCstrs = [], decClass = DecClass False False emptyDecClassVars emptyDecClassVars, localConsts = Map.empty, localVars = Map.empty, localFrees = Map.empty, localDeps = Set.empty, tDict = WrapNe emptyTDict, moduleCount = maybe (moduleCount e) id count }
--    debugTc $! do
--        opts <- askOpts
--        liftIO $! putStrLn $! "solving tcGlobal " ++ pprid (locpos l) ++ " " ++ show (implicitCoercions opts)
--    x <- m
--    when doReset $! do
--        solveTop l "tcGlobal"
--        dict <- top . tDict =<< State.get
--        x' <- substFromTSubsts "tcGlobal" dontStop l (tSubsts dict) False Map.empty x
--        returnSSess Nothing (Just "cleanup") $! do
--            liftIO $! resetGlobalEnv False
--            liftIO resetTyVarId
--    State.modify $! \e -> e { cstrCache = cstrCache olde, openedCstrs = openedCstrs olde, decClass = decClass olde, localConsts = localConsts olde, localVars = localVars olde, localFrees = localFrees olde, localDeps = localDeps olde, tDict = tDict olde, moduleCount = moduleCount olde }
--    liftIO $! mapM_ restoreGlobalEnv oldge
--    liftIO $! mapM_ restoreTyVarId oldti
--    returnS x
--  where
--    top (WrapNe x) = returnS x
--    top xs = do
--        ppxs <- mapM pp $! Foldable.toList xs
--        error $! "tcGlobal: " ++ show (vcat ppxs)    


