--TODO: uniqueness of shadow variables

{-# LANGUAGE DoAndIfThenElse, DeriveDataTypeable, ViewPatterns #-}

module Language.Boogie.Transformation.Shadow where

import Language.Boogie.AST
import Language.Boogie.Exts
import Language.Boogie.Position
import Language.Boogie.BasicBlocks
import Language.Boogie.Analysis.BlockGraph
import Language.Boogie.Analysis.Leakage

import Data.Set (Set (..))
import qualified Data.Set as Set
import Data.Map (Map (..))
import qualified Data.Map as Map
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe
import Data.List as List

import Text.PrettyPrint.ANSI.Leijen

import Control.Monad
import Control.Monad.State as State

import Debug.Trace

data ShadowSt = ShadowSt
    { seed :: Int
    , variables :: Set Id -- defined variables
    , exemptions :: Set Id -- variables not to be shadowed
    , typeExemptions :: Type -> Bool -- types not to be shadowed
    , shadowOk :: Maybe Id -- leakage aggregator variable
    , procedures :: Map Id ([Bool],[Bool],Set Id,Leakage) -- mapping from procedure name to (modifies clauses,leakage)
    , functions :: Map Id [Bool] -- mapping from function name to sequence of (shadowed or not) arguments
    }

type ShadowM x = State ShadowSt x

runShadow :: Set Id -> (Type -> Bool) -> Program -> Program
runShadow exemptions typeExemptions p = runShadowM exemptions typeExemptions (ppProgram p >>= shadowProgram)

runShadowM :: Set Id -> (Type -> Bool) -> ShadowM a -> a
runShadowM exemptions typeExemptions m = evalState m (ShadowSt 0 Set.empty exemptions typeExemptions Nothing Map.empty Map.empty)

-- preprocess program
ppProgram :: Program -> ShadowM Program
ppProgram (Program decls) = do
    decls' <- mapM (mapM ppDecl) decls
    return $ Program decls'

mergeProcs (bools,rbools,ids,leaks) (bools',rbools',ids',leaks') = (bools,rbools,mappend ids ids',mappend leaks' leaks')

ppDecl :: BareDecl -> ShadowM BareDecl
ppDecl (ProcedureDecl atts name targs args rets contracts body) = do
--    when (isLeakFunName name) $ addExemption name
    -- add procedure modifies list
    bools <- mapM (liftM not . isExemptType . itwType) args
    rbools <- mapM (liftM not . isExemptType . itwType) rets
    let (ids,leak) = ppContracts contracts
    let (body',leaks) = ppMaybeBody ids body
    State.modify $ \st -> st { procedures = Map.insertWith mergeProcs name (bools,rbools,ids,leak `mappend` leaks) (procedures st) }
    let contracts' = gReplaceCanCall contracts
    return $ ProcedureDecl atts name targs args rets contracts' body'
ppDecl (ImplementationDecl atts name targs args rets body) = do
--    when (isLeakFunName name) $ addExemption name
    bools <- mapM (liftM not . isExemptType . snd) args
    rbools <- mapM (liftM not . isExemptType . snd) rets
    let ids = Set.empty
    let (body',leaks) = ppBodies ids body
    State.modify $ \st -> st { procedures = Map.insertWith mergeProcs name (bools,rbools,ids,leaks) (procedures st) }
    return $ ImplementationDecl atts name targs args rets body'
ppDecl d@(FunctionDecl atts name targs args ret body) = do
--    when (isLeakFunName name) $ addExemption name
    State.modify $ \st -> st { functions = Map.insert name (map isPrivateFArg args) (functions st) }
    return d
ppDecl d = return d

isPrivateFArg :: FArg -> Bool
isPrivateFArg (Nothing,_) = True
isPrivateFArg (Just i,_) = isLeakVarName i

ppContracts :: [Contract] -> (Set Id,Leakage)
ppContracts [] = (mempty,mempty) 
ppContracts (c:cs) = (m `mappend` ms,leak `mappend` leaks)
    where
    (m,leak) = ppContract c
    (ms,leaks) = ppContracts cs
ppContract :: Contract -> (Set Id,Leakage)
ppContract c@(Modifies _ ids) = (Set.fromList ids,mempty)
ppContract c@(Requires _ e) = (mempty,Leakage (publicIds e) mempty)
ppContract c@(Ensures _ e) = (mempty,Leakage (publicIds e) mempty)

ppMaybeBody :: Set Id -> Maybe Body -> (Maybe Body,Leakage)
ppMaybeBody modifies Nothing = (Nothing,mempty)
ppMaybeBody modifies (Just b) = (Just b',leak)
    where (b',leak) = ppBody modifies b

ppBodies :: Set Id -> [Body] -> ([Body],Leakage)
ppBodies modifies [] = ([],mempty)
ppBodies modifies (b:bs) = (b':bs',leak `mappend` leaks)
    where
    (b',leak) = ppBody modifies b
    (bs',leaks) = ppBodies modifies bs

ppBody :: Set Id -> Body -> (Body,Leakage)
ppBody modifies (vars,b) = ((vars,fromBasicBlocks bb'),leaks)
    where
    bb = returnAsLastBlock $ toBasicBlocks' b
    leaks = computeLeakage modifies bb
    bb' = gReplaceCanCall bb

isExempt :: Id -> ShadowM Bool
isExempt i = do
    m <- liftM exemptions State.get
    return $ Set.member i m

unlessExempt :: a -> Id -> ShadowM [a] -> ShadowM [a]
unlessExempt x i m = do
    is <- isExempt i
    if is then return [x] else m

unlessExemptFVS :: FVS a => a -> x -> ShadowM x -> ShadowM x
unlessExemptFVS x def m = unlessExemptFVS' x def id m

unlessExemptFVS' :: FVS a => a -> x -> (Bool -> Bool) -> ShadowM x -> ShadowM x
unlessExemptFVS' x def f m = do
    exs <- liftM exemptions State.get
    let vs = fvs x
    if (f $ Set.null (Set.difference vs exs)) then return def else m

shadowProgram :: Program -> ShadowM Program
shadowProgram (Program decls) = do
    decls' <- concatMapM shadowDecl decls
    return $ Program decls'

shadowDecl :: Decl -> ShadowM [Decl]
shadowDecl (Pos p d) = do
    ds' <- shadowBareDecl d
    return $ map (Pos p) ds'

shadowBareDecl :: BareDecl -> ShadowM [BareDecl]
shadowBareDecl d@(TypeDecl {}) = return [d]
shadowBareDecl (VarDecl atts ids) = do -- duplicate global variables
    atts' <- concatMapM (shadowAttribute True) atts
    bools <- mapM (liftM not . isExemptType . itwType) ids
    ids' <- concatMapM (uncurry shadowIdTypeWhere) $ zip bools ids
    return [VarDecl atts' ids']
shadowBareDecl d@(ConstantDecl atts unique ids t orderSpec complete) = do -- duplicate global constants
    atts' <- concatMapM (shadowAttribute True) atts
    orderSpec' <- shadowParentInfo orderSpec
    ids' <- concatMapM shadowConstId ids
    return [ConstantDecl atts' unique ids' t orderSpec' complete]
shadowBareDecl d@(AxiomDecl atts e) = if hasLeakageAnn d
    then do
        atts' <- concatMapM (shadowAttribute True) atts
        e' <- shadowExpression DualE e
        return [AxiomDecl atts' e']
    else do
        atts' <- concatMapM (shadowAttribute False) atts
        e' <- shadowExpression ShadowE e
        return [removeLeakageAnns d,AxiomDecl atts' e']
shadowBareDecl d@(ProcedureDecl atts name targs args rets contracts body) = shadowLocal $ unlessExempt d name $ do
    (bools,rbools,modifies,leaks) <- getProcedure name
    name' <- shadowId name
    atts' <- concatMapM (shadowAttribute True) atts
    -- duplicate parameters, returns and contracts
    args' <- concatMapM (uncurry shadowIdTypeWhere) $ zip bools args
    rets' <- concatMapM (uncurry shadowIdTypeWhere) $ zip rbools rets
    contracts' <- concatMapM (shadowContract name) contracts
    
    -- create a fresh shadow assertion variable
    shadow_ok <- freshVariable "shadow_ok"
    -- declare shadow_ok at the start
    let defShadow = IdTypeWhere shadow_ok BoolType $ Pos noPos tt
    let initShadow = Pos noPos $ Assign [(shadow_ok,[])] [posTT]
    
    State.modify $ \st -> st { shadowOk = Just shadow_ok }
    body' <- mapM (shadowBody modifies leaks) body
    State.modify $ \st -> st { shadowOk = Nothing }
    
    let d' = ProcedureDecl atts' name' targs args' rets' contracts' (addMaybeBody defShadow initShadow body')
    return [d']
shadowBareDecl d@(ImplementationDecl atts name targs args rets body) = shadowLocal $ unlessExempt d name $ do
    (bools,rbools,modifies,leaks) <- getProcedure name
    name' <- shadowId name
    atts' <- concatMapM (shadowAttribute True) atts
    args' <- concatMapM (uncurry shadowIdType) $ zip bools args
    rets' <- concatMapM (uncurry shadowIdType) $ zip rbools rets
    
    -- create a fresh shadow assertion variable
    shadow_ok <- freshVariable "shadow_ok"
    -- declare shadow_ok at the start
    let defShadow = IdTypeWhere shadow_ok BoolType $ Pos noPos tt
    let initShadow = Pos noPos $ Assign [(shadow_ok,[])] [posTT]
    
    State.modify $ \st -> st { shadowOk = Just shadow_ok }
    body' <- mapM (shadowBody modifies leaks) body
    State.modify $ \st -> st { shadowOk = Nothing }
    
    let d' = ImplementationDecl atts' name' targs args' rets' (addBodies defShadow initShadow body')
    return [d']
shadowBareDecl d@(FunctionDecl atts name targs args ret body) = shadowLocal $ unlessExempt d name $ if isLeakFunName name
    then do
        atts' <- concatMapM (shadowAttribute False) atts
        name' <- shadowId name
        bools <- liftM ((Map.!name) . functions) State.get
        args' <- concatMapM (uncurry shadowFArg) (zip bools args)
        [ret'] <- shadowFArg False ret
        body' <- mapM (shadowExpression DualE) body
        let d' = FunctionDecl atts' name' targs args' ret' body'
        return [d']
    else do
        atts' <- concatMapM (shadowAttribute False) atts
        name' <- shadowId name
        args' <- concatMapM (shadowFArg False) args
        [ret'] <- shadowFArg False ret
        body' <- mapM (shadowExpression ShadowE) body
        let d' = FunctionDecl atts' name' targs args' ret' body'
        return [removeLeakageAnns d,d']

getProcedure :: Id -> ShadowM ([Bool],[Bool],Set Id,Leakage)
getProcedure proc = do
    xs <- liftM procedures State.get
    case Map.lookup proc xs of
        Nothing -> error $ "procedure not found: " ++ show proc
        Just x -> return x

shadowBody :: Set Id -> Leakage -> Body -> ShadowM Body
shadowBody modifies leaks (vars,block) = do    
    -- duplicate local variables
    let shadowArg (atts,itws) = do
        atts' <- concatMapM (shadowAttribute True) atts
        bools <- mapM (liftM not . isExemptType . itwType) itws
        itws' <- concatMapM (uncurry shadowIdTypeWhere) $ zip bools itws
        return (atts',itws')
    vars' <- mapM shadowArg vars
    block' <- shadowBlock modifies leaks block
    return (vars',block')

isExemptType :: Type -> ShadowM Bool
isExemptType t = do
    f <- liftM typeExemptions State.get
    return $ f t

addBodies :: IdTypeWhere -> Statement -> [Body] -> [Body]
addBodies def init [] = [([([],[def])],[])]
addBodies def init (b:bs) = addBody def init b : bs

addBody :: IdTypeWhere -> Statement -> Body -> Body
addBody def init (defs,b) = (([],[def]):defs,Pos noPos ([],init) : b)

addMaybeBody :: IdTypeWhere -> Statement -> Maybe Body -> Maybe Body
addMaybeBody def init Nothing = Nothing
addMaybeBody def init (Just b) = Just $ addBody def init b

shadowBlock :: Set Id -> Leakage -> Block -> ShadowM Block
shadowBlock modifies leaks b = do
    -- assumes that it is already a basic block
    let bb = toBasicBlocks' b
    bb' <- shadowBasicBlocks modifies leaks bb
    -- assert shadow_ok before the last return
    Just shadow_ok <- liftM shadowOk State.get
    let assert = Predicate [] $ SpecClause Inline False $ Pos noPos $ Var shadow_ok
    let bb'' = updLast (\(l,ss) -> (l,Pos noPos assert : ss)) bb'
    return (fromBasicBlocks bb'')

shadowBasicBlocks :: Set Id -> Leakage -> [BasicBlock] -> ShadowM [BasicBlock]
shadowBasicBlocks modifies leaks bs = do
    let bbs = flattenBasicBlocks bs (fst $ last bs)
    bbs' <- forM bbs $ \(bb,next) -> do
        let splitBranches = isBenign leaks bb && length bb > 1
        if splitBranches
            then fprodBasicBlocks (startLabelBBs bb) next bb
            else prodBasicBlocks bb
    return $ concat bbs'

shadowContract :: Id -> Contract -> ShadowM [Contract]
shadowContract proc c@(Requires free e) | hasLeakName e = do
    e' <- shadowExpression DualE e
    return [Requires free e']
shadowContract proc c@(Requires free e) = do
    e' <- shadowExpression ShadowDualE e
    return [removeLeakageAnns c,Requires free e']
shadowContract proc c@(Ensures free e) | hasLeakName e = do
    e' <- shadowExpression DualE e
    return [Ensures free e']
shadowContract proc c@(Ensures free e) = do
    e' <- shadowExpression ShadowDualE e
    return [removeLeakageAnns c,Ensures free e']
shadowContract proc c@(Modifies free ids) = do
    ids' <- mapM shadowId ids
    return [Modifies free (List.nub $ ids++ids')]

shadowConstId :: Id -> ShadowM [Id]
shadowConstId i = do
    addVariable i
    unlessExempt i i $ liftM (\x -> [i,x]) (shadowId i)

shadowParentInfo :: ParentInfo -> ShadowM ParentInfo
shadowParentInfo = mapM (mapM (mapSndM shadowId))

shadowFArg :: Bool -> FArg -> ShadowM [FArg]
shadowFArg False a@(Nothing,t) = return [(Nothing,t)]
shadowFArg True a@(Nothing,t) = return [(Nothing,t),(Nothing,t)]
shadowFArg False a@(Just i,t) = do
    when (isLeakVarName i) $ error "leakage variable not supported"
    addVariable i
    addExemption i
    return [(Just i,t)]
shadowFArg True a@(Just i,t) = if isLeakVarName i
    then do
        addVariable i
        i' <- shadowId i
        addVariable i'
        return [(Just i,t),(Just i',t)]
    else do
        addVariable i
        addExemption i
        return [(Just i,t)]

shadowIdType :: Bool -> IdType -> ShadowM [IdType]
shadowIdType False it@(i,t) = do
    addVariable i
    addExemption i
    return [removeLeakageAnns it]
shadowIdType True it@(i,t) = do
    addVariable i
    unlessExempt it i $ do
        i' <- shadowId i
        return [removeLeakageAnns it,(i',t)]

shadowIdTypeWhere :: Bool -> IdTypeWhere -> ShadowM [IdTypeWhere]
shadowIdTypeWhere False itw@(IdTypeWhere i t w) = do
    addVariable i
    addExemption i
    return [removeLeakageAnns itw]
shadowIdTypeWhere True itw@(IdTypeWhere i t w) = do
    addVariable i
    unlessExempt itw i $ do
        i' <- shadowId i
        w' <- shadowExpression ShadowE w
        return [removeLeakageAnns itw,IdTypeWhere i' t w']

shadowId :: Id -> ShadowM Id
shadowId i = do
    exempt <- isExempt i
    if exempt then return i else return (i++".shadow")

shadowExpression :: ShadowEMode -> Expression -> ShadowM Expression
shadowExpression m (Pos p e) = do
    e' <- shadowBareExpression m e
    return $ Pos p e'

data ShadowEMode
    = DualE -- dual mode (normal && shadow)
    | ShadowE --shadow mode without leakage annotations
    | ShadowDualE -- shadow mode with leakage annotations
 deriving (Eq,Show,Typeable,Data)

isDualE DualE = True
isDualE x = False

isDualMode DualE = True
isDualMode ShadowDualE = True
isDualMode _ = False

isShadowMode ShadowE = True
isShadowMode ShadowDualE = True
isShadowMode _ = False

shadowDuals :: (a -> ShadowM a) -> [Bool] -> [a] -> ShadowM [a]
shadowDuals f [] [] = return []
shadowDuals f (False:bs) (e:es) = do
    es' <- shadowDuals f bs es
    return (e:es')
shadowDuals f (True:bs) (e:es) = do
    e' <- f e
    es' <- shadowDuals f bs es
    return (e:e':es')
shadowDuals f bs es = error "shadowDuals: mismatching arguments"

shadowBareExpression :: ShadowEMode -> BareExpression -> ShadowM BareExpression
shadowBareExpression DualE e | not (hasLeakageFunAnn e) = do
    e' <- shadowBareExpression ShadowE e
    return $ BinaryExpression And (Pos noPos e) (Pos noPos e')
shadowBareExpression ShadowE e@(Application n@(isLeakFunName -> True) es) = do
    error $ show $ text "unsupported dual expression" <+> pretty e <+> text "in ShadowE mode"
shadowBareExpression (isDualMode -> True) e@(Application n@(isLeakFunName -> True) es) = do
    n' <- shadowId n
    bools <- liftM ((Map.!n) . functions) State.get
    es' <- shadowDuals (shadowExpression ShadowE) bools es
    return $ Application n' es'
shadowBareExpression (isDualMode -> True) e@(isLeakExpr -> Just l) = do
    lShadow <- shadowBareExpression ShadowE l
    return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression m e@(isPublicExpr -> Just (l,PublicMid)) = error "public mid expression not supported"
shadowBareExpression (isDualMode -> True) e@(isPublicExpr -> Just (l,_)) = do
    lShadow <- shadowBareExpression ShadowE l
    return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression m e@(isDeclassifiedExpr -> Just (_,True)) = error "declassified out expression not supported"
shadowBareExpression (isDualMode -> True) e@(isDeclassifiedExpr -> Just (l,False)) = do
    lShadow <- shadowBareExpression ShadowE l
    return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression (isDualE -> False) e@(Literal {}) = return e
shadowBareExpression (isDualE -> False) (Var i) = do
    i' <- shadowId i
    return $ Var i'
shadowBareExpression (isDualE -> False) e@(Logical {}) = return e
shadowBareExpression (isDualE -> False) (Old e) = do
    e' <- shadowExpression ShadowE e
    return $ Old e'
shadowBareExpression m (Coercion e t) = do
    e' <- shadowExpression m e
    return $ Coercion e' t
shadowBareExpression m (UnaryExpression o e) = do
    e' <- shadowExpression m e
    return $ UnaryExpression o e'
shadowBareExpression m (BinaryExpression o e1 e2) = do
    e1' <- shadowExpression m e1
    e2' <- shadowExpression m e2
    return $ BinaryExpression o e1' e2'
shadowBareExpression DualE e@(Application name@(isLeakFunName -> False) es) = do
    name' <- shadowId name
    es' <- mapM (shadowExpression ShadowDualE) es
    let e' = Application name' es'
    return $ BinaryExpression Eq (Pos noPos $ removeLeakageAnns e) (Pos noPos e')
shadowBareExpression ShadowDualE e@(Application name@(isLeakFunName -> False) es) = do
    name' <- shadowId name
    es' <- mapM (shadowExpression ShadowDualE) es
    return $ Application name' es'
shadowBareExpression ShadowE e@(Application name@(isLeakFunName -> False) es) = do
    name' <- shadowId name
    es' <- mapM (shadowExpression ShadowE) es
    return $ Application name' es'
shadowBareExpression mode (MapSelection m es) = do
    m' <- shadowExpression mode m
    es' <- mapM (shadowExpression mode) es
    return $ MapSelection m' es'
shadowBareExpression mode (MapUpdate m es r) = do
    m' <- shadowExpression mode m
    es' <- mapM (shadowExpression mode) es
    r' <- shadowExpression mode r
    return $ MapUpdate m' es' r'
shadowBareExpression m@(isDualE -> False) (Quantified o alphas args trggs e) = withExemptions $ do
    let add (v,t) = do
        addVariable v
        when (isLeakVarName v) $ error "dual variable not supported in non-dual quantification"
        addExemption v
    mapM_ add args
    trggs' <- concatMapM (shadowQTriggerAttribute) trggs
    e' <- shadowExpression m e
    return $ Quantified o alphas args trggs' e'
shadowBareExpression DualE (Quantified o alphas args trggs e) = withExemptions $ do
    let add (v,t) = if isLeakVarName v
        then do
            addVariable v
            v' <- shadowId v
            addVariable v'
            return [(v,t),(v',t)]
        else do
            addVariable v
            addExemption v
            return [(v,t)]
    args' <- concatMapM add args
    trggs' <- concatMapM (shadowQTriggerAttribute) trggs
    e' <- shadowExpression DualE e
    return $ Quantified o alphas args' trggs' e'
shadowBareExpression m e = error $ show $ text "expression" <+> pretty e <+> text "not supported in mode" <+> text (show m)

shadowQTriggerAttribute :: QTriggerAttribute -> ShadowM [QTriggerAttribute]
shadowQTriggerAttribute t@(Left trggs) = do
    let sha e = if hasLeakageAnn e
                    then liftM (:[]) (shadowExpression DualE e)
                    else liftM (\e' -> [e,e']) (shadowExpression ShadowE e)
    t' <- liftM Left $ concatMapM sha trggs
    return [t']
shadowQTriggerAttribute t@(Right att) = do
    atts <- (shadowAttribute True) att
    return $ map Right atts

-- product
prodBasicBlocks :: [BasicBlock] -> ShadowM [BasicBlock]
prodBasicBlocks = mapM (shadowBasicBlock False)

shadowBasicBlock :: Bool -> BasicBlock -> ShadowM BasicBlock
shadowBasicBlock False (l,ss) = do
    ss' <- concatMapM (shadowStatement False) ss
    return (l,ss')
shadowBasicBlock True (l,ss) = do
    ss' <- concatMapM (shadowStatement True) ss
    l' <- shadowId l
    return (l',ss')

shadowStatement :: Bool -> Statement -> ShadowM [Statement]
shadowStatement doFull (Pos p s) = liftM (map (Pos p)) $ shadowBareStatement doFull s

shadowBareStatement :: Bool -> BareStatement -> ShadowM [BareStatement]
shadowBareStatement doFull s@(Predicate atts spec@(SpecClause st isAssume (Pos _ (isPublicExpr -> Just (l,ty))))) = do
    l' <- shadowBareExpression ShadowE l
    Just shadow_ok <- liftM shadowOk State.get
    let implies = case ty of
                    PublicMid -> Pos noPos . BinaryExpression Implies (Pos noPos $ Var shadow_ok)
                    otherwise -> id
    let e' = Pos noPos $ BinaryExpression Eq (Pos noPos l) (Pos noPos l')
    let spec' = SpecClause st isAssume $ implies e'
    return [Predicate atts spec']
shadowBareStatement doFull s@(Predicate atts spec@(SpecClause st False (Pos _ (isDeclassifiedExpr -> Just (l,ty))))) = do
    l' <- shadowBareExpression ShadowE l
    let e' = Pos noPos $ BinaryExpression Eq (Pos noPos l) (Pos noPos l')
    if ty
        then do -- delay assertion of equality
            Just shadow_ok <- liftM shadowOk State.get
            return [Assign [(shadow_ok,[])] [Pos noPos $ BinaryExpression And (Pos noPos $ Var shadow_ok) e'] ]
        else do -- in-place assertion of equality
            return [Predicate atts $ SpecClause st False e']
shadowBareStatement doFull s@(Havoc ids) = do
    ids' <- mapM shadowId ids
    let s' = Havoc ids'
    if doFull then return [s'] else return [removeLeakageAnns s,s']
shadowBareStatement doFull Skip = return [Skip]
shadowBareStatement doFull s@(Goto ids) = do
    ids' <- mapM shadowId ids
    if doFull
        then return [Goto ids']
        else return [removeLeakageAnns s] -- do not duplicate gotos
shadowBareStatement doFull p@(Predicate atts spec) = do
    ps' <- shadowPredicate doFull p
    return ps'
shadowBareStatement doFull s@(Assign lhs rhs) = do
    let shadowLhs (i,ess) = do
        i' <- shadowId i
        ess' <- mapM (mapM (shadowExpression ShadowE)) ess
        return (i',ess')
    lhs' <- mapM shadowLhs lhs
    rhs' <- mapM (shadowExpression ShadowE) rhs
    let s' = Assign lhs' rhs'
    if doFull
        then return [s']
        else return [removeLeakageAnns s,s']
shadowBareStatement doFull s@(Call atts is name es) = if doFull
    then do -- shadow arguments but not function name
        is' <- mapM shadowId is
        atts' <- concatMapM (shadowAttribute False) atts
        es' <- mapM (shadowExpression ShadowE) es
        let s' = Call atts' is' name es'
        return [s']
    else do -- duplicate call arguments
        (bools,rbools,_,_) <- getProcedure name
        is' <- shadowDuals shadowId rbools is
        name' <- shadowId name
        atts' <- concatMapM (shadowAttribute True) atts
        es' <- shadowDuals (shadowExpression ShadowE) bools es
        let s' = Call atts' is' name' es'
        return [s']
shadowBareStatement doFull s@(CallForall i es) = do
    i' <- shadowId i
    es' <- mapM (shadowWildcardExpression ShadowDualE) es
    let s' = CallForall i' es'
    if doFull
        then return [s']
        else return [removeLeakageAnns s,s']
shadowBareStatement doFull Return = return [Return]
shadowBareStatement doFull (Break {}) = error "shadowBareStatement: Break"
shadowBareStatement doFull (If {}) = error "shadowBareStatement: If"
shadowBareStatement doFull (While {}) = error "shadowBareStatement: While"

shadowDual :: Data a => (a -> ShadowM a) -> (a -> ShadowM [a])
shadowDual m x = do
    x' <- m x
    return [removeLeakageAnns x,x']

shadowAttribute :: Bool -> Attribute -> ShadowM [Attribute]
shadowAttribute doDual (Attribute tag vals) = liftM (map (Attribute tag)) $ mapM (shadowAttrVal doDual) vals
    where
    shadowAttrVal :: Bool -> AttrValue -> ShadowM [AttrValue]
    shadowAttrVal False v@(EAttr e) = do
        v' <- liftM EAttr $ shadowExpression ShadowE e
        return [v']
    shadowAttrVal True v@(EAttr e) = if hasLeakageAnn e
        then do
            v' <- liftM EAttr $ shadowExpression DualE e
            return [v']
        else do
            v' <- liftM EAttr $ shadowExpression ShadowE e
            if doDual then return [removeLeakageAnns v,v'] else return [v']
    shadowAttrVal _ (SAttr s) = return [SAttr s]

shadowWildcardExpression :: ShadowEMode -> WildcardExpression -> ShadowM WildcardExpression
shadowWildcardExpression m Wildcard = return Wildcard
shadowWildcardExpression m (Expr e) = do
    e' <- shadowExpression m e
    return $ Expr e'

shadowPredicate :: Bool -> BareStatement -> ShadowM [BareStatement]
shadowPredicate doFull p@(Predicate atts (SpecClause st isAssume e)) | hasLeakFunName e = do
    e' <- shadowExpression DualE e
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute True) atts
    let p' = Predicate atts' s'
    return [p']
shadowPredicate doFull p@(Predicate atts (SpecClause st isAssume e)) = do
    e' <- shadowExpression ShadowDualE e
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute False) atts
    let p' = Predicate atts' s'
    if doFull then return [p'] else return [removeLeakageAnns p,p']       

-- normal program with the last goto replaced pointing to the shadow label and annotations removed
redirectBasicBlock :: Maybe Id -> Id -> BasicBlock -> BasicBlock
redirectBasicBlock next startShadow (l,ss) = (l,concatMap redirectStatement ss)
    where
    redirectStatement (Pos p s) = map (Pos p) (redirectBareStatement s)
    redirectBareStatement (Goto [l]) | Just l == next = [Goto [startShadow]]
    redirectBareStatement x = [removeLeakageAnns x]

-- full product
fprodBasicBlocks :: Id -> Maybe Id -> [BasicBlock] -> ShadowM [BasicBlock]
fprodBasicBlocks start next bs = do
    startShadow <- shadowId start
    let bsRedir = map (redirectBasicBlock next startShadow) bs
    -- duplicated program without shadowing the final goto
    withExemptions $ do
        mapM_ addExemption next
        bsShadow <- mapM (shadowBasicBlock True) bs
        return $ bsRedir ++ bsShadow

addExemption :: Id -> ShadowM ()
addExemption i = State.modify $ \st -> st { exemptions = Set.insert i (exemptions st) }

addVariable :: Id -> ShadowM ()
addVariable i = State.modify $ \st -> st { variables = Set.insert i (variables st) }

freshVariable :: Id -> ShadowM Id
freshVariable v = do
    vs <- liftM variables State.get
    if Set.member v vs
        then do
            i <- incSeed
            freshVariable (v ++ "_" ++ show i)
        else addVariable v >> return v

incSeed :: ShadowM Int
incSeed = do
    i <- liftM seed State.get
    State.modify $ \st -> st { seed = succ (seed st) }
    return i

shadowLocal :: ShadowM a -> ShadowM a
shadowLocal m = do
    st <- State.get
    x <- m
    State.modify $ \st' -> st' { variables = variables st, exemptions = exemptions st }
    return x

withExemptions :: ShadowM a -> ShadowM a
withExemptions m = do
    st <- State.get
    x <- m
    State.modify $ \st' -> st' { exemptions = exemptions st }
    return x


