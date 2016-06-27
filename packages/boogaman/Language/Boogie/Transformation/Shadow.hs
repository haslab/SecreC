--TODO: uniqueness of shadow variables

{-# LANGUAGE DoAndIfThenElse, DeriveDataTypeable, ViewPatterns #-}

module Language.Boogie.Transformation.Shadow where

import Language.Boogie.Options
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
    , fullProd :: Bool -- perform full product or normal product
    }

type ShadowM x = State ShadowSt x

runShadow :: Options -> Set Id -> (Type -> Bool) -> Program -> Program
runShadow opts exemptions typeExemptions p = runShadowM exemptions typeExemptions (ppProgram opts p >>= shadowProgram opts)

runShadowM :: Set Id -> (Type -> Bool) -> ShadowM a -> a
runShadowM exemptions typeExemptions m = evalState m (ShadowSt 0 Set.empty exemptions typeExemptions Nothing Map.empty Map.empty False)

-- preprocess program
ppProgram :: Options -> Program -> ShadowM Program
ppProgram opts (Program decls) = do
    decls' <- mapM (mapM $ ppDecl opts) decls
    return $ Program decls'

mergeProcs (bools,rbools,ids,leaks) (bools',rbools',ids',leaks') = (bools,rbools,mappend ids ids',mappend leaks' leaks')

ppDecl :: Options -> BareDecl -> ShadowM BareDecl
ppDecl opts (ProcedureDecl atts name targs args rets contracts body) = do
--    when (isLeakFunName name) $ addExemption name
    -- add procedure modifies list
    bools <- mapM (liftM not . isExemptType . itwType) args
    rbools <- mapM (liftM not . isExemptType . itwType) rets
    let (ids,leak) = ppContracts opts contracts
    let (body',leaks) = ppMaybeBody opts ids body
    State.modify $ \st -> st { procedures = Map.insertWith mergeProcs name (bools,rbools,ids,leak `mappend` leaks) (procedures st) }
    let contracts' = gReplaceCanCall opts contracts
    return $ ProcedureDecl atts name targs args rets contracts' body'
ppDecl opts (ImplementationDecl atts name targs args rets body) = do
--    when (isLeakFunName name) $ addExemption name
    bools <- mapM (liftM not . isExemptType . snd) args
    rbools <- mapM (liftM not . isExemptType . snd) rets
    let ids = Set.empty
    let (body',leaks) = ppBodies opts ids body
    State.modify $ \st -> st { procedures = Map.insertWith mergeProcs name (bools,rbools,ids,leaks) (procedures st) }
    return $ ImplementationDecl atts name targs args rets body'
ppDecl opts d@(FunctionDecl atts name targs args ret body) = do
--    when (isLeakFunName name) $ addExemption name
    State.modify $ \st -> st { functions = Map.insert name (map (isPrivateFArg opts) args) (functions st) }
    return d
ppDecl opts d = return d

isPrivateFArg :: Options -> FArg -> Bool
isPrivateFArg opts (Nothing,_) = True
isPrivateFArg opts (Just i,_) = isLeakVarName opts i

ppContracts :: Options -> [Contract] -> (Set Id,Leakage)
ppContracts opts [] = (mempty,mempty) 
ppContracts opts (c:cs) = (m `mappend` ms,leak `mappend` leaks)
    where
    (m,leak) = ppContract opts c
    (ms,leaks) = ppContracts opts cs
ppContract :: Options -> Contract -> (Set Id,Leakage)
ppContract opts c@(Modifies _ ids) = (Set.fromList ids,mempty)
ppContract opts c@(Requires _ e) = (mempty,Leakage (publicIds opts e) mempty)
ppContract opts c@(Ensures _ e) = (mempty,Leakage (publicIds opts e) mempty)

ppMaybeBody :: Options -> Set Id -> Maybe Body -> (Maybe Body,Leakage)
ppMaybeBody opts modifies Nothing = (Nothing,mempty)
ppMaybeBody opts modifies (Just b) = (Just b',leak)
    where (b',leak) = ppBody opts modifies b

ppBodies :: Options -> Set Id -> [Body] -> ([Body],Leakage)
ppBodies opts modifies [] = ([],mempty)
ppBodies opts modifies (b:bs) = (b':bs',leak `mappend` leaks)
    where
    (b',leak) = ppBody opts modifies b
    (bs',leaks) = ppBodies opts modifies bs

ppBody :: Options -> Set Id -> Body -> (Body,Leakage)
ppBody opts modifies (vars,b) = ((vars,fromBasicBlocks bb'),leaks)
    where
    bb = returnAsLastBlock $ toBasicBlocks' b
    leaks = computeLeakage opts modifies bb
    bb' = gReplaceCanCall opts bb

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

shadowProgram :: Options -> Program -> ShadowM Program
shadowProgram opts (Program decls) = do
    decls' <- concatMapM (shadowDecl opts) decls
    return $ Program decls'

shadowDecl :: Options -> Decl -> ShadowM [Decl]
shadowDecl opts (Pos p d) = do
    ds' <- shadowBareDecl opts d
    return $ map (Pos p) ds'

shadowBareDecl :: Options -> BareDecl -> ShadowM [BareDecl]
shadowBareDecl opts d@(TypeDecl {}) = return [d]
shadowBareDecl opts (VarDecl atts ids) = do -- duplicate global variables
    atts' <- concatMapM (shadowAttribute opts True) atts
    bools <- mapM (liftM not . isExemptType . itwType) ids
    ids' <- concatMapM (uncurry (shadowIdTypeWhere opts)) $ zip bools ids
    return [VarDecl atts' ids']
shadowBareDecl opts d@(ConstantDecl atts unique ids t orderSpec complete) = do -- duplicate global constants
    atts' <- concatMapM (shadowAttribute opts True) atts
    orderSpec' <- shadowParentInfo orderSpec
    ids' <- concatMapM shadowConstId ids
    return [ConstantDecl atts' unique ids' t orderSpec' complete]
shadowBareDecl opts d@(AxiomDecl atts e) = if hasLeakageAtt atts
    then do
        atts' <- concatMapM (shadowAttribute opts True) atts
        e' <- shadowExpression opts DualE e
        return [AxiomDecl atts' e']
    else do
        atts' <- concatMapM (shadowAttribute opts False) $ atts
        e' <- shadowExpression opts ShadowE $ e
        return [removeLeakageAnns opts d,AxiomDecl atts' e']
shadowBareDecl opts d@(ProcedureDecl atts name targs args rets contracts body) = shadowLocal $ unlessExempt d name $ do
    (bools,rbools,modifies,leaks) <- getProcedure name
    name' <- shadowId name
    atts' <- concatMapM (shadowAttribute opts True) atts
    -- duplicate parameters, returns and contracts
    args' <- concatMapM (uncurry $ shadowIdTypeWhere opts) $ zip bools args
    rets' <- concatMapM (uncurry $ shadowIdTypeWhere opts) $ zip rbools rets
    contracts' <- concatMapM (shadowContract opts name) contracts
    
    -- create a fresh shadow assertion variable
    shadow_ok <- freshVariable "shadow_ok"
    -- declare shadow_ok at the start
    let defShadow = IdTypeWhere shadow_ok BoolType $ Pos noPos tt
    let initShadow = Pos noPos $ Assign [(shadow_ok,[])] [posTT]
    
    State.modify $ \st -> st { shadowOk = Just shadow_ok }
    body' <- mapM (shadowBody opts modifies leaks) body
    State.modify $ \st -> st { shadowOk = Nothing }
    
    let d' = ProcedureDecl atts' name' targs args' rets' contracts' (addMaybeBody defShadow initShadow body')
    return [d']
shadowBareDecl opts d@(ImplementationDecl atts name targs args rets body) = shadowLocal $ unlessExempt d name $ do
    (bools,rbools,modifies,leaks) <- getProcedure name
    name' <- shadowId name
    atts' <- concatMapM (shadowAttribute opts True) atts
    args' <- concatMapM (uncurry $ shadowIdType opts) $ zip bools args
    rets' <- concatMapM (uncurry $ shadowIdType opts) $ zip rbools rets
    
    -- create a fresh shadow assertion variable
    shadow_ok <- freshVariable "shadow_ok"
    -- declare shadow_ok at the start
    let defShadow = IdTypeWhere shadow_ok BoolType $ Pos noPos tt
    let initShadow = Pos noPos $ Assign [(shadow_ok,[])] [posTT]
    
    State.modify $ \st -> st { shadowOk = Just shadow_ok }
    body' <- mapM (shadowBody opts modifies leaks) body
    State.modify $ \st -> st { shadowOk = Nothing }
    
    let d' = ImplementationDecl atts' name' targs args' rets' (addBodies defShadow initShadow body')
    return [d']
shadowBareDecl opts d@(FunctionDecl atts name targs args ret body) = shadowLocal $ unlessExempt d name $ if isLeakFunName opts name
    then do
        atts' <- concatMapM (shadowAttribute opts False) atts
        name' <- shadowId name
        bools <- liftM ((Map.!name) . functions) State.get
        args' <- concatMapM (uncurry (shadowFArg opts)) (zip bools args)
        [ret'] <- shadowFArg opts False ret
        body' <- mapM (shadowExpression opts DualE) body
        let d' = FunctionDecl atts' name' targs args' ret' body'
        return [d']
    else do
        atts' <- concatMapM (shadowAttribute opts False) atts
        name' <- shadowId name
        args' <- concatMapM (shadowFArg opts False) args
        [ret'] <- shadowFArg opts False ret
        body' <- mapM (shadowExpression opts ShadowE) body
        let d' = FunctionDecl atts' name' targs args' ret' body'
        return [removeLeakageAnns opts d,d']

getProcedure :: Id -> ShadowM ([Bool],[Bool],Set Id,Leakage)
getProcedure proc = do
    xs <- liftM procedures State.get
    case Map.lookup proc xs of
        Nothing -> error $ "procedure not found: " ++ show proc
        Just x -> return x

shadowBody :: Options -> Set Id -> Leakage -> Body -> ShadowM Body
shadowBody opts modifies leaks (vars,block) = do    
    -- duplicate local variables
    let shadowArg (atts,itws) = do
        atts' <- concatMapM (shadowAttribute opts True) atts
        bools <- mapM (liftM not . isExemptType . itwType) itws
        itws' <- concatMapM (uncurry (shadowIdTypeWhere opts)) $ zip bools itws
        return (atts',itws')
    vars' <- mapM shadowArg vars
    block' <- shadowBlock opts modifies leaks block
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

shadowBlock :: Options -> Set Id -> Leakage -> Block -> ShadowM Block
shadowBlock opts modifies leaks b = do
    -- assumes that it is already a basic block
    let bb = toBasicBlocks' b
    bb' <- shadowBasicBlocks opts modifies leaks bb
    -- assert shadow_ok before the last return
    Just shadow_ok <- liftM shadowOk State.get
    let assert = Predicate [] $ SpecClause Inline False $ Pos noPos $ Var shadow_ok
    let bb'' = updLast (\(l,ss) -> (l,Pos noPos assert : ss)) bb'
    return (fromBasicBlocks bb'')

shadowBasicBlocks :: Options -> Set Id -> Leakage -> [BasicBlock] -> ShadowM [BasicBlock]
shadowBasicBlocks opts modifies leaks bs = do
    let bbs = flattenBasicBlocks bs (fst $ last bs)
    bbs' <- forM bbs $ \(bb,next) -> do
        let doFull = isBenign leaks bb && length bb > 1
        State.modify $ \st -> st { fullProd = doFull }
        if doFull
            then fprodBasicBlocks opts (startLabelBBs bb) next bb -- full product: backward leakage analysis
            else prodBasicBlocks opts bb -- simple product: forward leakage analysis
    return $ concat bbs'

shadowContract :: Options -> Id -> Contract -> ShadowM [Contract]
shadowContract opts proc c@(Requires free e) | hasLeakageFunAnn opts e = do
    e' <- shadowExpression opts DualE e
    return [Requires free e']
shadowContract opts proc c@(Requires free e) = do
    e' <- shadowExpression opts ShadowDualE e
    return [removeLeakageAnns opts c,Requires free e']
shadowContract opts proc c@(Ensures free e) | hasLeakageFunAnn opts e = do
    e' <- shadowExpression opts DualE e
    return [Ensures free e']
shadowContract opts proc c@(Ensures free e) = do
    e' <- shadowExpression opts ShadowDualE e
    return [removeLeakageAnns opts c,Ensures free e']
shadowContract opts proc c@(Modifies free ids) = do
    ids' <- mapM shadowId ids
    return [Modifies free (List.nub $ ids++ids')]

shadowConstId :: Id -> ShadowM [Id]
shadowConstId i = do
    addVariable i
    unlessExempt i i $ liftM (\x -> [i,x]) (shadowId i)

shadowParentInfo :: ParentInfo -> ShadowM ParentInfo
shadowParentInfo = mapM (mapM (mapSndM shadowId))

shadowFArg :: Options -> Bool -> FArg -> ShadowM [FArg]
shadowFArg opts False a@(Nothing,t) = return [(Nothing,t)]
shadowFArg opts True a@(Nothing,t) = return [(Nothing,t),(Nothing,t)]
shadowFArg opts False a@(Just i,t) = do
    when (isLeakVarName opts i) $ error "leakage variable not supported"
    addVariable i
    addExemption i
    return [(Just i,t)]
shadowFArg opts True a@(Just i,t) = if isLeakVarName opts i
    then do
        addVariable i
        i' <- shadowId i
        addVariable i'
        return [(Just i,t),(Just i',t)]
    else do
        addVariable i
        addExemption i
        return [(Just i,t)]

shadowIdType :: Options -> Bool -> IdType -> ShadowM [IdType]
shadowIdType opts False it@(i,t) = do -- if the type is exempt, then the variable is exempt
    addVariable i
    addExemption i
    return [removeLeakageAnns opts it]
shadowIdType opts True it@(i,t) = do
    addVariable i
    unlessExempt it i $ do
        i' <- shadowId i
        return [removeLeakageAnns opts it,(i',t)]

shadowIdTypeWhere :: Options -> Bool -> IdTypeWhere -> ShadowM [IdTypeWhere]
shadowIdTypeWhere opts False itw@(IdTypeWhere i t w) = do
    addVariable i
    addExemption i
    return [removeLeakageAnns opts itw]
shadowIdTypeWhere opts True itw@(IdTypeWhere i t w) = do
    addVariable i
    unlessExempt itw i $ do
        i' <- shadowId i
        w' <- shadowExpression opts ShadowE w
        return [removeLeakageAnns opts itw,IdTypeWhere i' t w']

shadowId :: Id -> ShadowM Id
shadowId i = do
    exempt <- isExempt i
    if exempt then return i else return (i++".shadow")

shadowExpression :: Options -> ShadowEMode -> Expression -> ShadowM Expression
shadowExpression opts m (Pos p e) = do
    e' <- shadowBareExpression opts m e
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

shadowBareExpression :: Options -> ShadowEMode -> BareExpression -> ShadowM BareExpression
shadowBareExpression opts ShadowE e | hasLeakageFunAnn opts e = error $ show $ text "unsupported leakage expression" <+> pretty e <+> text "in ShadowE mode"
shadowBareExpression opts DualE e | not (hasLeakageFunAnn opts e) = do
    e' <- shadowBareExpression opts ShadowE e
    return $ BinaryExpression And (Pos noPos e) (Pos noPos e')
shadowBareExpression opts (isDualMode -> True) e@(Application n@(isLeakFunName opts -> True) es) = do
    n' <- shadowId n
    bools <- liftM ((Map.!n) . functions) State.get
    es' <- shadowDuals (shadowExpression opts ShadowE) bools es
    return $ Application n' es'
shadowBareExpression opts (isDualMode -> True) e@(isLeakExpr opts -> Just l) = do
    lShadow <- shadowBareExpression opts ShadowE l
    return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression opts m e@(isPublicExpr opts -> Just (l,PublicMid)) = do
    doFull <- State.gets fullProd
    if doFull
        then error "public mid expression not supported"
        else do
            lShadow <- shadowBareExpression opts ShadowE l
            return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression opts (isDualMode -> True) e@(isPublicExpr opts -> Just (l,_)) = do
    lShadow <- shadowBareExpression opts ShadowE l
    return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression opts m e@(isDeclassifiedExpr opts -> Just (_,True)) = error "declassified out expression not supported"
shadowBareExpression opts (isDualMode -> True) e@(isDeclassifiedExpr opts -> Just (l,False)) = do
    lShadow <- shadowBareExpression opts ShadowE l
    return $ BinaryExpression Eq (Pos noPos l) (Pos noPos lShadow)
shadowBareExpression opts (isDualE -> False) e@(Literal {}) = return e
shadowBareExpression opts (isDualE -> False) (Var i) = do
    i' <- shadowId i
    return $ Var i'
shadowBareExpression opts (isDualE -> False) e@(Logical {}) = return e
shadowBareExpression opts (isDualE -> False) (Old e) = do
    e' <- shadowExpression opts ShadowE e
    return $ Old e'
shadowBareExpression opts m (Coercion e t) = do
    e' <- shadowExpression opts m e
    return $ Coercion e' t
shadowBareExpression opts m (UnaryExpression o e) = do
    e' <- shadowExpression opts m e
    return $ UnaryExpression o e'
shadowBareExpression opts m (BinaryExpression o e1 e2) = do
    e1' <- shadowExpression opts m e1
    e2' <- shadowExpression opts m e2
    return $ BinaryExpression o e1' e2'
shadowBareExpression opts DualE e@(Application name@(isLeakFunName opts -> False) es) = do
    name' <- shadowId name
    es' <- mapM (shadowExpression opts ShadowDualE) es
    let e' = Application name' es'
    return $ BinaryExpression Eq (Pos noPos $ removeLeakageAnns opts e) (Pos noPos e')
shadowBareExpression opts ShadowDualE e@(Application name@(isLeakFunName opts -> False) es) = do
    name' <- shadowId name
    es' <- mapM (shadowExpression opts ShadowDualE) es
    return $ Application name' es'
shadowBareExpression opts ShadowE e@(Application name@(isLeakFunName opts -> False) es) = do
    name' <- shadowId name
    es' <- mapM (shadowExpression opts ShadowE) es
    return $ Application name' es'
shadowBareExpression opts mode (MapSelection m es) = do
    m' <- shadowExpression opts mode m
    es' <- mapM (shadowExpression opts mode) es
    return $ MapSelection m' es'
shadowBareExpression opts mode (MapUpdate m es r) = do
    m' <- shadowExpression opts mode m
    es' <- mapM (shadowExpression opts mode) es
    r' <- shadowExpression opts mode r
    return $ MapUpdate m' es' r'
shadowBareExpression opts m@(isDualE -> False) (Quantified o alphas args trggs e) = withExemptions $ do
    let add (v,t) = do
        addVariable v
        addExemption v
    mapM_ add args
    trggs' <- concatMapM (shadowQTriggerAttribute opts False) trggs
    e' <- shadowExpression opts m e
    return $ Quantified o alphas args trggs' e'
shadowBareExpression opts DualE (Quantified o alphas args trggs e) = withExemptions $ do
    let add (v,t) = if isLeakVarName opts v
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
    trggs' <- concatMapM (shadowQTriggerAttribute opts True) trggs
    e' <- shadowExpression opts DualE e
    return $ Quantified o alphas args' trggs' e'
shadowBareExpression opts m e = error $ show $ text "expression" <+> pretty e <+> text "not supported in mode" <+> text (show m)

shadowQTriggerAttribute :: Options -> Bool -> QTriggerAttribute -> ShadowM [QTriggerAttribute]
shadowQTriggerAttribute opts True t@(Left trggs) = do
    let sha e = if hasLeakageAnn opts e
                    then liftM (:[]) (shadowExpression opts DualE e)
                    else liftM (\e' -> [e,e']) (shadowExpression opts ShadowE e)
    t' <- liftM Left $ concatMapM sha trggs
    return [t']
shadowQTriggerAttribute opts False t@(Left trggs) = do
    let sha e = liftM (:[]) (shadowExpression opts ShadowE e)
    t' <- liftM Left $ concatMapM sha trggs
    return [t']
shadowQTriggerAttribute opts doDual t@(Right att) = do
    atts <- (shadowAttribute opts doDual) att
    return $ map Right atts

-- product
prodBasicBlocks :: Options -> [BasicBlock] -> ShadowM [BasicBlock]
prodBasicBlocks opts = mapM (shadowBasicBlock opts False)

shadowBasicBlock :: Options -> Bool -> BasicBlock -> ShadowM BasicBlock
shadowBasicBlock opts False (l,ss) = do
    ss' <- concatMapM (shadowStatement opts False) ss
    return (l,ss')
shadowBasicBlock opts True (l,ss) = do
    ss' <- concatMapM (shadowStatement opts True) ss
    l' <- shadowId l
    return (l',ss')

shadowStatement :: Options -> Bool -> Statement -> ShadowM [Statement]
shadowStatement opts doFull (Pos p s) = do
    liftM (map (Pos p)) $ shadowBareStatement opts doFull s

shadowBareStatement :: Options -> Bool -> BareStatement -> ShadowM [BareStatement]
shadowBareStatement opts doFull s@(Predicate atts spec@(SpecClause st isAssume (Pos _ (isPublicExpr opts -> Just (l,ty))))) = do
    l' <- shadowBareExpression opts ShadowE l
    Just shadow_ok <- liftM shadowOk State.get
    let implies = case ty of
                    PublicMid -> if doFull then Pos noPos . BinaryExpression Implies (Pos noPos $ Var shadow_ok) else id
                    otherwise -> id
    let e' = Pos noPos $ BinaryExpression Eq (Pos noPos l) (Pos noPos l')
    let spec' = SpecClause st isAssume $ implies e'
    return [Predicate atts spec']
shadowBareStatement opts doFull s@(Predicate atts spec@(SpecClause st False (Pos _ (isDeclassifiedExpr opts -> Just (l,ty))))) = do
    l' <- shadowBareExpression opts ShadowE l
    let e' = Pos noPos $ BinaryExpression Eq (Pos noPos l) (Pos noPos l')
    if ty
        then do -- delay assertion of equality
            Just shadow_ok <- liftM shadowOk State.get
            return [Assign [(shadow_ok,[])] [Pos noPos $ BinaryExpression And (Pos noPos $ Var shadow_ok) e'] ]
        else do -- in-place assertion of equality
            return [Predicate atts $ SpecClause st False e']
shadowBareStatement opts doFull s@(Havoc ids) = do
    ids' <- mapM shadowId ids
    let s' = Havoc ids'
    if doFull then return [s'] else return [removeLeakageAnns opts s,s']
shadowBareStatement opts doFull Skip = return [Skip]
shadowBareStatement opts doFull s@(Goto ids) = do
    ids' <- mapM shadowId ids
    if doFull
        then return [Goto ids']
        else return [removeLeakageAnns opts s] -- do not duplicate gotos
shadowBareStatement opts doFull p@(Predicate atts spec) = do

    ps' <- shadowPredicate opts doFull p
    return ps'
shadowBareStatement opts doFull s@(Assign lhs rhs) = do
    let shadowLhs (i,ess) = do
        i' <- shadowId i
        ess' <- mapM (mapM (shadowExpression opts ShadowE)) ess
        return (i',ess')
    lhs' <- mapM shadowLhs lhs
    rhs' <- mapM (shadowExpression opts ShadowE) rhs
    let s' = Assign lhs' rhs'
    if doFull
        then return [s']
        else return [removeLeakageAnns opts s,s']
shadowBareStatement opts doFull s@(Call atts is name es) = if doFull
    then do -- shadow arguments but not function name
        is' <- mapM shadowId is
        atts' <- concatMapM (shadowAttribute opts False) atts
        es' <- mapM (shadowExpression opts ShadowE) es
        let s' = Call atts' is' name es'
        return [s']
    else do -- duplicate call arguments
        (bools,rbools,_,_) <- getProcedure name
        is' <- shadowDuals shadowId rbools is
        name' <- shadowId name
        atts' <- concatMapM (shadowAttribute opts True) atts
        es' <- shadowDuals (shadowExpression opts ShadowE) bools es
        let s' = Call atts' is' name' es'
        return [s']
shadowBareStatement opts doFull s@(CallForall i es) = do
    i' <- shadowId i
    es' <- mapM (shadowWildcardExpression opts ShadowDualE) es
    let s' = CallForall i' es'
    if doFull
        then return [s']
        else return [removeLeakageAnns opts s,s']
shadowBareStatement opts doFull Return = return [Return]
shadowBareStatement opts doFull (Break {}) = error "shadowBareStatement: Break"
shadowBareStatement opts doFull (If {}) = error "shadowBareStatement: If"
shadowBareStatement opts doFull (While {}) = error "shadowBareStatement: While"

shadowDual :: Data a => Options -> (a -> ShadowM a) -> (a -> ShadowM [a])
shadowDual opts m x = do
    x' <- m x
    return [removeLeakageAnns opts x,x']

shadowAttribute :: Options -> Bool -> Attribute -> ShadowM [Attribute]
shadowAttribute opts doDual (Attribute tag vals) = do
    liftM (map (Attribute tag)) $ mapM (shadowAttrVal opts doDual) vals
  where
    shadowAttrVal :: Options -> Bool -> AttrValue -> ShadowM [AttrValue]
    shadowAttrVal opts False v@(EAttr e) = do
        v' <- liftM EAttr $ shadowExpression opts ShadowE e
        return [v']
    shadowAttrVal opts True v@(EAttr e) = if hasLeakageAnn opts e
        then do
            v' <- liftM EAttr $ shadowExpression opts DualE e
            return [v']
        else do
            v' <- liftM EAttr $ shadowExpression opts ShadowE e
            if doDual then return [removeLeakageAnns opts v,v'] else return [v']
    shadowAttrVal opts _ (SAttr s) = return [SAttr s]

shadowWildcardExpression :: Options -> ShadowEMode -> WildcardExpression -> ShadowM WildcardExpression
shadowWildcardExpression opts m Wildcard = return Wildcard
shadowWildcardExpression opts m (Expr e) = do
    e' <- shadowExpression opts m e
    return $ Expr e'

shadowPredicate :: Options -> Bool -> BareStatement -> ShadowM [BareStatement]
shadowPredicate opts doFull p@(Predicate atts (SpecClause st isAssume e)) | hasLeakageFunAnn opts e = do
    e' <- shadowExpression opts DualE e
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute opts True) atts
    let p' = Predicate atts' s'
    return [p']
shadowPredicate opts doFull p@(Predicate atts (SpecClause st isAssume e)) = do
    e' <- shadowExpression opts ShadowDualE e
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute opts False) atts
    let p' = Predicate atts' s'
    if doFull then return [p'] else return [removeLeakageAnns opts p,p']       

-- normal program with the last goto replaced pointing to the shadow label and annotations removed
redirectBasicBlock :: Options -> Maybe Id -> Id -> BasicBlock -> BasicBlock
redirectBasicBlock opts next startShadow (l,ss) = (l,concatMap redirectStatement ss)
    where
    redirectStatement (Pos p s) = map (Pos p) (redirectBareStatement s)
    redirectBareStatement (Goto [l]) | Just l == next = [Goto [startShadow]]
    redirectBareStatement x = [removeLeakageAnns opts x]

-- full product
fprodBasicBlocks :: Options -> Id -> Maybe Id -> [BasicBlock] -> ShadowM [BasicBlock]
fprodBasicBlocks opts start next bs = do
    startShadow <- shadowId start
    let bsRedir = map (redirectBasicBlock opts next startShadow) bs
    -- duplicated program without shadowing the final goto
    withExemptions $ do
        mapM_ addExemption next
        bsShadow <- mapM (shadowBasicBlock opts True) bs
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


