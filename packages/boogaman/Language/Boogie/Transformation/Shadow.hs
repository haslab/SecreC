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
import Language.Boogie.Analysis.Annotation
import Language.Boogie.Transformation.Simplify

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

type ShadowM m x = StateT ShadowSt m x

runShadow :: MonadIO m => Options -> Set Id -> (Type -> Bool) -> Program -> m Program
runShadow opts exemptions typeExemptions p = runShadowM exemptions typeExemptions (ppProgram opts p >>= shadowProgram opts)

runShadowM :: MonadIO m => Set Id -> (Type -> Bool) -> ShadowM m a -> m a
runShadowM exemptions typeExemptions m = evalStateT m (ShadowSt 0 Set.empty exemptions typeExemptions Nothing Map.empty Map.empty False)

-- preprocess program
ppProgram :: MonadIO m => Options -> Program -> ShadowM m Program
ppProgram opts (Program decls) = do
    decls' <- mapM (ppCommentOrDecl opts) decls
    return $ Program decls'

ppCommentOrDecl :: MonadIO m => Options -> Either Comment Decl -> ShadowM m (Either Comment Decl)
ppCommentOrDecl opts (Left c) = return (Left c)
ppCommentOrDecl opts (Right d) = do
    d' <- mapM (ppDecl opts) d
    return $ Right d'

mergeProcs (bools,rbools,ids,leaks) (bools',rbools',ids',leaks') = (bools,rbools,mappend ids ids',mappend leaks' leaks')

ppDecl :: MonadIO m => Options -> BareDecl -> ShadowM m BareDecl
ppDecl opts (ProcedureDecl atts name targs args rets contracts body) = strace opts ("pp procedure " ++ show name) $ do
--    when (isLeakFunName name) $ addExemption name
    -- add procedure modifies list
    bools <- mapM (liftM not . isExemptType . itwType) args
    rbools <- mapM (liftM not . isExemptType . itwType) rets
    let (ids,leak) = ppContracts opts contracts
    let (body',leaks) = ppMaybeBody opts ids body
    State.modify $ \st -> st { procedures = Map.insertWith mergeProcs name (bools,rbools,ids,leak `mappend` leaks) (procedures st) }
    let contracts' = gReplaceCanCall opts contracts
    return $ ProcedureDecl atts name targs args rets contracts' body'
ppDecl opts (ImplementationDecl atts name targs args rets body) = strace opts ("pp implementation " ++ show name) $ do
--    when (isLeakFunName name) $ addExemption name
    bools <- mapM (liftM not . isExemptType . snd) args
    rbools <- mapM (liftM not . isExemptType . snd) rets
    let ids = Set.empty
    let (body',leaks) = ppBodies opts ids body
    State.modify $ \st -> st { procedures = Map.insertWith mergeProcs name (bools,rbools,ids,leaks) (procedures st) }
    return $ ImplementationDecl atts name targs args rets body'
ppDecl opts d@(FunctionDecl atts name targs args ret body) = strace opts ("pp function " ++ show name) $ do
--    when (isLeakFunName name) $ addExemption name
    State.modify $ \st -> st { functions = Map.insert name (map (isPrivateFArg opts) args) (functions st) }
    return d
ppDecl opts d@(AxiomDecl atts e) = strace opts ("pp axiom ") $ do
    let atts' = if hasLeakageFunAnn opts e then Attribute "leakage" [] : atts else atts
    return $ AxiomDecl atts' e
ppDecl opts d = return d

isPrivateFArg :: Options -> FArg -> Bool
isPrivateFArg opts (Nothing,_) = True
isPrivateFArg opts (Just i,_) = isLeakVarName opts i

ppContracts :: Options -> [Either Comment Contract] -> (Set Id,Leakage)
ppContracts opts [] = (mempty,mempty) 
ppContracts opts (c:cs) = (m `mappend` ms,leak `mappend` leaks)
    where
    (m,leak) = ppContract opts c
    (ms,leaks) = ppContracts opts cs
ppContract :: Options -> Either Comment Contract -> (Set Id,Leakage)
ppContract opts (Left c) = (Set.empty,mempty)
ppContract opts (Right c@(Modifies _ ids)) = (Set.fromList ids,mempty)
ppContract opts (Right c@(Requires _ e)) = (mempty,Leakage (publicIds opts e) mempty)
ppContract opts (Right c@(Ensures _ e)) = (mempty,Leakage (publicIds opts e) mempty)

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

isExempt :: MonadIO m => Options -> Id -> ShadowM m Bool
isExempt opts i = do
    m <- liftM exemptions State.get
    let b = Set.member i m
    strace opts (show $ text "isExempt" <+> pretty i <+> pretty b) $ return b

unlessExempt :: MonadIO m => Options -> a -> Id -> ShadowM m [a] -> ShadowM m [a]
unlessExempt opts x i m = do
    is <- isExempt opts i
    if is then return [x] else m

unlessExemptFVS :: (MonadIO m,FVS a) => a -> x -> ShadowM m x -> ShadowM m x
unlessExemptFVS x def m = unlessExemptFVS' x def id m

unlessExemptFVS' :: (MonadIO m,FVS a) => a -> x -> (Bool -> Bool) -> ShadowM m x -> ShadowM m x
unlessExemptFVS' x def f m = do
    exs <- liftM exemptions State.get
    let vs = fvs x
    if (f $ Set.null (Set.difference vs exs)) then return def else m

shadowProgram :: MonadIO m => Options -> Program -> ShadowM m Program
shadowProgram opts (Program decls) = do
    decls' <- concatMapM (shadowCommentOrDecl opts) decls
    return $ Program decls'

shadowCommentOrDecl :: MonadIO m => Options -> Either Comment Decl -> ShadowM m [Either Comment Decl]
shadowCommentOrDecl opts (Left c) = return [Left c]
shadowCommentOrDecl opts (Right d) = do
    ds' <- shadowDecl opts d 
    return $ map Right ds'

shadowDecl :: MonadIO m => Options -> Decl -> ShadowM m [Decl]
shadowDecl opts (Pos p d) = do
    ds' <- shadowBareDecl opts d
    return $ map (Pos p) ds'

boolToDual :: Bool -> Maybe Bool
boolToDual False = Nothing
boolToDual True = Just True

shadowBareDecl :: MonadIO m => Options -> BareDecl -> ShadowM m [BareDecl]
shadowBareDecl opts d@(TypeDecl {}) = return [d]
shadowBareDecl opts (VarDecl atts ids) = do -- duplicate global variables
    atts' <- concatMapM (shadowAttribute opts True) atts
    bools <- mapM (liftM not . isExemptType . itwType) ids
    ids' <- concatMapM (uncurry (shadowIdTypeWhere opts)) $ zip (map boolToDual bools) ids
    return [VarDecl atts' ids']
shadowBareDecl opts d@(ConstantDecl atts unique ids t orderSpec complete) = do -- duplicate global constants
    atts' <- concatMapM (shadowAttribute opts True) atts
    orderSpec' <- shadowParentInfo opts orderSpec
    ids' <- concatMapM (shadowConstId opts) ids
    return [ConstantDecl atts' unique ids' t orderSpec' complete]
shadowBareDecl opts d@(AxiomDecl atts e) = if hasLeakageAtt atts
    then do
        atts' <- concatMapM (shadowAttribute opts True) atts
        e' <- shadowExpression opts DualE e
        return [AxiomDecl atts' e']
    else do
        atts' <- concatMapM (shadowAttribute opts False) $ atts
        e' <- shadowExpression opts ShadowE $ e
        return [removeLeakageAnns opts True d,AxiomDecl atts' e']
shadowBareDecl opts d@(ProcedureDecl atts name targs args rets contracts body) = strace opts ("shadowing procedure " ++ show (pretty name)) $ shadowLocal $ unlessExempt opts d name $ if isLeakFunName opts name
    then do
        (bools,rbools,modifies,leaks) <- getProcedure name
        name' <- shadowId opts DualE name
        atts' <- concatMapM (shadowAttribute opts True) atts
        -- duplicate parameters, returns and contracts
        args' <- concatMapM (uncurry $ shadowIdTypeWhere opts) $ zip (map boolToDual bools) args
        rets' <- concatMapM (uncurry $ shadowIdTypeWhere opts) $ zip (map boolToDual rbools) rets
        contracts' <- concatMapM (shadowCommentOrContract opts name DualE) contracts
        
        -- create a fresh shadow assertion variable
        shadow_ok <- freshVariable "shadow_ok"
        -- declare shadow_ok at the start
        let defShadow = IdTypeWhere shadow_ok BoolType $ Pos noPos tt
        let initShadow = Pos noPos $ Assign [(shadow_ok,[])] [posTT]
        
        State.modify $ \st -> st { shadowOk = Just shadow_ok }
        body' <- mapM (shadowBody opts modifies leaks True) body
        State.modify $ \st -> st { shadowOk = Nothing }
        
        let d' = ProcedureDecl atts' name' targs args' rets' contracts' (addMaybeBody defShadow initShadow body')
        return [d']
    else do
        (bools,rbools,modifies,leaks) <- getProcedure name
        name' <- shadowId opts ShadowE name
        atts' <- concatMapM (shadowAttribute opts False) atts
        -- duplicate parameters, returns and contracts
        args' <- concatMapM (shadowIdTypeWhere opts $ Just False) args
        rets' <- concatMapM (shadowIdTypeWhere opts $ Just False) rets
        contracts' <- concatMapM (shadowCommentOrContract opts name ShadowE) contracts
        
        body' <- mapM (shadowBody opts modifies leaks False) body
        
        let d' = ProcedureDecl atts' name' targs args' rets' contracts' (body')
        return [removeLeakageAnns opts True d,d']
shadowBareDecl opts d@(ImplementationDecl atts name targs args rets body) = strace opts ("entering implementation " ++ show (pretty name)) $ shadowLocal $ unlessExempt opts d name $ if isLeakFunName opts name
    then strace opts ("generating product implementation for " ++ show (pretty name)) $ do
        (bools,rbools,modifies,leaks) <- getProcedure name
        name' <- shadowId opts DualE name
        atts' <- concatMapM (shadowAttribute opts True) atts
        args' <- concatMapM (uncurry $ shadowIdType opts) $ zip bools args
        rets' <- concatMapM (uncurry $ shadowIdType opts) $ zip rbools rets
        
        -- create a fresh shadow assertion variable
        shadow_ok <- freshVariable "shadow_ok"
        -- declare shadow_ok at the start
        let defShadow = IdTypeWhere shadow_ok BoolType $ Pos noPos tt
        let initShadow = Pos noPos $ Assign [(shadow_ok,[])] [posTT]
        
        State.modify $ \st -> st { shadowOk = Just shadow_ok }
        body' <- mapM (shadowBody opts modifies leaks True) body
        State.modify $ \st -> st { shadowOk = Nothing }
            
        let d' = ImplementationDecl atts' name' targs args' rets' (addBodies defShadow initShadow body')
        return [d']
    else strace opts ("shadowing implementation of " ++ show (pretty name)) $ do
        (bools,rbools,modifies,leaks) <- getProcedure name
        name' <- shadowId opts ShadowE name
        atts' <- concatMapM (shadowAttribute opts False) atts
        args' <- concatMapM (shadowIdType opts False) args
        rets' <- concatMapM (shadowIdType opts False) rets
        
        body' <- mapM (shadowBody opts modifies leaks False) body
            
        let d' = ImplementationDecl atts' name' targs args' rets' (body')
        return [removeLeakageAnns opts True d,d']
shadowBareDecl opts d@(FunctionDecl atts name targs args ret body) = strace opts ("shadowing function " ++ show (pretty name)) $ shadowLocal $ unlessExempt opts d name $ if isLeakFunName opts name
    then do
        atts' <- concatMapM (shadowAttribute opts False) atts
        name' <- shadowId opts DualE name
        bools <- liftM (lookupMap name . functions) State.get
        args' <- concatMapM (uncurry (shadowFArg opts)) (zip bools args)
        [ret'] <- shadowFArg opts False ret
        body' <- mapM (shadowExpression opts DualE) body
        let d' = FunctionDecl atts' name' targs args' ret' body'
        return [d']
    else do
        atts' <- concatMapM (shadowAttribute opts False) atts
        name' <- shadowId opts ShadowE name
        args' <- concatMapM (shadowFArg opts False) args
        [ret'] <- shadowFArg opts False ret
        body' <- mapM (shadowExpression opts ShadowE) body
        let d' = FunctionDecl atts' name' targs args' ret' body'
        return [removeLeakageAnns opts True d,d']

getProcedure :: MonadIO m => Id -> ShadowM m ([Bool],[Bool],Set Id,Leakage)
getProcedure proc = do
    xs <- liftM procedures State.get
    case Map.lookup proc xs of
        Nothing -> error $ "procedure not found: " ++ show proc
        Just x -> return x

shadowBody :: MonadIO m => Options -> Set Id -> Leakage -> Bool -> Body -> ShadowM m Body
shadowBody opts modifies leaks isDual (vars,block) = do    
    -- duplicate local variables
    let shadowArg (atts,itws) = do
        atts' <- concatMapM (shadowAttribute opts isDual) atts
        bools <- mapM (liftM not . isExemptType . itwType) itws
        itws' <- if isDual
            then concatMapM (uncurry (shadowIdTypeWhere opts)) $ zip (map boolToDual bools) itws
            else concatMapM (shadowIdTypeWhere opts $ Just False) itws
        return (atts',itws')
    vars' <- mapM shadowArg vars
    block' <- shadowBlock opts modifies leaks isDual block
    return (vars',block')

isExemptType :: MonadIO m => Type -> ShadowM m Bool
isExemptType t = do
    f <- liftM typeExemptions State.get
    return $ f t

addBodies :: IdTypeWhere -> Statement -> [Body] -> [Body]
addBodies def init [] = [([([],[def])],[])]
addBodies def init (b:bs) = addBody def init b : bs

addBody :: IdTypeWhere -> Statement -> Body -> Body
addBody def init (defs,b) = (([],[def]):defs,Right (Pos noPos ([],init)) : b)

addMaybeBody :: IdTypeWhere -> Statement -> Maybe Body -> Maybe Body
addMaybeBody def init Nothing = Nothing
addMaybeBody def init (Just b) = Just $ addBody def init b

shadowBlock :: MonadIO m => Options -> Set Id -> Leakage -> Bool -> Block -> ShadowM m Block
shadowBlock opts modifies leaks isDual b = do
    -- assumes that it is already a basic block
    let bb = toBasicBlocks' b
    bb' <- shadowBasicBlocks opts modifies leaks isDual bb
    if isDual
        then do
            -- assert shadow_ok before the last return
            Just shadow_ok <- liftM shadowOk State.get
            let assert = Predicate [] $ SpecClause Inline False $ Pos noPos $ Var shadow_ok
            let bb'' = updLast (\(l,ss) -> (l,Right (Pos noPos assert) : ss)) bb'
            return (fromBasicBlocks bb'')
        else return (fromBasicBlocks bb')

shadowBasicBlocks :: MonadIO m => Options -> Set Id -> Leakage -> Bool -> [BasicBlock] -> ShadowM m [BasicBlock]
shadowBasicBlocks opts modifies leaks True bs = strace opts ("shadowBasicBlocks") $ do
    bbs <- lift $ flattenBasicBlocks bs (fst $ last bs)
    bbs' <- forM bbs $ \(bb,next) -> do
        let doFull = isBenign leaks bb && length bb > 1
        if doFull
            then fprodBasicBlocks opts (startLabelBBs bb) next bb -- full product: backward leakage analysis
            else prodBasicBlocks opts DualE bb -- simple product: forward leakage analysis
    return $ concat bbs'
shadowBasicBlocks opts modifies leaks False bs = do
    bbs <- lift $ flattenBasicBlocks bs (fst $ last bs)
    bbs' <- forM bbs $ \(bb,next) -> prodBasicBlocks opts ShadowE bb
    return $ concat bbs'

shadowCommentOrContract :: MonadIO m => Options -> Id -> ShadowEMode -> Either Comment Contract -> ShadowM m [Either Comment Contract]
shadowCommentOrContract opts proc mode (Left c) = return [Left c]
shadowCommentOrContract opts proc mode (Right c) = do
    cs' <- shadowContract opts proc mode c
    return $ map Right cs'

shadowContract :: MonadIO m => Options -> Id -> ShadowEMode -> Contract -> ShadowM m [Contract]
shadowContract opts proc DualE c@(Requires free e) | hasLeakageFunAnn opts e = do
    e' <- shadowExpression opts DualE e
    return [Requires free e']
shadowContract opts proc DualE c@(Requires free e) | not (hasLeakageFunAnn opts e) = do
    e' <- shadowExpression opts ShadowE e
    return [removeLeakageAnns opts True c,Requires free e']
shadowContract opts proc ShadowE c@(Requires free e) | not (hasLeakageFunAnn opts e) = do
    e' <- shadowExpression opts ShadowE e
    return [Requires free e']
shadowContract opts proc ShadowDualE c@(Requires free e) = do
    e' <- shadowExpression opts ShadowDualE e
    return [removeLeakageAnns opts True c,Requires free e']
shadowContract opts proc DualE c@(Ensures free e) | hasLeakageFunAnn opts e = do
    e' <- shadowExpression opts DualE e
    return [Ensures free e']
shadowContract opts proc DualE c@(Ensures free e) | not (hasLeakageFunAnn opts e) = do
    e' <- shadowExpression opts ShadowE e
    return [removeLeakageAnns opts True c,Ensures free e']
shadowContract opts proc ShadowE c@(Ensures free e) | not (hasLeakageFunAnn opts e) = do
    e' <- shadowExpression opts ShadowE e
    return [Ensures free e']
shadowContract opts proc ShadowDualE c@(Ensures free e) = do
    e' <- shadowExpression opts ShadowDualE e
    return [removeLeakageAnns opts True c,Ensures free e']
shadowContract opts proc mode c@(Modifies free ids) = do
    ids' <- mapM (shadowId opts mode) ids
    return [Modifies free (List.nub $ (if isDualMode mode then ids else [])++ids')]
shadowContract opts proc mode c = error $ show $ text "shadowContract:" <+> text (show mode) <+> pretty c

shadowConstId :: MonadIO m => Options -> Id -> ShadowM m [Id]
shadowConstId opts i = do
    addVariable i
    unlessExempt opts i i $ liftM (\x -> [i,x]) (shadowId opts ShadowE i)

shadowParentInfo :: MonadIO m => Options -> ParentInfo -> ShadowM m ParentInfo
shadowParentInfo opts = mapM (mapM (mapSndM (shadowId opts ShadowE)))

shadowFArg :: MonadIO m => Options -> Bool -> FArg -> ShadowM m [FArg]
shadowFArg opts False a@(Nothing,t) = return [(Nothing,t)]
shadowFArg opts True a@(Nothing,t) = return [(Nothing,t),(Nothing,t)]
shadowFArg opts False a@(Just i,t) = do
    --when (isLeakVarName opts i) $ error $ show $ text "shadowFArg: leakage variable not supported" <+> pretty a
    addVariable i
    addExemption opts i
    return [(Just i,t)]
shadowFArg opts True a@(Just i,t) = if isLeakVarName opts i
    then do
        addVariable i
        i' <- shadowId opts ShadowE i
        addVariable i'
        return [(Just i,t),(Just i',t)]
    else do
        addVariable i
        addExemption opts i
        return [(Just i,t)]

shadowIdType :: MonadIO m => Options -> Bool -> IdType -> ShadowM m [IdType]
shadowIdType opts False it@(i,t) = do -- if the type is exempt, then the variable is exempt
    addVariable i
    addExemption opts i
    return [removeLeakageAnns opts True it]
shadowIdType opts True it@(i,t) = do
    addVariable i
    unlessExempt opts it i $ do
        i' <- shadowId opts ShadowE i
        return [removeLeakageAnns opts True it,(i',t)]

shadowIdTypeWhere :: MonadIO m => Options -> Maybe Bool -> IdTypeWhere -> ShadowM m [IdTypeWhere]
shadowIdTypeWhere opts Nothing itw@(IdTypeWhere i t w) = do
    addVariable i
    addExemption opts i
    return [removeLeakageAnns opts True itw]
shadowIdTypeWhere opts (Just doDual) itw@(IdTypeWhere i t w) = do
    addVariable i
    unlessExempt opts itw i $ do
        i' <- shadowId opts ShadowE i
        w' <- shadowExpression opts ShadowE w
        if doDual
            then return [removeLeakageAnns opts True itw,IdTypeWhere i' t w']
            else return [IdTypeWhere i' t w']

shadowId :: MonadIO m => Options -> ShadowEMode -> Id -> ShadowM m Id
shadowId opts mode@(isDualE -> False) i = do
    exempt <- isExempt opts i
    if exempt then return i else return (i++".shadow")
shadowId opts DualE i = do
    exempt <- isExempt opts i
    if exempt then return i else return (i++".dual")

shadowExpression :: MonadIO m => Options -> ShadowEMode -> Expression -> ShadowM m Expression
shadowExpression opts m (Pos p e) = do
    e' <- shadowBareExpression p opts m e
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

isShadowM mode ShadowE = True
isShadowM mode ShadowDualE = True
isShadowM mode _ = False

shadowDuals :: MonadIO m => (a -> ShadowM m a) -> [Bool] -> [a] -> ShadowM m [a]
shadowDuals f [] [] = return []
shadowDuals f (False:bs) (e:es) = do
    es' <- shadowDuals f bs es
    return (e:es')
shadowDuals f (True:bs) (e:es) = do
    e' <- f e
    es' <- shadowDuals f bs es
    return (e:e':es')
shadowDuals f bs es = error "shadowDuals: mismatching arguments"

shadowBareExpression :: MonadIO m => SourcePos -> Options -> ShadowEMode -> BareExpression -> ShadowM m BareExpression
shadowBareExpression p opts mode (isLeakageExpr opts -> Just e') = shadowBareExpression p opts mode e'
shadowBareExpression p opts mode (isFreeExpr opts -> Just e') = shadowBareExpression p opts mode e'
shadowBareExpression p opts ShadowE e | hasLeakageFunAnn opts e = error $ show $ text (show p) <+> text "unsupported leakage expression" <+> pretty e <+> text "in ShadowE mode"
shadowBareExpression p opts DualE e | not (hasLeakageFunAnn opts e) = strace opts ("shadowing a non-leakage expression " ++ show (pretty e)) $ do
    e' <- shadowBareExpression p opts ShadowE e
    return $ BinaryExpression And (Pos noPos $ gReplaceFrees opts e) (Pos noPos e')
shadowBareExpression p opts (isDualMode -> True) e@(Application n@(isLeakFunName opts -> True) es) = do
    n' <- shadowId opts DualE n
    bools <- liftM (lookupMap n . functions) State.get
    es' <- shadowDuals (shadowExpression opts ShadowE) bools es
    return $ Application n' es'
shadowBareExpression p opts (isDualMode -> True) e@(isLeakExpr opts -> Just l) = do
    lShadow <- shadowBareExpression p opts ShadowE l
    return $ BinaryExpression Eq (Pos noPos $ gReplaceFrees opts l) (Pos noPos lShadow)
shadowBareExpression p opts m e@(isPublicExpr opts -> Just (l,PublicMid)) = do
    doFull <- State.gets fullProd
    if doFull
        then error "public mid expression not supported"
        else do
            lShadow <- shadowBareExpression p opts ShadowE l
            return $ BinaryExpression Eq (Pos noPos $ gReplaceFrees opts l) (Pos noPos lShadow)
shadowBareExpression p opts (isDualMode -> True) e@(isPublicExpr opts -> Just (l,_)) = do
    lShadow <- shadowBareExpression p opts ShadowE l
    return $ BinaryExpression Eq (Pos noPos $ gReplaceFrees opts l) (Pos noPos lShadow)
shadowBareExpression p opts mode e@(isDeclassifiedExpr opts -> Just (_,True)) = error $ show p ++ ": declassified out expression not supported in " ++ show mode ++ " " ++ show (pretty e)
shadowBareExpression p opts (isDualMode -> True) e@(isDeclassifiedExpr opts -> Just (l,False)) = do
    lShadow <- shadowBareExpression p opts ShadowE l
    return $ BinaryExpression Eq (Pos noPos $ gReplaceFrees opts l) (Pos noPos lShadow)
shadowBareExpression p opts (isDualE -> False) e@(Literal {}) = return e
shadowBareExpression p opts (isDualE -> False) (Var i) = do
    i' <- shadowId opts ShadowE i
    return $ Var i'
shadowBareExpression p opts (isDualE -> False) e@(Logical {}) = return e
shadowBareExpression p opts (isDualE -> False) (Old e) = do
    e' <- shadowExpression opts ShadowE e
    return $ Old e'
shadowBareExpression p opts m (Coercion e t) = do
    e' <- shadowExpression opts m e
    return $ Coercion e' t
shadowBareExpression p opts m (UnaryExpression o e) = do
    e' <- shadowExpression opts m e
    return $ UnaryExpression o e'
shadowBareExpression p opts m (BinaryExpression o e1 e2) = do
    e1' <- shadowExpression opts m e1
    e2' <- shadowExpression opts m e2
    return $ BinaryExpression o e1' e2'
shadowBareExpression p opts DualE e@(Application name@(isLeakFunName opts -> False) es) = do
    name' <- shadowId opts ShadowE name
    es' <- mapM (shadowExpression opts ShadowDualE) es
    let e' = Application name' es'
    return $ BinaryExpression Eq (Pos noPos $ removeLeakageAnns opts True e) (Pos noPos e')
shadowBareExpression p opts ShadowDualE e@(Application name@(isLeakFunName opts -> False) es) = do
    name' <- shadowId opts ShadowE name
    es' <- mapM (shadowExpression opts ShadowDualE) es
    return $ Application name' es'
shadowBareExpression p opts ShadowE e@(Application name@(isLeakFunName opts -> False) es) = do
    name' <- shadowId opts ShadowE name
    es' <- mapM (shadowExpression opts ShadowE) es
    return $ Application name' es'
shadowBareExpression p opts mode (MapSelection m es) = do
    m' <- shadowExpression opts mode m
    es' <- mapM (shadowExpression opts mode) es
    return $ MapSelection m' es'
shadowBareExpression p opts mode (MapUpdate m es r) = do
    m' <- shadowExpression opts mode m
    es' <- mapM (shadowExpression opts mode) es
    r' <- shadowExpression opts mode r
    return $ MapUpdate m' es' r'
shadowBareExpression p opts m@(isDualE -> False) (Quantified o alphas args trggs e) = withExemptions $ do
    let add (v,t) = do
        addVariable v
        addExemption opts v
    mapM_ add args
    trggs' <- concatMapM (shadowQTriggerAttribute opts False (map fst args)) trggs
    e' <- shadowExpression opts m e
    return $ Quantified o alphas args trggs' e'
shadowBareExpression p opts DualE (Quantified o alphas args trggs e) = withExemptions $ do
    let add (v,t) = if isLeakVarName opts v
        then do
            addVariable v
            v' <- shadowId opts ShadowE v
            addVariable v'
            return [(v,t),(v',t)]
        else do
            addVariable v
            addExemption opts v
            return [(v,t)]
    args' <- concatMapM add args
    trggs' <- concatMapM (shadowQTriggerAttribute opts True (map fst args)) trggs
    e' <- shadowExpression opts DualE e
    return $ Quantified o alphas args' trggs' e'
shadowBareExpression p opts ShadowE (IfExpr c e1 e2) = do
    c' <- shadowExpression opts ShadowE c
    e1' <- shadowExpression opts ShadowE e1
    e2' <- shadowExpression opts ShadowE e2
    return $ IfExpr c' e1' e2'
shadowBareExpression p opts m e = error $ show $ text (show p) <+> text "expression" <+> pretty e <+> text "not supported in mode" <+> text (show m)

shadowQTriggerAttribute :: MonadIO m => Options -> Bool -> [Id] -> QTriggerAttribute -> ShadowM m [QTriggerAttribute]
shadowQTriggerAttribute opts True vars t@(Left trggs) = do
    let sha e = if hasLeakageAnn opts e
                    then liftM (:[]) (shadowExpression opts DualE $ removeLeakageAnns opts False e)
                    else liftM (\e' -> [e,e']) (shadowExpression opts ShadowE $ removeLeakageAnns opts True e)
    liftM (maybe [] ((:[]) . Left) . cleanTrigger (Just vars)) $ concatMapM sha trggs
shadowQTriggerAttribute opts False vars t@(Left trggs) = do
    let sha e = liftM (:[]) (shadowExpression opts ShadowE $ removeLeakageAnns opts True e)
    liftM (maybe [] ((:[]) . Left) . cleanTrigger (Just vars)) $ concatMapM sha trggs
shadowQTriggerAttribute opts doDual vars t@(Right att) = do
    atts <- (shadowAttribute opts doDual) att
    return $ map Right atts

-- product
prodBasicBlocks :: MonadIO m => Options -> ShadowEMode -> [BasicBlock] -> ShadowM m [BasicBlock]
prodBasicBlocks opts mode bs = strace opts ("prodBasicBlocks") $ mapM (shadowBasicBlock opts mode) bs

shadowBasicBlock :: MonadIO m => Options -> ShadowEMode -> BasicBlock -> ShadowM m BasicBlock
shadowBasicBlock opts ShadowDualE (l,ss) = do
    ss' <- concatMapM (shadowCommentOrStatement opts ShadowDualE) ss
    l' <- shadowId opts ShadowE l
    return (l',ss')
shadowBasicBlock opts ShadowE (l,ss) = do
    ss' <- concatMapM (shadowCommentOrStatement opts ShadowE) ss
    return (l,ss')
shadowBasicBlock opts DualE (l,ss) = do
    ss' <- concatMapM (shadowCommentOrStatement opts DualE) ss
    return (l,ss')

shadowCommentOrStatement :: MonadIO m => Options -> ShadowEMode -> Either Comment Statement -> ShadowM m [Either Comment Statement]
shadowCommentOrStatement opts mode (Left c) = return [Left c]
shadowCommentOrStatement opts mode (Right s) = do
    ss' <- shadowStatement opts mode s
    return $ map Right ss'

shadowStatement :: MonadIO m => Options -> ShadowEMode -> Statement -> ShadowM m [Statement]
shadowStatement opts mode (Pos p s) = do
    liftM (map (Pos p)) $ shadowBareStatement p opts mode s

shadowBareStatement :: MonadIO m => SourcePos -> Options -> ShadowEMode -> BareStatement -> ShadowM m [BareStatement]
shadowBareStatement p opts mode s@(Havoc ids) = do
    ids' <- mapM (shadowId opts ShadowE) ids
    let s' = Havoc ids'
    if isDualE mode then return [removeLeakageAnns opts True s,s'] else return [s']
shadowBareStatement p opts mode Skip = return [Skip]
shadowBareStatement p opts DualE s@(Goto ids) = return [s]
shadowBareStatement p opts ShadowE s@(Goto ids) = return [s]
shadowBareStatement p opts ShadowDualE s@(Goto ids) = do
    ids' <- mapM (shadowId opts ShadowE) ids
    return [Goto ids']
shadowBareStatement p opts mode pr@(Predicate atts spec) = do
    ps' <- strace opts ("shadowPredicate " ++ show mode ++ " " ++ show (pretty pr)) $ shadowPredicate p opts mode pr
    return ps'
shadowBareStatement p opts mode s@(Assign lhs rhs) = do
    let shadowLhs (i,ess) = do
        i' <- shadowId opts ShadowE i
        ess' <- mapM (mapM (shadowExpression opts ShadowE)) ess
        return (i',ess')
    lhs' <- mapM shadowLhs lhs
    let mode' = if isDualE mode then ShadowDualE else ShadowE
    rhs' <- mapM (shadowExpression opts mode') rhs
    let s' = Assign lhs' rhs'
    if isDualE mode
        then return [removeLeakageAnns opts True s,s']
        else return [s']
shadowBareStatement p opts ShadowDualE s@(Call atts is name es) = do -- shadow arguments
    name' <- shadowId opts ShadowE name
    is' <- mapM (shadowId opts DualE) is
    atts' <- concatMapM (shadowAttribute opts False) atts
    es' <- mapM (shadowExpression opts ShadowDualE) es
    let s' = Call atts' is' name' es'
    return [s']
shadowBareStatement p opts DualE s@(Call atts is name es) | isLeakFunName opts name = strace opts ("shadow statement DualE leakage " ++ show (pretty s)) $ do -- duplicate call arguments
    (bools,rbools,_,_) <- getProcedure name
    is' <- shadowDuals (shadowId opts ShadowE) rbools is
    name' <- shadowId opts DualE name
    atts' <- concatMapM (shadowAttribute opts True) atts
    es' <- shadowDuals (shadowExpression opts ShadowDualE) bools es
    let s' = Call atts' is' name' es'
    return [s']
shadowBareStatement p opts DualE s@(Call atts is name es) | not (isLeakFunName opts name) = strace opts ("shadow statement DualE nonleakage " ++ show (pretty s)) $ do -- duplicate call
    is' <- mapM (shadowId opts ShadowE) is
    name' <- shadowId opts ShadowE name
    atts' <- concatMapM (shadowAttribute opts False) atts
    es' <- mapM (shadowExpression opts ShadowDualE) es
    let s' = Call atts' is' name' es'
    return [s,s']
shadowBareStatement p opts ShadowE s@(Call atts is name es) | not (isLeakFunName opts name) = strace opts ("shadow statement ShadowE " ++ show (pretty s)) $ do -- shadow call arguments
    is' <- mapM (shadowId opts ShadowE) is
    name' <- shadowId opts ShadowE name
    atts' <- concatMapM (shadowAttribute opts False) atts
    es' <- mapM (shadowExpression opts ShadowE) es
    let s' = Call atts' is' name' es'
    return [s']
shadowBareStatement p opts ShadowDualE s@(CallForall i es) = do
    i' <- shadowId opts ShadowDualE i
    es' <- mapM (shadowWildcardExpression opts ShadowDualE) es
    let s' = CallForall i' es'
    return [s']
shadowBareStatement p opts ShadowE s@(CallForall i es) = do
    i' <- shadowId opts ShadowE i
    es' <- mapM (shadowWildcardExpression opts ShadowE) es
    let s' = CallForall i' es'
    return [s']
shadowBareStatement p opts DualE s@(CallForall i es) = do
    i' <- shadowId opts ShadowE i
    es' <- mapM (shadowWildcardExpression opts ShadowDualE) es
    let s' = CallForall i' es'
    return [removeLeakageAnns opts True s,s']
shadowBareStatement p opts mode Return = return [Return]
shadowBareStatement p opts mode (Break {}) = error "shadowBareStatement: Break"
shadowBareStatement p opts mode (If {}) = error "shadowBareStatement: If"
shadowBareStatement p opts mode (While {}) = error "shadowBareStatement: While"

shadowDual :: (MonadIO m,Data a) => Options -> (a -> ShadowM m a) -> (a -> ShadowM m [a])
shadowDual opts m x = do
    x' <- m x
    return [removeLeakageAnns opts True x,x']

shadowAttribute :: MonadIO m => Options -> Bool -> Attribute -> ShadowM m [Attribute]
shadowAttribute opts doDual (Attribute tag vals) = do
    liftM (map (Attribute tag)) $ mapM (shadowAttrVal opts doDual) vals
  where
    shadowAttrVal :: MonadIO m => Options -> Bool -> AttrValue -> ShadowM m [AttrValue]
    shadowAttrVal opts False v@(EAttr e) = do
        v' <- liftM EAttr $ shadowExpression opts ShadowE $ removeLeakageAnns opts True e
        return $ cleanAttrVals Nothing [v']
    shadowAttrVal opts True v@(EAttr e) = if hasLeakageAnn opts e
        then do
            v' <- liftM EAttr $ shadowExpression opts DualE $ removeLeakageAnns opts False e
            return $ cleanAttrVals Nothing [v']
        else do
            v' <- liftM EAttr $ shadowExpression opts ShadowE $ removeLeakageAnns opts True e
            if doDual
                then return $ cleanAttrVals Nothing [removeLeakageAnns opts True v,v']
                else return $ cleanAttrVals Nothing [v']
    shadowAttrVal opts _ (SAttr s) = return [SAttr s]

shadowWildcardExpression :: MonadIO m => Options -> ShadowEMode -> WildcardExpression -> ShadowM m WildcardExpression
shadowWildcardExpression opts m Wildcard = return Wildcard
shadowWildcardExpression opts m (Expr e) = do
    e' <- shadowExpression opts m e
    return $ Expr e'

freePred :: Options -> BareStatement -> BareStatement
freePred opts p@(Predicate atts spec@(SpecClause st isAssume (Pos l e))) = case isFreeExpr opts e of
    Just e' -> (Predicate atts (SpecClause st True (Pos l e')))
    Nothing -> p

leakagePred :: Options -> BareStatement -> Maybe BareStatement
leakagePred opts (freePred opts -> p@(Predicate atts spec@(SpecClause st isAssume (Pos l e)))) = case isLeakageExpr opts e of
    Nothing -> if hasLeakageAtt atts || hasLeakageFunAnn opts e then Just p else Nothing
    Just e' -> Just $ Predicate atts (SpecClause st isAssume (Pos l e'))

shadowPredicate :: MonadIO m => SourcePos -> Options -> ShadowEMode -> BareStatement -> ShadowM m [BareStatement]
shadowPredicate p opts mode@(isDualMode -> True) s@(leakagePred opts -> Just (Predicate atts spec@(SpecClause st isAssume (Pos _ (isPublicExpr opts -> Just (l,ty)))))) = do
    l' <- shadowBareExpression p opts ShadowE l
    Just shadow_ok <- liftM shadowOk State.get
    let implies = case ty of
                    PublicMid -> if isDualE mode then id else Pos noPos . BinaryExpression Implies (Pos noPos $ Var shadow_ok)
                    otherwise -> id
    let e' = Pos noPos $ BinaryExpression Eq (Pos noPos l) (Pos noPos l')
    let spec' = SpecClause st isAssume $ implies e'
    return [Predicate atts spec']
shadowPredicate p opts mode@(isDualMode -> True) s@(leakagePred opts -> Just (Predicate atts spec@(SpecClause st False (Pos _ (isDeclassifiedExpr opts -> Just (l,ty)))))) = do
    l' <- shadowBareExpression p opts ShadowE l
    let e' = Pos noPos $ BinaryExpression Eq (Pos noPos l) (Pos noPos l')
    if ty
        then do -- delay assertion of equality
            Just shadow_ok <- liftM shadowOk State.get
            return [Assign [(shadow_ok,[])] [Pos noPos $ BinaryExpression And (Pos noPos $ Var shadow_ok) e'] ]
        else do -- in-place assertion of equality
            return [Predicate atts $ SpecClause st False e']
shadowPredicate p opts mode@(isDualMode -> True) pr@(leakagePred opts -> Just (Predicate atts (SpecClause st isAssume e))) = do
    e' <- shadowExpression opts DualE e
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute opts True) atts
    let pr' = Predicate atts' s'
    return [pr']
shadowPredicate p opts mode@(isDualMode -> False) pr@(leakagePred opts -> Just (Predicate atts (SpecClause st isAssume e))) = strace opts ("shadow non-leakage predicate " ++ show (pretty pr)) $ do
    e' <- shadowExpression opts ShadowE e
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute opts False) atts
    let pr' = Predicate atts' s'
    if isDualE mode then return [removeLeakageAnns opts True pr,pr'] else return [pr']
shadowPredicate p opts mode pr@(freePred opts -> Predicate atts (SpecClause st isAssume e)) | isNothing (leakagePred opts pr) = do
    e' <- shadowExpression opts ShadowE e
    let opr = Predicate atts (SpecClause st isAssume e)
    let s' = SpecClause st isAssume e'
    atts' <- concatMapM (shadowAttribute opts False) atts
    let pr' = Predicate atts' s'
    if isDualE mode then return [removeLeakageAnns opts True opr,pr'] else return [pr']

-- normal program with the last goto replaced pointing to the shadow label and annotations removed
redirectBasicBlock :: Options -> Maybe Id -> Id -> BasicBlock -> BasicBlock
redirectBasicBlock opts next startShadow (l,ss) = (l,concatMap redirectCommentOrStatement ss)
    where
    redirectCommentOrStatement :: Either Comment Statement -> [Either Comment Statement]
    redirectCommentOrStatement (Left c) = [Left c]
    redirectCommentOrStatement (Right s) = map Right $ redirectStatement s
    redirectStatement :: Statement -> [Statement]
    redirectStatement (Pos p s) = map (Pos p) (redirectBareStatement s)
    redirectBareStatement :: BareStatement -> [BareStatement]
    redirectBareStatement (Goto [l]) | Just l == next = [Goto [startShadow]]
    redirectBareStatement x = [removeLeakageAnns opts True x]

-- full product
fprodBasicBlocks :: MonadIO m => Options -> Id -> Maybe Id -> [BasicBlock] -> ShadowM m [BasicBlock]
fprodBasicBlocks opts start next bs = do
    startShadow <- shadowId opts ShadowE start
    let bsRedir = map (redirectBasicBlock opts next startShadow) bs
    -- duplicated program without shadowing the final goto
    withExemptions $ do
        mapM_ (addExemption opts) next
        bsShadow <- mapM (shadowBasicBlock opts ShadowDualE) bs
        return $ bsRedir ++ bsShadow

addExemption :: MonadIO m => Options -> Id -> ShadowM m ()
addExemption opts i = strace opts ("added exemption " ++ show (pretty i)) $ State.modify $ \st -> st { exemptions = Set.insert i (exemptions st) }

addVariable :: MonadIO m => Id -> ShadowM m ()
addVariable i = State.modify $ \st -> st { variables = Set.insert i (variables st) }

freshVariable :: MonadIO m => Id -> ShadowM m Id
freshVariable v = do
    vs <- liftM variables State.get
    if Set.member v vs
        then do
            i <- incSeed
            freshVariable (v ++ "_" ++ show i)
        else addVariable v >> return v

incSeed :: MonadIO m => ShadowM m Int
incSeed = do
    i <- liftM seed State.get
    State.modify $ \st -> st { seed = succ (seed st) }
    return i

shadowLocal :: MonadIO m => ShadowM m a -> ShadowM m a
shadowLocal m = do
    st <- State.get
    x <- m
    State.modify $ \st' -> st' { variables = variables st, exemptions = exemptions st }
    return x

withExemptions :: MonadIO m => ShadowM m a -> ShadowM m a
withExemptions m = do
    st <- State.get
    x <- m
    State.modify $ \st' -> st' { exemptions = exemptions st }
    return x
