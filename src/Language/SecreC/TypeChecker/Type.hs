module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression

import Data.Traversable
import Data.Maybe
import Data.Monoid
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.List as List
import Control.Monad hiding (mapM)
import Prelude hiding (mapM)

tcTypeSpec :: Location loc => TypeSpecifier loc -> TcM loc (TypeSpecifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) = do
    (sec',tsec) <- tcMbSecTypeSpec sec 
    dta' <- tcDatatypeSpec dta
    let tdta = typed $ loc dta'
    (dim',tdim) <- tcMbDimtypeSpec dim
    let t = CType tsec tdta tdim [] -- return type without array sizes
    return $ TypeSpecifier (Typed l t) sec' dta' dim'
    
tcMbSecTypeSpec :: Location loc => Maybe (SecTypeSpecifier loc) -> TcM loc (Maybe (SecTypeSpecifier (Typed loc)),Type)
tcMbSecTypeSpec Nothing = return (Nothing,Public) -- public by default
tcMbSecTypeSpec (Just sec) = do
    sec' <- tcReaderM $ tcSecTypeSpec sec
    let t = typed $ loc sec'
    return (Just sec',t)

tcSecTypeSpec :: Location loc => SecTypeSpecifier loc -> TcReaderM loc (SecTypeSpecifier (Typed loc))
tcSecTypeSpec (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l Public)
tcSecTypeSpec (PrivateSpecifier l d) = do
    t <- checkPrivateDomain d
    let d' = fmap (flip Typed t) d
    return $ PrivateSpecifier (Typed l t) d'

tcDatatypeSpec :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier {}) = do
    b <- insideTemplate
    if b
        then tcTemplateTypeConstraint tplt
        else tcTemplateTypeResolve tplt 
tcDatatypeSpec (VariableSpecifier l v) = do
    t <- tcReaderM $ checkNonTemplateType v
    let v' = fmap (flip Typed t) v 
    return $ VariableSpecifier (Typed l t) v'

-- | Raises a template constraint
tcTemplateTypeConstraint :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcTemplateTypeConstraint (TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let t = TApp tn (map (typed . loc) args') mempty
    let cstr = TCstr (Left tn) (map (typed . loc) args')
    let l' = Typed l t
    let n' = fmap notTyped n -- we dont't type the template name, only the application
    addTemplateConstraint cstr -- add constraint to the environment
    return $ TemplateSpecifier l' n' args'

-- | Resolves a template constraint by finding a best match among the template definitions in scope.
-- Best match here means the most specific constraint. If there is no best match, an error is raised.
-- argument types must be monomorphic
tcTemplateTypeResolve :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcTemplateTypeResolve (TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let targs = map (typed . loc) args'
    (t,pos,_) <- matchTemplateType l tn targs (checkTemplateType n) mempty
    let l' = Typed l t
    let n' = fmap notTyped n -- we don't type the template name, only the application
    return $ TemplateSpecifier l' n' args'

-- | Matches a list of constraints and produces a dictionary as a witness
resolveTemplateConstraints :: Location loc => loc -> [TCstr] -> TDict -> TcM loc TDict
resolveTemplateConstraints l cstrs dict = foldM (\d c -> resolveTemplateConstraint l c d) dict cstrs

-- | Matches a constraint and produces a dictionary as a witness
resolveTemplateConstraint :: Location loc => loc -> TCstr -> TDict -> TcM loc TDict
resolveTemplateConstraint l (TCstr (Left n) args) dict = do
    (t,pos,dict') <- matchTemplateType l n args (checkTemplateType (TypeName l n)) dict
    return dict'
resolveTemplateConstraint l (TCstr (Right n) args) dict = do
    (t,pos,dict') <- matchTemplateType l n args (checkProcedure (ProcedureName l n)) dict
    return dict'
    
-- | Matches a list of template arguments against a list of template declarations
matchTemplateType :: Location loc => loc -> Identifier -> [Type] -> TcReaderM loc [EntryEnv loc] -> TDict -> TcM loc (Type,Position,TDict)
matchTemplateType l n args check dict = do
    entries <- tcReaderM $ check
    let entries' = case lookupTDict n args dict of
            Nothing -> entries
            Just p -> filter (\e -> locpos (entryLoc e) == p) entries
    instances <- instantiateTemplateEntries n args entries'
    case instances of
        [] -> tcError (locpos l) $ NoMatchingTemplateOrProcedure n (map (locpos . entryLoc) entries')
        es -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst):_) <- tcReaderM $ sortByM (compareTemplateDecls l n) es
            -- return the instantiated body of the most specific declaration
            resolveTemplateEntry e subst $ mappend dict $ TDict $ Map.singleton (n,args) (locpos l)

resolveTemplateEntry :: Location loc => EntryEnv loc -> Substs Type -> TDict -> TcM loc (Type,Position,TDict)
resolveTemplateEntry e s dict = case entryType e of
    TpltType vars cstrs specials body -> do
        let cstrs' = substTraversable s cstrs -- specialize the constraints
        let specials' = substTraversable s specials -- specialize the specializations
        dict' <- resolveTemplateConstraints (entryLoc e) cstrs' dict -- compute a dictionary from the constraints
        let body' = subst s body -- specialize the struct's body
        let body'' = addTDict dict' body' -- pass the dictionary to resolve inner template instantiations
        return (body'',locpos $ entryLoc e,dict')

-- | Tells if one declaration is strictly more specific than another, and if not it fails
compareTemplateDecls :: Location loc => loc -> Identifier -> (EntryEnv loc,Substs Type) -> (EntryEnv loc,Substs Type) -> TcReaderM loc Ordering
compareTemplateDecls l n (e1,s1) (e2,d2) = do
    ord <- comparesList l (uniqueTemplateArgs n e1) (uniqueTemplateArgs n e2)
    when (ord == EQ) $ tcError (locpos l) $ ComparisonException $ "Duplicate instances for template or overload" ++ n
    return ord
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: Location loc => Identifier -> [Type] -> [EntryEnv loc] -> TcM loc [(EntryEnv loc,Substs Type)]
instantiateTemplateEntries n args es = foldM (\xs e -> liftM (xs ++) (instantiateTemplateEntry n args e)) [] es

instantiateTemplateEntry :: Location loc => Identifier -> [Type] -> EntryEnv loc -> TcM loc [(EntryEnv loc,Substs Type)]
instantiateTemplateEntry n args e = do
    -- we are just unifying type variables, without coercions, and hence just check for pure equality
    ok <- tcReaderM $ prove (equalsList (entryLoc e) args $ uniqueTemplateArgs n e)
    case ok of
        Nothing -> return []
        Just subst -> return [(e,subst)]

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = PrimType $ fmap (const ()) p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: Location loc => TemplateTypeArgument loc -> TcM loc (TemplateTypeArgument (Typed loc))
tcTemplateTypeArgument (GenericTemplateTypeArgument l n) = do
    t <- tcReaderM $ checkTemplateArg n
    let n' = fmap (flip Typed t) n
    return $ GenericTemplateTypeArgument (Typed l t) n'
tcTemplateTypeArgument (TemplateTemplateTypeArgument l n args) = do
    TemplateSpecifier l' n' args' <- tcDatatypeSpec (TemplateSpecifier l n args)
    return $ TemplateTemplateTypeArgument l' n' args'
tcTemplateTypeArgument (PrimitiveTemplateTypeArgument l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveTemplateTypeArgument (Typed l t) p'
tcTemplateTypeArgument (IntTemplateTypeArgument l i) = do
    let t = TDim i
    return $ IntTemplateTypeArgument (Typed l t) i
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: Location loc => Maybe (DimtypeSpecifier loc) -> TcM loc (Maybe (DimtypeSpecifier (Typed loc)),Expression ())
tcMbDimtypeSpec Nothing = return (Nothing,integerExpr 0) -- 0 by default
tcMbDimtypeSpec (Just dim) = do
    (dim',t) <- tcDimtypeSpec dim
    return (Just dim',t)

tcDimtypeSpec :: Location loc => DimtypeSpecifier loc -> TcM loc (DimtypeSpecifier (Typed loc),Expression ())
tcDimtypeSpec (DimSpecifier l e) = do
    e' <- tcDimSizeExpr Nothing e
    return (DimSpecifier (notTyped l) e',fmap (const ()) e') 

tcRetTypeSpec :: Location loc => ReturnTypeSpecifier loc -> TcM loc (ReturnTypeSpecifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing) = do
    let t = Void
    return $ ReturnType (Typed l Void) Nothing
tcRetTypeSpec (ReturnType l (Just s)) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    return $ ReturnType (Typed l t) (Just s')

-- | Retrieves a constant dimension from a type
typeDim :: Location loc => loc -> Type -> TcM loc (Maybe Integer)
typeDim l (CType _ _ e _) = do
    let le = fmap (const noloc) e
    (_,mb) <- integerLitExpr le
    when (isNothing mb) $ tcWarn (locpos l) $ NoStaticDimension (fmap locpos le)
    return mb
typeDim l _ = error "no dimension"

projectMatrixType :: Location loc => loc -> Type -> [(Maybe Integer,Maybe Integer)] -> TcM loc Type
projectMatrixType l (CType sec t dim szs) rngs = do
    mb <- isStaticIntegerExpr dim
    case mb of
        Nothing -> tcError (locpos l) $ NonStaticDimension
        Just d -> do
            if (d > 0 && length szs >= length rngs)
                then do
                    szs' <- projectSizes l szs rngs
                    return $ CType sec t (integerExpr $ toEnum $ length szs') szs'
                else tcError (locpos l) $ MismatchingArrayDimension (toEnum $ length szs) (toEnum $ length rngs) Nothing

projectSizes :: Location loc => loc -> [Expression ()] -> [(Maybe Integer,Maybe Integer)] -> TcM loc [Expression ()]
projectSizes l [] _ = return []
projectSizes l _ [] = return []
projectSizes l (x:xs) (y:ys) = do
    mb <- isStaticIntegerExpr x
    z <- case mb of
        Just sz -> do
            let low = maybe 0 id (fst y)
                upp = maybe sz id (snd y)
            if (sz >= low && sz <= upp)
                then return $ integerExpr (upp - low)
                else tcError (locpos l) $ ArrayAccessOutOfBounds sz (low,upp)
        otherwise -> do
            tcWarn (locpos l) $ DependentSizeSelection
            return x
    zs <- projectSizes l xs ys
    return (z:zs)

-- | checks that a given type is a struct type, resolving struct templates if necessary, and projects a particular field.
projectStructField :: Location loc => loc -> Type -> AttributeName loc -> TcM loc Type
projectStructField l (StructType atts) (AttributeName _ a) = do -- project the field
    case List.find (\(Attribute _ t f) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound a
        Just (Attribute _ t f) -> return $ typeSpecifierLoc t
projectStructField l (TApp n args dict) a = do -- resolve templates
    (t,pos,dict') <- matchTemplateType l n args (checkTemplateType (TypeName l n)) dict
    projectStructField l t a -- project the field

