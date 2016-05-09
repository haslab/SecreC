{-# LANGUAGE RankNTypes, ScopedTypeVariables, ViewPatterns, TupleSections, TypeFamilies #-}

module Language.SecreC.Parser.Parsec where

import Language.SecreC.Position
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Monad
import Language.SecreC.Pretty hiding (sepBy)
import Language.SecreC.Parser.Tokens
import Language.SecreC.Parser.Lexer

import Text.Parsec hiding (many,many1)
import qualified Text.Parsec as Parsec
import Text.Parsec.Pos

import Control.Applicative hiding ((<|>),optional,many)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Catch hiding (try)
import Control.Monad.Except
import Control.Monad.Reader (ask)
import Control.Monad.Identity
import Control.Monad.State as State
import Control.Monad.Writer as Writer

import System.IO

import Safe

import qualified Data.Foldable as Foldable
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

instance (Monad m,MonadCatch m) => MonadThrow (ParsecT s u m) where
    throwM = lift . throwM

instance MonadCatch m => MonadCatch (ParsecT s u m) where
    p `catch` h = mkPT $ \s ->
            runParsecT p s `catch` \e ->
                runParsecT (h e) s

many1 :: MonadCatch m => String -> ScParserT m a -> ScParserT m [a]
many1 msg p = catch (Parsec.many1 p) (\(e::SomeException) -> error $ msg ++ show e)

many :: MonadCatch m => String -> ScParserT m a -> ScParserT m [a]
many msg p = catch (Parsec.many p) (\(e::SomeException) -> error $ msg ++ show e)

-- parser inside an annotation or not
type ScState = Bool

type ScParserT m a = ParsecT [TokenInfo] ScState (SecrecM m) a

infixr 1 >*< 
(>*<) :: ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (a,b)
p1 >*< p2 = do
    x <- p1
    y <- p2
    return (x,y)
    
infixr 1 >+< 
(>+<) :: ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (Either a b)
p1 >+< p2 = liftM Left p1 <|> liftM Right p2

infixr 1 <||>
(<||>) :: ParsecT s u m a -> ParsecT s u m a -> ParsecT s u m a
p1 <||> p2 = try p1 <|> p2

apA :: Applicative f => f a -> (a -> b) -> f b
apA m f = pure f <*> m

apA2 :: Applicative f => f a -> f b -> (a -> b -> c) -> f c
apA2 ma mb f = pure f <*> ma <*> mb

apA3 :: Applicative f => f a -> f b -> f c -> (a -> b -> c -> d) -> f d
apA3 ma mb mc f = pure f <*> ma <*> mb <*> mc

apA4 :: Applicative f => f a -> f b -> f c -> f d -> (a -> b -> c -> d -> e) -> f e
apA4 ma mb mc md f = pure f <*> ma <*> mb <*> mc <*> md

apA5 :: Applicative f => f a -> f b -> f c -> f d -> f e -> (a -> b -> c -> d -> e -> g) -> f g
apA5 ma mb mc md me f = pure f <*> ma <*> mb <*> mc <*> md <*> me

apA6 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> (a -> b -> c -> d -> e -> g -> h) -> f h
apA6 ma mb mc md me mg f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg

scTok :: (Monad m,MonadCatch m) => Token -> ScParserT m TokenInfo
scTok t = scTokPred ((==t) . tSymb)

scTokPred :: (Monad m,MonadCatch m) => (TokenInfo -> Bool) -> ScParserT m TokenInfo
scTokPred p = scTokWith (\x -> if p x then Just x else Nothing)

scTokWith :: (Monad m,MonadCatch m) => (TokenInfo -> Maybe a) -> ScParserT m a
scTokWith f = tokenPrim ppr next f
    where
    next p t (s:ss) = positionToSourcePos $ tLoc s
    next p t [] = updatePosString p (ppr t)

scChar :: (Monad m,MonadCatch m) => Char -> ScParserT m TokenInfo
scChar c = scTokPred (p . tSymb)
    where
    p (CHAR c') = c == c'
    p _ = False

scParens :: (Monad m,MonadCatch m) => ScParserT m a -> ScParserT m a
scParens p = scChar '(' *> p <* scChar ')'

scBraces :: (Monad m,MonadCatch m) => ScParserT m a -> ScParserT m a
scBraces p = scChar '{' *> p <* scChar '}'

scParens' :: (Monad m,MonadCatch m) => (TokenInfo -> ScParserT m a) -> ScParserT m a
scParens' p = do
    x1 <- scChar '('
    x <- p x1
    scChar ')'
    return x

scBrackets :: (Monad m,MonadCatch m) => ScParserT m a -> ScParserT m a
scBrackets p = scChar '[' *> p <* scChar ']'

scBrackets' :: (Monad m,MonadCatch m) => (TokenInfo -> ScParserT m a) -> ScParserT m a
scBrackets' p = do
    x1 <- scChar '['
    x <- p x1
    scChar ']'
    return x

scABrackets :: (Monad m,MonadCatch m) => ScParserT m a -> ScParserT m a
scABrackets p = scChar '<' *> p <* scChar '>'

scCBrackets :: (Monad m,MonadCatch m) => ScParserT m a -> ScParserT m a
scCBrackets p = scChar '{' *> p <* scChar '}'

scCBrackets' :: (Monad m,MonadCatch m) => (TokenInfo -> ScParserT m a) -> ScParserT m a
scCBrackets' p = do
    x1 <- scChar '{'
    x <- p x1
    scChar '}'
    return x

scFoldl1 :: (Monad m,MonadCatch m) => (a -> b -> ScParserT m a) -> ScParserT m a -> ScParserT m b -> ScParserT m a
scFoldl1 f ma mb = do
    x <- ma
    ys <- many1 "scFoldl1" mb
    Foldable.foldlM f x ys
    
scFoldl :: (Monad m,MonadCatch m) => (a -> b -> ScParserT m a) -> ScParserT m a -> ScParserT m b -> ScParserT m a
scFoldl f ma mb = do
    x <- ma
    ys <- many "scFoldl" mb
    Foldable.foldlM f x ys

scMaybeCont :: ScParserT m a -> (Maybe a -> ScParserT m b) -> ScParserT m b
scMaybeCont p cont = (p >>= cont . Just) <||> cont Nothing
                
scMaybeContPair :: ScParserT m a -> ScParserT m b -> ScParserT m (Maybe a,b)
scMaybeContPair p cont = scMaybeCont p (\mb -> liftM (mb,) cont)

-- * Grammar

-- ** Literals

scIntLiteral :: (Monad m,MonadCatch m) => ScParserT m (Loc Position Integer)
scIntLiteral = liftM (\x1 -> Loc (loc x1) (tokenInteger x1)) (scTokPred p) <?> "int literal"
    where
    p (TokenInfo (BIN_LITERAL _) _ _) = True
    p (TokenInfo (DEC_LITERAL _) _ _) = True
    p (TokenInfo (HEX_LITERAL _) _ _) = True
    p (TokenInfo (OCT_LITERAL _) _ _) = True
    p _ = False

scFloatLiteral :: (Monad m,MonadCatch m) => ScParserT m (Loc Position Double)
scFloatLiteral = liftM (\x1 -> Loc (loc x1) (tokenFloat x1)) (scTokPred p) <?> "float literal"
    where
    p (TokenInfo (FLOAT_LITERAL _) _ _) = True
    p _ = False

scStrFragment :: (Monad m,MonadCatch m) => ScParserT m TokenInfo
scStrFragment = scTokPred p <?> "string fragment"
    where
    p (TokenInfo (STR_FRAGMENT _) _ _) = True
    p _ = False

scStrIdentifier :: (Monad m,MonadCatch m) => ScParserT m TokenInfo
scStrIdentifier = scTokPred p <?> "string identifier"
    where
    p (TokenInfo (STR_IDENTIFIER _) _ _) = True
    p _ = False

-- ** Identifiers

scKindId :: (Monad m,MonadCatch m) => ScParserT m (KindName Identifier Position)
scKindId = liftM (\t -> KindName (tLoc t) (tokenString t)) scIdentifier <?> "kind id"

scVarId :: (Monad m,MonadCatch m) => ScParserT m (VarName Identifier Position)
scVarId = liftM (\t -> VarName (tLoc t) (tokenString t)) scIdentifier <?> "variable id"

scAttributeId :: (Monad m,MonadCatch m) => ScParserT m (AttributeName Identifier Position)
scAttributeId = liftM (\t -> AttributeName (tLoc t) (tokenString t)) scIdentifier <?> "attribute id"

scProcedureId :: (Monad m,MonadCatch m) => ScParserT m (ProcedureName Identifier Position)
scProcedureId = liftM (\t -> ProcedureName (tLoc t) (tokenString t)) scIdentifier <?> "procedure id"

scDomainId :: (Monad m,MonadCatch m) => ScParserT m (DomainName Identifier Position)
scDomainId = liftM (\t -> DomainName (tLoc t) (tokenString t)) scIdentifier <?> "domain id"

scTypeId :: (Monad m,MonadCatch m) => ScParserT m (TypeName Identifier Position)
scTypeId = liftM (\t -> TypeName (tLoc t) (tokenString t)) scIdentifier <?> "type id"

scTemplateArgId :: (Monad m,MonadCatch m) => ScParserT m (TemplateArgName Identifier Position)
scTemplateArgId = liftM (\t -> TemplateArgName (tLoc t) (tokenString t)) scIdentifier <?> "template argument id"

scModuleId :: (Monad m,MonadCatch m) => ScParserT m (ModuleName Identifier Position)
scModuleId = liftM (\t -> ModuleName (tLoc t) (tokenString t)) scIdentifier <?> "module id"

scIdentifier :: (Monad m,MonadCatch m) => ScParserT m TokenInfo
scIdentifier = scTokPred (p . tSymb) <?> "id"
    where
    p (IDENTIFIER s) = True
    p _ = False

scEOF :: (Monad m,MonadCatch m) => ScParserT m ()
scEOF = scTokPred (p . tSymb) >> return ()
    where
    p TokenEOF = True
    p _ = False

-- ** Program and variable declarations

scModuleFile :: (MonadIO m,MonadCatch m) => ScParserT m (Module Identifier Position)
scModuleFile = scModule <* scEOF

scModule :: (MonadIO m,MonadCatch m) => ScParserT m (Module Identifier Position)
scModule = ((apA4 (scTok MODULE) scModuleId (scChar ';') scProgram (\x1 x2 x3 x4 -> Module (loc x1) (Just x2) x4) <?> "named module")
       <|> (apA scProgram (\x1 -> Module (loc x1) Nothing x1) <?> "unamed module")
       )
    
scProgram :: (MonadIO m,MonadCatch m) => ScParserT m (Program Identifier Position)
scProgram = do
    p <- scPosition
    apA2 scImportDeclarations scGlobalDeclarations (\x1 x2 -> Program (if null x1 then if null x2 then p else loc (headNote "scProgram" x2) else loc (headNote "scProgram" x1)) x1 x2) <?> "program"

scImportDeclarations :: (Monad m,MonadCatch m) => ScParserT m [ImportDeclaration Identifier Position]
scImportDeclarations = many "scImportDeclarations" scImportDeclaration <?> "import declarations"

scGlobalDeclarations :: (MonadIO m,MonadCatch m) => ScParserT m [GlobalDeclaration Identifier Position]
scGlobalDeclarations = many "scGlobalDeclarations" scGlobalDeclaration <?> "global declarations"

scImportDeclaration :: (Monad m,MonadCatch m) => ScParserT m (ImportDeclaration Identifier Position)
scImportDeclaration = apA3 (scTok IMPORT) scModuleId (scChar ';') (\x1 x2 x3 -> Import (loc x1) x2) <?> "import declaration"

scGlobalDeclaration :: (MonadIO m,MonadCatch m) => ScParserT m (GlobalDeclaration Identifier Position)
scGlobalDeclaration = (apA2 scConstDeclaration (scChar ';') (\x1 x2 -> GlobalConst (loc x1) x1) <?> "const declaration")
                 <||>  (apA2 scVariableDeclaration (scChar ';') (\x1 x2 -> GlobalVariable (loc x1) x1) <?> "variable declaration")
                 <||> (apA2 scDomainDeclaration (scChar ';') (\x1 x2 -> GlobalDomain (loc x1) x1) <?> "domain declaration")
                 <||> (apA2 scKindDeclaration (scChar ';') (\x1 x2 -> GlobalKind (loc x1) x1) <?> "kind declaration")
                 <||> (apA scProcedureDeclaration (\x1 -> GlobalProcedure (loc x1) x1) <?> "procedure declaration")
                 <||> (apA scStructureDeclaration (\x1 -> GlobalStructure (loc x1) x1) <?> "structure declaration")
                 <||> (apA scTemplateDeclaration (\x1 -> GlobalTemplate (loc x1) x1) <?> "template declaration")
                 <||> ((scGlobalAnnotations >>= \x1 -> scLoc (headMay x1) >>= \lx1 -> return $ GlobalAnnotations lx1 x1) <?> "annotation declaration")

scLoc :: (Monad m,LocOf a ~ Position,Located a) => Maybe a -> ScParserT m Position
scLoc (Just x) = return $ loc x
scLoc Nothing = liftM sourcePosToPosition getPosition

scKindDeclaration :: (Monad m,MonadCatch m) => ScParserT m (KindDeclaration Identifier Position)
scKindDeclaration = apA2 (scTok KIND) scKindId (\x1 x2 -> Kind (loc x1) x2) <?> "kind declaration"

scDomainDeclaration :: (Monad m,MonadCatch m) => ScParserT m (DomainDeclaration Identifier Position)
scDomainDeclaration = apA3 (scTok DOMAIN) scDomainId scKindId (\x1 x2 x3 -> Domain (loc x1) x2 x3) <?> "domain declaration"

scVariableInitialization :: (Monad m,MonadCatch m) => ScParserT m (VariableInitialization Identifier Position)
scVariableInitialization = apA3
    scVarId
    (optionMaybe scSizes)
    (optionMaybe (scChar '=' *> scExpression))
    (\x1 x2 x3 -> VariableInitialization (loc x1) x1 x2 x3) <?> "variable initialization"

scConstInitialization :: (Monad m,MonadCatch m) => ScParserT m (ConstInitialization Identifier Position)
scConstInitialization = apA3
    scVarId
    (optionMaybe scSizes)
    (optionMaybe (scChar '=' *> scExpression))
    (\x1 x2 x3 -> ConstInitialization (loc x1) x1 x2 x3) <?> "const initialization"

scVariableInitializations :: (Monad m,MonadCatch m) => ScParserT m (NeList (VariableInitialization Identifier Position))
scVariableInitializations = apA (sepBy1 scVariableInitialization (scChar ',')) fromListNe <?> "variable initializations"

scConstInitializations :: (Monad m,MonadCatch m) => ScParserT m (NeList (ConstInitialization Identifier Position))
scConstInitializations = apA (sepBy1 scConstInitialization (scChar ',')) fromListNe <?> "const initializations"

scVariableDeclaration :: (Monad m,MonadCatch m) => ScParserT m (VariableDeclaration Identifier Position)
scVariableDeclaration = scTypeSpecifier $ \x1 -> apA scVariableInitializations (\x2 -> VariableDeclaration (loc x1) x1 x2) <?> "variable declaration"

scConstDeclaration :: (Monad m,MonadCatch m) => ScParserT m (ConstDeclaration Identifier Position)
scConstDeclaration = do
    x0 <- scTok CONST
    scTypeSpecifier $ \x1 -> apA scConstInitializations (\x2 -> ConstDeclaration (loc x0) x1 x2) <?> "const declaration"

scProcedureParameter :: (Monad m,MonadCatch m) => ScParserT m (ProcedureParameter Identifier Position)
scProcedureParameter =
    (scTok CONST >>= \x0 -> (scVariadicTypeSpecifier $ \(x1,x2) -> apA2 scVarId scInvariant (\x3 x4 -> ConstProcedureParameter (loc x0) x1 x2 x3 x4) <?> "const procedure parameter"))
    <|> (scVariadicTypeSpecifier $ \(x1,x2) -> apA scVarId (\x3 -> ProcedureParameter (loc x1) x1 x2 x3) <?> "procedure parameter")

scSizes :: (Monad m,MonadCatch m) => ScParserT m (Sizes Identifier Position)
scSizes = apA (scParens scVariadicExpressionList1) Sizes <?> "dimensions"

scInvariant :: (Monad m,MonadCatch m) => ScParserT m (Maybe (Expression Identifier Position))
scInvariant = optionMaybe (scBraces scExpression) <?> "dimensions"

scExpressionList :: (Monad m,MonadCatch m) => ScParserT m [Expression Identifier Position]
scExpressionList = sepBy scExpression (scChar ',') <?> "expression list"

scVariadicExpressionList :: (Monad m,MonadCatch m) => ScParserT m [(Expression Identifier Position,IsVariadic)]
scVariadicExpressionList = (sepBy scVariadicExpression (scChar ',')) <?> "variadic expression list"

scVariadicExpressionList1 :: (Monad m,MonadCatch m) => ScParserT m (NeList (Expression Identifier Position,IsVariadic))
scVariadicExpressionList1 = apA (sepBy1 scVariadicExpression (scChar ',')) fromListNe <?> "variadic expression list"

-- ** Types                                                                     

scTypeSpecifier :: (Monad m,MonadCatch m) => (TypeSpecifier Identifier Position -> ScParserT m a) -> ScParserT m a
scTypeSpecifier cont = (scMaybeCont scSecTypeSpecifier $ \x1 -> do
    x2 <- scDatatypeSpecifier
    x3 <- optionMaybe scDimtypeSpecifier
    let t = TypeSpecifier (maybe (loc x2) loc x1) x1 x2 x3
    cont t) <?> "type specifier"

scVariadicTypeSpecifier :: (Monad m,MonadCatch m) => ((TypeSpecifier Identifier Position,IsVariadic) -> ScParserT m a) -> ScParserT m a
scVariadicTypeSpecifier cont = scTypeSpecifier $ \t -> do
    scMaybeCont (scTok VARIADIC) $ \b -> cont (t,isJust b)

scSecTypeSpecifier :: (Monad m,MonadCatch m) => ScParserT m (SecTypeSpecifier Identifier Position)
scSecTypeSpecifier = (apA (scTok PUBLIC) (\x1 -> PublicSpecifier (loc x1)) <?> "public security type")
                 <|> (apA scDomainId (\x1 -> PrivateSpecifier (loc x1) x1) <?> "private security type")

scDatatypeSpecifier :: (Monad m,MonadCatch m) => ScParserT m (DatatypeSpecifier Identifier Position)
scDatatypeSpecifier = (apA scPrimitiveDatatype (\x1 -> PrimitiveSpecifier (loc x1) x1) <?> "primitive type specifier")
                  <|> (scTemplateStructDatatypeSpecifier <?> "template type specifier")
                  <||> (apA scTypeId (\x1 -> VariableSpecifier (loc x1) x1) <?> "named type specifier")

scPrimitiveDatatype :: (Monad m,MonadCatch m) => ScParserT m (PrimitiveDatatype Position)
scPrimitiveDatatype = (apA (scTok BOOL) (DatatypeBool . loc)
                  <|> apA (scTok INT) (DatatypeInt64 . loc)
                  <|> apA (scTok UINT) (DatatypeUint64 . loc)
                  <|> apA (scTok INT8) (DatatypeInt8 . loc)
                  <|> apA (scTok UINT8) (DatatypeUint8 . loc)
                  <|> apA (scTok INT16) (DatatypeInt16 . loc)
                  <|> apA (scTok UINT16) (DatatypeUint16 . loc)
                  <|> apA (scTok INT32) (DatatypeInt32 . loc)
                  <|> apA (scTok UINT32) (DatatypeUint32 . loc)
                  <|> apA (scTok INT64) (DatatypeInt64 . loc)
                  <|> apA (scTok UINT64) (DatatypeUint64 . loc)
                  <|> apA (scTok STRING) (DatatypeString . loc)
                  <|> apA (scTok XOR_UINT8) (DatatypeXorUint8 . loc)
                  <|> apA (scTok XOR_UINT16) (DatatypeXorUint16 . loc)
                  <|> apA (scTok XOR_UINT32) (DatatypeXorUint32 . loc)
                  <|> apA (scTok XOR_UINT64) (DatatypeXorUint64 . loc)
                  <|> apA (scTok XOR_UINT) (DatatypeXorUint64 . loc)
                  <|> apA (scTok FLOAT) (DatatypeFloat32 . loc)
                  <|> apA (scTok FLOAT32) (DatatypeFloat32 . loc)
                  <|> apA (scTok FLOAT64) (DatatypeFloat64 . loc)) <?> "primitive type"

scTemplateStructDatatypeSpecifier :: (Monad m,MonadCatch m) => ScParserT m (DatatypeSpecifier Identifier Position)
scTemplateStructDatatypeSpecifier = apA2 scTypeId (scABrackets scTemplateTypeArguments) (\x1 x2 -> TemplateSpecifier (loc x1) x1 x2) <?> "template struct specifier"

scTemplateTypeArguments :: (Monad m,MonadCatch m) => ScParserT m [(TemplateTypeArgument Identifier Position,IsVariadic)]
scTemplateTypeArguments = sepBy (apA2 scTemplateTypeArgument scVariadic (,)) (scChar ',') <?> "template type arguments"

scTemplateTypeArgument :: (Monad m,MonadCatch m) => ScParserT m (TemplateTypeArgument Identifier Position)
scTemplateTypeArgument = (apA (scTok PUBLIC) (PublicTemplateTypeArgument . loc) <?> "public template type argument")
                     <|> (apA2 scTypeId (scABrackets scTemplateTypeArguments) (\x1 x2 -> TemplateTemplateTypeArgument (loc x1) x1 x2) <?> "template template type argument")
                    <||> (apA scTemplateArgId (\x1 -> GenericTemplateTypeArgument (loc x1) x1) <?> "named template type argument") -- type, domain or variable identifier
                     <|> (apA scExpression (\x1 -> ExprTemplateTypeArgument (loc x1) x1) <?> "expression template type argument")
                     <||> (apA scPrimitiveDatatype (\x1 -> PrimitiveTemplateTypeArgument (loc x1) x1) <?> "primitive template type argument")

scDimtypeSpecifier :: (Monad m,MonadCatch m) => ScParserT m (DimtypeSpecifier Identifier Position)
scDimtypeSpecifier = (scBrackets' $ \x1 -> scBrackets' $ \x2 ->
      apA scExpression (\x3 -> DimSpecifier (loc x1) x3)) <?> "dimension specifier"

-- ** Templates                                                               

scTemplateDeclaration :: (MonadIO m,MonadCatch m) => ScParserT m (TemplateDeclaration Identifier Position)
scTemplateDeclaration = (do
    x1 <- scTok TEMPLATE
    x3 <- scABrackets scTemplateQuantifiers
    (    apA scStructure (templStruct x1 x3)
     <|> apA scProcedureDeclaration  (\x5 -> TemplateProcedureDeclaration (loc x1) x3 x5))) <?> "template declaration"
  where
    templStruct x1 x3 (Nothing,x5) = TemplateStructureDeclaration (loc x1) x3 x5
    templStruct x1 x3 (Just x4,x5) = TemplateStructureSpecialization (loc x1) x3 x4 x5

scTemplateQuantifiers :: (Monad m,MonadCatch m) => ScParserT m [TemplateQuantifier Identifier Position]
scTemplateQuantifiers = (Text.Parsec.sepBy scTemplateQuantifier (scChar ',')) <?> "template quantifiers"

scTemplateQuantifier :: (Monad m,MonadCatch m) => ScParserT m (TemplateQuantifier Identifier Position)
scTemplateQuantifier =
        (apA4 (scTok DOMAIN) scVariadic scDomainId (optionMaybe (scChar ':' *> scKindId)) (\x1 x2 x3 x4 -> DomainQuantifier (loc x1) x2 x3 x4)
    <|> apA4 (scTok DIMENSIONALITY) scVariadic scVarId scInvariant (\x1 x2 x3 x4 -> DimensionQuantifier (loc x1) x2 x3 x4)
    <|> apA3 (scTok TYPE) scVariadic scTypeId (\x1 x2 x3 -> DataQuantifier (loc x1) x2 x3)) <?> "template quantifier"

scVariadic :: (Monad m,MonadCatch m) => ScParserT m IsVariadic
scVariadic = apA (optionMaybe (scTok VARIADIC)) isJust

-- ** Structures                                                                 

scStructure :: (Monad m,MonadCatch m) => ScParserT m (Maybe [(TemplateTypeArgument Identifier Position,IsVariadic)],StructureDeclaration Identifier Position)
scStructure = apA4 (scTok STRUCT) scTypeId (optionMaybe $ scABrackets scTemplateTypeArguments) (scCBrackets scAttributeList) (\x1 x2 x3 x4 -> (x3,StructureDeclaration (loc x1) x2 x4)) <?> "structure declaration"

scStructureDeclaration :: (Monad m,MonadCatch m) => ScParserT m (StructureDeclaration Identifier Position)
scStructureDeclaration = apA3 (scTok STRUCT) scTypeId (scCBrackets scAttributeList) (\x1 x2 x3 -> StructureDeclaration (loc x1) x2 x3) <?> "structure declaration"

scAttributeList :: (Monad m,MonadCatch m) => ScParserT m [Attribute Identifier Position]
scAttributeList = many "scAttributeList" scAttribute <?> "attribute list"

scAttribute :: (Monad m,MonadCatch m) => ScParserT m (Attribute Identifier Position)
scAttribute = scTypeSpecifier $ \x1 -> apA2 scAttributeId (scChar ';') (\x2 x3 -> Attribute (loc x1) x1 x2) <?> "attribute"

-- ** Procedures                                

scReturnTypeSpecifier :: (Monad m,MonadCatch m) => (ReturnTypeSpecifier Identifier Position -> ScParserT m a) -> ScParserT m a
scReturnTypeSpecifier cont = ((apA (scTok VOID) (\x1 -> ReturnType (loc x1) Nothing) >>= cont)
                         <|> scTySize)
                          <?> "return type specifier"
    where
    scTySize = scTypeSpecifier $ \x1 -> do
        cont $ ReturnType (loc x1) (Just x1)

scProcedureDeclaration :: (MonadIO m,MonadCatch m) => ScParserT m (ProcedureDeclaration Identifier Position)
scProcedureDeclaration = ((scReturnTypeSpecifier $ \x1 -> apA5 (scTok OPERATOR) scOp (scParens scProcedureParameterList) scProcedureAnnotations scCompoundStatement (\x2 x3 x4 x5 x6 -> OperatorDeclaration (loc x1) x1 x3 x4 x5 (unLoc x6)))
                    <||> (scReturnTypeSpecifier $ \x1 -> apA4 scProcedureId (scParens scProcedureParameterList) scProcedureAnnotations scCompoundStatement (\x2 x3 x4 x5 -> ProcedureDeclaration (loc x1) x1 x2 x3 x4 (unLoc x5)))) <?> "procedure definition"
    
scProcedureParameterList :: (Monad m,MonadCatch m) => ScParserT m [ProcedureParameter Identifier Position]
scProcedureParameterList = sepBy scProcedureParameter (scChar ',') <?> "procedure parameters"

scOp :: (Monad m,MonadCatch m) => ScParserT m (Op Identifier Position)
scOp = (apA (scChar '+') (OpAdd . loc)
   <|> apA (scChar '&') (OpBand . loc)
   <|> apA (scChar '|') (OpBor  . loc)
   <|> apA (scChar '/') (OpDiv  . loc)
   <|> apA (scChar '>') (OpGt   . loc)
   <|> apA (scChar '<') (OpLt   . loc)
   <|> apA (scChar '%') (OpMod  . loc)
   <|> apA (scChar '*') (OpMul  . loc)
   <|> apA (scChar '-') (OpSub  . loc)
   <|> apA (scChar '^') (OpXor  . loc)
   <|> apA (scChar '!') (OpNot . loc)
   <|> apA (scTok EQ_OP) (OpEq . loc)
   <|> apA (scTok GE_OP) (OpGe . loc)
   <|> apA (scTok LAND_OP) (OpLand . loc)
   <|> apA (scTok LE_OP) (OpLe . loc)
   <|> apA (scTok LOR_OP) (OpLor . loc)
   <|> apA (scTok NE_OP) (OpNe . loc)
   <|> apA (scTok SHL_OP) (OpShl . loc)
   <|> apA (scTok SHR_OP) (OpShr . loc)
   <|> apA (scTok IMPLIES_OP) (OpImplies . loc)
   <|> apA (scTok EQUIV_OP) (OpEquiv . loc)
   <|> apA scCastType (\x1 -> OpCast (loc x1) x1) ) <?> "op"

-- * Statements                                                           

scCompoundStatement :: (MonadIO m,MonadCatch m) => ScParserT m (Loc Position [Statement Identifier Position])
scCompoundStatement = scCBrackets' $ \x1 -> apA (many "scCompoundStatement" scStatement) (\x2 -> Loc (loc x1) x2) <?> "compound statement"

scStatement :: (MonadIO m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scStatement = (apA scCompoundStatement (\x1 -> CompoundStatement (loc x1) (unLoc x1))
          <|> scIfStatement
          <|> scForStatement
          <|> scWhileStatement
          <|> scDowhileStatement
          <|> scAssertStatement
          <|> scPrintStatement
          <|> scSyscallStatement
          <|> apA2 scConstDeclaration (scChar ';') (\x1 x2 -> ConstStatement (loc x1) x1)
          <||> apA2 scVariableDeclaration (scChar ';') (\x1 x2 -> VarStatement (loc x1) x1)
          <||> apA3 (scTok RETURN) (optionMaybe scExpression) (scChar ';') (\x1 x2 x3 -> ReturnStatement (loc x1) x2)
          <|> apA2 (scTok CONTINUE) (scChar ';') (\x1 x2 -> ContinueStatement (loc x1))
          <|> apA2 (scTok BREAK) (scChar ';') (\x1 x2 -> BreakStatement (loc x1))
          <|> apA (scChar ';') (\x1 -> CompoundStatement (loc x1) [])
          <|> (scStatementAnnotations >>= \x1 -> scLoc (headMay x1) >>= \lx1 -> return $ AnnStatement lx1 x1)
          <|> apA2 scExpression (scChar ';') (\x1 x2 -> ExpressionStatement (loc x1) x1)
        ) <?> "statement"

scIfStatement :: (MonadIO m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scIfStatement = apA4 (scTok IF) (scParens scExpression) scStatement (optionMaybe (scTok ELSE *> scStatement)) (\x1 x2 x3 x4 -> IfStatement (loc x1) x2 x3 x4) <?> "if statement"

scForInitializer :: (Monad m,MonadCatch m) => ScParserT m (ForInitializer Identifier Position)
scForInitializer = (apA scVariableDeclaration InitializerVariable
               <||> apA (optionMaybe scExpression) InitializerExpression
             ) <?> "for initializer"

scForStatement :: (MonadIO m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scForStatement = (do
    x1 <- scTok FOR
    scChar '('
    x2 <- scForInitializer
    scChar ';'
    x3 <- optionMaybe scExpression
    scChar ';'
    x4 <- optionMaybe scExpression
    scChar ')'
    x5 <- scLoopAnnotations
    x6 <- scStatement
    return $ ForStatement (loc x1) x2 x3 x4 x5 x6) <?> "for statement"

scWhileStatement :: (MonadIO m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scWhileStatement = apA4 (scTok WHILE) (scParens scExpression) scLoopAnnotations scStatement (\x1 x2 x3 x4 -> WhileStatement (loc x1) x2 x3 x4)
    <?> "while statement"

scPrintStatement :: (Monad m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scPrintStatement = apA3 (scTok PRINT) (scParens scVariadicExpressionList) (scChar ';') (\x1 x2 x3 -> PrintStatement (loc x1) x2)
    <?> "print statement"

scDowhileStatement :: (MonadIO m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scDowhileStatement = apA6 (scTok DO) scLoopAnnotations scStatement (scTok WHILE) (scParens scExpression) (scChar ';') (\x1 x2 x3 x4 x5 x6 -> DowhileStatement (loc x1) x2 x3 x5)
    <?> "dowhile statement"

scAssertStatement :: (Monad m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scAssertStatement = apA3 (scTok ASSERT) (scParens scExpression) (scChar ';') (\x1 x2 x3 -> AssertStatement (loc x1) x2)
    <?> "assert statement"

scSyscallStatement :: (Monad m,MonadCatch m) => ScParserT m (Statement Identifier Position)
scSyscallStatement = apA3 (scTok SYSCALL) (scParens sysparams) (scChar ';') (\x1 (x2,x3) x4 -> SyscallStatement (loc x1) x2 x3)
  <?> "syscall statement"
    where
    sysparams = liftM unLoc scStringLiteral
            >*< many "scSyscallStatement" (scChar ',' *> scSyscallParameter)

scSyscallParameter :: (Monad m,MonadCatch m) => ScParserT m (SyscallParameter Identifier Position)
scSyscallParameter = (apA2 (scTok SYSCALL_RETURN) scVarId (\x1 x2 -> SyscallReturn (loc x1) x2)
                 <|> apA2 (scTok REF) scVarId (\x1 x2 -> SyscallPushRef (loc x1) x2)
                 <|> apA2 (scTok CREF) scExpression (\x1 x2 -> SyscallPushCRef (loc x1) x2)
                 <|> apA scExpression (\x1 -> SyscallPush (loc x1) x1)) <?> "syscall parameter"

-- ** Indices: not strictly expressions as they only appear in specific context  

scSubscript :: (Monad m,MonadCatch m) => ScParserT m (Subscript Identifier Position)
scSubscript = scBrackets scIndices <?> "subsscript"

scIndices :: (Monad m,MonadCatch m) => ScParserT m (NeList (Index Identifier Position))
scIndices = apA (sepBy1 scIndex (scChar ',')) fromListNe <?> "indices"

---- Precedence of slicing operator? Right now it binds weakest as it can appear
---- in very specific context. However, if we ever wish for "foo : bar" evaluate
---- to value in some other context we need to figure out sane precedence.
scIndex :: (Monad m,MonadCatch m) => ScParserT m (Index Identifier Position)
scIndex = (apA3 (optionMaybe scExpression) (scChar ':') (optionMaybe scExpression) (\x1 x2 x3 -> IndexSlice (maybe (loc x2) loc x1) x1 x3)
     <||> apA scExpression (\x1 -> IndexInt (loc x1) x1)) <?> "index"

-- ** Expressions                                                               

scLvalue :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scLvalue = scPostfixExpression <?> "lvalue"

scExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scExpression = scAssignmentExpression <?> "expression"

scVariadicExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position,IsVariadic)
scVariadicExpression  = apA2 scExpression scVariadic (,)

scAssignmentExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scAssignmentExpression = (apA3 scLvalue op scAssignmentExpression (\x1 x2 x3 -> BinaryAssign (loc x1) x1 x2 x3)
                      <||> scQualifiedExpression
                     ) <?> "assignment expression"
    where
    op = apA (scChar '=') (BinaryAssignEqual . loc)
     <|> apA (scTok MUL_ASSIGN) (BinaryAssignMul . loc)
     <|> apA (scTok DIV_ASSIGN) (BinaryAssignDiv . loc)
     <|> apA (scTok MOD_ASSIGN) (BinaryAssignMod . loc)
     <|> apA (scTok ADD_ASSIGN) (BinaryAssignAdd . loc)                                                                                
     <|> apA (scTok SUB_ASSIGN) (BinaryAssignSub . loc)
     <|> apA (scTok AND_ASSIGN) (BinaryAssignAnd . loc)
     <|> apA (scTok OR_ASSIGN) (BinaryAssignOr . loc)
     <|> apA (scTok XOR_ASSIGN) (BinaryAssignXor . loc)

scQualifiedExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scQualifiedExpression = scFoldl
    (\qe (t) -> return $ QualExpr (loc qe) qe t)
    scConditionalExpression
    (scTok TYPE_QUAL *> scTypeSpecifier return) <?> "qualified expression"

scConditionalExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scConditionalExpression = (do
    x1 <- scLogicalImpliesExpression 
    mb <- optionMaybe (scChar '?' *> scExpression >*< scChar ':' *> scExpression) 
    case mb of
        Nothing -> return x1
        Just (x2,x3) -> return $ CondExpr (loc x1) x1 x2 x3) <?> "conditional expression"

scLogicalImpliesExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scLogicalImpliesExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scLogicalOrExpression
    (ops >*< scLogicalOrExpression) <?> "logical implies expression"
  where
    ops = apA (scTok IMPLIES_OP) (OpImplies . loc)
      <|> apA (scTok EQUIV_OP) (OpEquiv . loc)

scLogicalOrExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scLogicalOrExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scLogicalAndExpression
    (ops >*< scLogicalAndExpression) <?> "logical or expression"
  where
    ops = apA (scTok LOR_OP) (OpLor . loc)

scLogicalAndExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scLogicalAndExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scBitwiseOrExpression
    (ops >*< scBitwiseOrExpression) <?> "logical and expression"
  where
    ops = apA (scTok LAND_OP) (OpLand . loc)

scBitwiseOrExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scBitwiseOrExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scBitwiseXorExpression
    (ops >*< scBitwiseXorExpression) <?> "bitwise or expression"
  where
    ops = apA (scChar '|') (OpBor . loc)

scBitwiseXorExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scBitwiseXorExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scBitwiseAndExpression
    (ops >*< scBitwiseAndExpression) <?> "bitwise xor expression"
  where
    ops = apA (scChar '^') (OpXor . loc)
    
scBitwiseAndExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scBitwiseAndExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scEqualityExpression
    (ops >*< scEqualityExpression) <?> "bitwise and expression"
  where
    ops = apA (scChar '&') (OpBand . loc)

scEqualityExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scEqualityExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scRelationalExpression
    (ops >*< scRelationalExpression) <?> "equality expression"
  where
    ops = apA (scTok EQ_OP) (OpEq . loc)
      <|> apA (scTok NE_OP) (OpNe . loc)

scRelationalExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scRelationalExpression = scFoldl
    (\se1 (op,se2) -> return $ BinaryExpr (loc se1) se1 op se2)
    scShiftExpression
    (ops >*< scShiftExpression) <?> "relational expression"
  where
    ops = apA (scTok LE_OP) (OpLe . loc)
      <|> apA (scTok GE_OP) (OpGe . loc)
      <|> apA (scChar '<') (OpLt . loc)
      <|> apA (scChar '>') (OpGt . loc)

scShiftExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scShiftExpression = scFoldl
    (\a1 (op,a2) -> return $ BinaryExpr (loc a1) a1 op a2)
    scAdditiveExpression
    (ops >*< scAdditiveExpression) <?> "shift expression"
  where
    ops = apA (scTok SHL_OP) (OpShl . loc)
      <|> apA (scTok SHR_OP) (OpShr . loc)

scAdditiveExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scAdditiveExpression = scFoldl
    (\a1 (op,a2) -> return $ BinaryExpr (loc a1) a1 op a2)
    scMultiplicativeExpression
    (ops >*< scMultiplicativeExpression) <?> "additive expression"
  where
    ops = apA (scChar '+') (OpAdd . loc)
      <|> apA (scChar '-') (OpSub . loc)

scMultiplicativeExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scMultiplicativeExpression = scFoldl
    (\a1 (op,a2) -> return $ BinaryExpr (loc a1) a1 op a2)
    scCastExpression
    (ops >*< scCastExpression) <?> "multiplicative expression"
  where
    ops = apA (scChar '*') (OpMul . loc)
      <|> apA (scChar '/') (OpDiv . loc)
      <|> apA (scChar '%') (OpMod . loc)

scCastExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scCastExpression = (apA2 scCastType scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpCast (loc x1) x1) x2)
            <||> scPrefixOp) <?> "cast expression"

scCastType :: (Monad m,MonadCatch m) => ScParserT m (CastType Identifier Position)
scCastType = scParens (apA scPrimitiveDatatype (CastPrim) <|> apA scTypeId (CastTy))

scPrefixOp :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scPrefixOp = (apA2 (scTok INC_OP) scLvalue (\x1 x2 -> PreOp (loc x1) (OpAdd $ loc x1) x2)
         <|> apA2 (scTok DEC_OP) scLvalue (\x1 x2 -> PreOp (loc x1) (OpSub $ loc x1) x2)
         <|> scPostfixOp) <?> "prefix op"

scPostfixOp :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scPostfixOp = ((scLvalue >>= \x1 ->
                    apA (scTok INC_OP) (\x2 -> PostOp (loc x1) (OpAdd (loc x2)) x1)
                <|> apA (scTok DEC_OP) (\x2 -> PostOp (loc x1) (OpSub (loc x2)) x1)
              )
          <||> scUnaryExpression) <?> "postix op"

scUnaryExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scUnaryExpression = liftM unaryLitExpr (apA2 (scChar '~') scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpInv (loc x1)) x2)
                <|> apA2 (scChar '!') scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpNot (loc x1)) x2)
                <|> apA2 (scChar '-') scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpSub (loc x1)) x2)
                <|> scPostfixExpression) <?> "unary expression"

scPostfixExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scPostfixExpression = scFoldl f scPostfixExpression' (scSubscript >+< (scChar '.' *> scAttributeId))
    where
    f pe (Left s) = return $ PostIndexExpr (loc pe) pe s
    f pe (Right v) = return $ SelectionExpr (loc pe) pe v

scPostfixExpression' :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scPostfixExpression' = (apA2 (scTok DOMAINID) (scParens scSecTypeSpecifier) (\x1 x2 -> DomainIdExpr (loc x1) x2)
                  <|> apA2 (scTok STRINGFROMBYTES) (scParens scExpression) (\x1 x2 -> StringFromBytesExpr (loc x1) x2)
                  <|> apA2 (scTok BYTESFROMSTRING) (scParens scExpression) (\x1 x2 -> BytesFromStringExpr (loc x1) x2)
                  <|> apA2 (scTok VSIZE) (scParens scExpression) (\x1 x2 -> VArraySizeExpr (loc x1) x2)
                  <|> apA2 (scTok LEAK) (scParens scExpression) (\x1 x2 -> LeakExpr (loc x1) x2)
                  <|> apA2 (scTok VARRAY) (scParens (apA2 scExpression (scChar ',' >> scExpression) (,))) (\x1 (x2,x3) -> VArrayExpr (loc x1) x2 x3)
                  <|> apA3 scProcedureId
                      (optionMaybe $ scABrackets scTemplateTypeArguments)
                      (scParens (optionMaybe scVariadicExpressionList))
                      (\x1 x2 x3 -> ProcCallExpr (loc x1) x1 x2 (maybe [] id x3))
                  <||> scQuantifiedExpr
                  <||> scPrimaryExpression) <?> "postfix expression"

scQuantifiedExpr :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scQuantifiedExpr = apA4 scQuantifier (sepBy1 scQVar (scChar ',')) (scChar ';') scExpression (\x1 x2 x3 x4 -> QuantifiedExpr (loc x1) x1 x2 x4)
    where
    scQVar = scTypeSpecifier $ \x -> do
        y <- scVarId
        return (x,y)
    
scQuantifier :: (Monad m,MonadCatch m) => ScParserT m (Quantifier Position)
scQuantifier = apA (scTok FORALL) (\x1 -> ForallQ (loc x1))
           <|> apA (scTok EXISTS) (\x1 -> ForallQ (loc x1))

scPrimaryExpression :: (Monad m,MonadCatch m) => ScParserT m (Expression Identifier Position)
scPrimaryExpression = (scParens scExpression
                  <|> scCBrackets' (\x1 -> apA scExpressionList (ArrayConstructorPExpr (loc x1)))
                  <|> apA scVarId (\x1 -> RVariablePExpr (loc x1) x1)
                  <|> apA (scTok RESULT) (\x1 -> ResultExpr (loc x1))
                  <|> apA scLiteral (\x1 -> LitPExpr (loc x1) x1)) <?> "primary expression"

scStringLiteral :: (Monad m,MonadCatch m) => ScParserT m (Loc Position String)
scStringLiteral = apA (many1 "scStringLiteral" scStringPart) mergeStrs <?> "string literal"
    where
    mergeStrs xs = Loc (loc $ headNote "head parsec" xs) (concatMap unLoc xs)

scStringPart :: (Monad m,MonadCatch m) => ScParserT m (Loc Position String)
scStringPart = (apA scStrIdentifier (\x1 -> Loc (loc x1) (tokenString x1))
           <|> apA scStrFragment (\x1 -> Loc (loc x1) (tokenString x1))) <?> "string part"


scBoolLiteral :: (Monad m,MonadCatch m) => ScParserT m (Loc Position Bool)
scBoolLiteral = (apA (scTok TRUE_B) (\x1 -> Loc (loc x1) (tokenBool x1))
            <|> apA (scTok FALSE_B) (\x1 -> Loc (loc x1) (tokenBool x1))) <?> "bool literal"

scLiteral :: (Monad m,MonadCatch m) => ScParserT m (Literal Position)
scLiteral = (apA scIntLiteral (\x1 -> IntLit (loc x1) (unLoc x1))
        <|> apA scStringLiteral (\x1 -> StringLit (loc x1) (unLoc x1))
        <|> apA scBoolLiteral (\x1 -> BoolLit (loc x1) (unLoc x1))
        <|> apA scFloatLiteral (\x1 -> FloatLit (loc x1) (unLoc x1))) <?> "literal"

-- ** Annotations

scGlobalAnnotations :: (MonadIO m,MonadCatch m) => ScParserT m [GlobalAnnotation Identifier Position]
scGlobalAnnotations = scAnnotations1 $ many1 "scGlobalAnnotations" scGlobalAnnotation

scGlobalAnnotation :: (MonadIO m,MonadCatch m) => ScParserT m (GlobalAnnotation Identifier Position)
scGlobalAnnotation = apA3 (scTok TEMPLATE) (scABrackets scTemplateQuantifiers) scProcedureDeclaration (\x1 x2 x3 -> GlobalProcedureAnn (loc x1) x2 x3)
                 <|> apA scProcedureDeclaration (\x1 -> GlobalProcedureAnn (loc x1) [] x1)

scLoopAnnotations :: (MonadIO m,MonadCatch m) => ScParserT m [LoopAnnotation Identifier Position]
scLoopAnnotations = scAnnotations0 $ many "scLoopAnnotations" scLoopAnnotation

scLoopAnnotation :: (MonadIO m,MonadCatch m) => ScParserT m (LoopAnnotation Identifier Position)
scLoopAnnotation = apA3 (scTok DECREASES) scExpression (scChar ';') (\x1 x2 x3 -> DecreasesAnn (loc x1) x2)
               <|> apA3 (scTok INVARIANT) scExpression (scChar ';') (\x1 x2 x3 -> InvariantAnn (loc x1) x2)

scProcedureAnnotations :: (MonadIO m,MonadCatch m) => ScParserT m [ProcedureAnnotation Identifier Position]
scProcedureAnnotations = scAnnotations0 $ many "scProcedureAnnotations" scProcedureAnnotation

scProcedureAnnotation :: (MonadIO m,MonadCatch m) => ScParserT m (ProcedureAnnotation Identifier Position)
scProcedureAnnotation = apA3 (scTok REQUIRES) scExpression (scChar ';') (\x1 x2 x3 -> RequiresAnn (loc x1) x2)
                    <|> apA3 (scTok ENSURES) scExpression (scChar ';') (\x1 x2 x3 -> EnsuresAnn (loc x1) x2)
                    <|> apA3 (scTok LEAKS) scExpression (scChar ';') (\x1 x2 x3 -> parseLeaks (loc x1) x2)

parseLeaks :: Position -> Expression Identifier Position -> ProcedureAnnotation Identifier Position
parseLeaks l e = mk l $ LeakExpr l e
    where mk = if hasResult e then EnsuresAnn else RequiresAnn

scStatementAnnotations :: (MonadIO m,MonadCatch m) => ScParserT m [StatementAnnotation Identifier Position]
scStatementAnnotations = scAnnotations1 $ many1 "scStatementAnnotations" scStatementAnnotation

scStatementAnnotation :: (MonadIO m,MonadCatch m) => ScParserT m (StatementAnnotation Identifier Position)
scStatementAnnotation = apA3 (scTok ASSUME) scExpression (scChar ';') (\x1 x2 x3 -> AssumeAnn (loc x1) x2)
                    <|> apA3 (scTok ASSERT) scExpression (scChar ';') (\x1 x2 x3 -> AssertAnn (loc x1) x2)


scAnnotations0 :: (PP a,Monoid a,MonadIO m,MonadCatch m) => ScParserT m a -> ScParserT m a
scAnnotations0 = scAnnotations' (many "scAnnotations0")

scAnnotations1 :: (PP a,Monoid a,MonadIO m,MonadCatch m) => ScParserT m a -> ScParserT m a
scAnnotations1 = scAnnotations' (many1 "scAnnotations1")

scAnnotations' :: (PP a,Monoid a,MonadIO m,MonadCatch m) => (forall b . ScParserT m b -> ScParserT m [b]) -> ScParserT m a -> ScParserT m a
scAnnotations' parseAnns parse = do
    insideAnn <- getState
    if insideAnn
        then parse
        else do
            toks <- parseAnns (scTokWith getAnn)
            let anns = unlines $ concat $ map ((\(ANNOTATION x) -> x) . tSymb) toks
            p <- scLoc $ headMay toks
            lift $ catchError
                (parseSecreCWith (ppr p) anns True (positionToAlexPos p) $ do
                    setPosition (positionToSourcePos p)
                    parse <* scEOF
                )
                (\e -> warn p e >> return mempty)
            
  where
    getAnn tok@(tSymb -> ANNOTATION a) = Just tok
    getAnn tok = Nothing

-- * Parsing functions

parseFileIO :: Options -> String -> IO (Module Identifier Position)
parseFileIO opts fn = runSecrecM opts $ parseFile fn

parseFile :: (MonadIO m,MonadCatch m) => String -> SecrecM m (Module Identifier Position)
parseFile fn = do
    str <- liftIO (readFile fn)
    x <- parseSecreC fn str
    return x

parseSecreCIO :: Options -> String -> String -> IO (Module Identifier Position)
parseSecreCIO opts fn str = runSecrecM opts $ parseSecreC fn str

parseSecreCIOWith :: PP a => Options -> String -> String -> Bool -> AlexPosn -> ScParserT IO a -> IO a
parseSecreCIOWith opts fn str insideAnn pos parse = runSecrecM opts $ parseSecreCWith fn str insideAnn pos parse

parseSecreC :: (MonadIO m,MonadCatch m) => String -> String -> SecrecM m (Module Identifier Position)
parseSecreC fn str = parseSecreCWith fn str False alexStartPos scModuleFile

parseSecreCWith :: (MonadIO m,PP a) => String -> String -> Bool -> AlexPosn -> ScParserT m a -> SecrecM m a
parseSecreCWith fn str insideAnn pos parser = do
    case runLexerWith fn str pos return of
        Left err -> throwError $ parserError $ LexicalException err
        Right toks -> do
            opts <- ask
            when (debugLexer opts) $ liftIO $ hPutStrLn stderr ("Lexed " ++ fn ++ ":") >> hPutStrLn stderr (show $ map tSymb toks)
            e <- runParserT parser insideAnn fn toks
            case e of
                Left err -> throwError $ parserError $ ParsecException $ show err
                Right a -> do
                    when (debugParser opts) $ liftIO $ hPutStrLn stderr ("Parsed " ++ fn ++ ":") >> hPutStrLn stderr (ppr a)
                    return a
scPosition :: (Monad m,MonadCatch m) => ScParserT m Position
scPosition = liftM sourcePosToPosition getPosition
