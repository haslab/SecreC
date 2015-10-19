{-# LANGUAGE TupleSections #-}

module Language.SecreC.Parser.Parsec where

import Language.SecreC.Position
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Monad
import Language.SecreC.Pretty
import Language.SecreC.Parser.Tokens
import Language.SecreC.Parser.Lexer

import Text.Parsec
import Text.Parsec.Pos

import Control.Applicative hiding ((<|>),optional,many)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ask)
import Control.Monad.Identity

import System.IO

import qualified Data.Foldable as Foldable

type ScParserT u m a = ParsecT [TokenInfo] u m a

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

scTok :: Monad m => Token -> ScParserT u m TokenInfo
scTok t = scTokPred ((==t) . tSymb)

scTokPred :: Monad m => (TokenInfo -> Bool) -> ScParserT u m TokenInfo
scTokPred p = scTokWith (\x -> if p x then Just x else Nothing)

scTokWith :: Monad m => (TokenInfo -> Maybe a) -> ScParserT u m a
scTokWith f = tokenPrim ppr next f
    where
    next p t (s:ss) = positionToSourcePos $ tLoc s
    next p t [] = updatePosString p (ppr t)

scChar :: Monad m => Char -> ScParserT u m TokenInfo
scChar c = scTokPred (p . tSymb)
    where
    p (CHAR c') = c == c'
    p _ = False

scBraces :: Monad m => ScParserT u m a -> ScParserT u m a
scBraces p = scChar '(' *> p <* scChar ')'

scBraces' :: Monad m => (TokenInfo -> ScParserT u m a) -> ScParserT u m a
scBraces' p = do
    x1 <- scChar '('
    x <- p x1
    scChar ')'
    return x

scBrackets :: Monad m => ScParserT u m a -> ScParserT u m a
scBrackets p = scChar '[' *> p <* scChar ']'

scBrackets' :: Monad m => (TokenInfo -> ScParserT u m a) -> ScParserT u m a
scBrackets' p = do
    x1 <- scChar '['
    x <- p x1
    scChar ']'
    return x

scABrackets :: Monad m => ScParserT u m a -> ScParserT u m a
scABrackets p = scChar '<' *> p <* scChar '>'

scCBrackets :: Monad m => ScParserT u m a -> ScParserT u m a
scCBrackets p = scChar '{' *> p <* scChar '}'

scCBrackets' :: Monad m => (TokenInfo -> ScParserT u m a) -> ScParserT u m a
scCBrackets' p = do
    x1 <- scChar '{'
    x <- p x1
    scChar '}'
    return x

scFoldl1 :: Monad m => (a -> b -> ScParserT u m a) -> ScParserT u m a -> ScParserT u m b -> ScParserT u m a
scFoldl1 f ma mb = do
    x <- ma
    ys <- many1 mb
    Foldable.foldlM f x ys
    
scFoldl :: Monad m => (a -> b -> ScParserT u m a) -> ScParserT u m a -> ScParserT u m b -> ScParserT u m a
scFoldl f ma mb = do
    x <- ma
    ys <- many mb
    Foldable.foldlM f x ys

scMaybeCont :: ScParserT u m a -> (Maybe a -> ScParserT u m b) -> ScParserT u m b
scMaybeCont p cont = (p >>= cont . Just) <||> cont Nothing
                
scMaybeContPair :: ScParserT u m a -> ScParserT u m b -> ScParserT u m (Maybe a,b)
scMaybeContPair p cont = scMaybeCont p (\mb -> liftM (mb,) cont)

-- * Grammar

-- ** Literals

scIntLiteral :: Monad m => ScParserT u m (Loc Position Integer)
scIntLiteral = liftM (\x1 -> Loc (loc x1) (tokenInteger x1)) (scTokPred p) <?> "int literal"
    where
    p (TokenInfo (BIN_LITERAL _) _ _) = True
    p (TokenInfo (DEC_LITERAL _) _ _) = True
    p (TokenInfo (HEX_LITERAL _) _ _) = True
    p (TokenInfo (OCT_LITERAL _) _ _) = True
    p _ = False

scFloatLiteral :: Monad m => ScParserT u m (Loc Position Float)
scFloatLiteral = liftM (\x1 -> Loc (loc x1) (tokenFloat x1)) (scTokPred p) <?> "float literal"
    where
    p (TokenInfo (FLOAT_LITERAL _) _ _) = True
    p _ = False

scStrFragment :: Monad m => ScParserT u m TokenInfo
scStrFragment = scTokPred p <?> "string fragment"
    where
    p (TokenInfo (STR_FRAGMENT _) _ _) = True
    p _ = False

scStrIdentifier :: Monad m => ScParserT u m TokenInfo
scStrIdentifier = scTokPred p <?> "string identifier"
    where
    p (TokenInfo (STR_IDENTIFIER _) _ _) = True
    p _ = False

-- ** Identifiers

scKindId :: Monad m => ScParserT u m (KindName Position)
scKindId = liftM (\t -> KindName (tLoc t) (tokenString t)) scIdentifier <?> "kind id"

scVarId :: Monad m => ScParserT u m (VarName Position)
scVarId = liftM (\t -> VarName (tLoc t) (tokenString t)) scIdentifier <?> "variable id"

scAttributeId :: Monad m => ScParserT u m (AttributeName Position)
scAttributeId = liftM (\t -> AttributeName (tLoc t) (tokenString t)) scIdentifier <?> "attribute id"

scProcedureId :: Monad m => ScParserT u m (ProcedureName Position)
scProcedureId = liftM (\t -> ProcedureName (tLoc t) (tokenString t)) scIdentifier <?> "procedure id"

scDomainId :: Monad m => ScParserT u m (DomainName Position)
scDomainId = liftM (\t -> DomainName (tLoc t) (tokenString t)) scIdentifier <?> "domain id"

scTypeId :: Monad m => ScParserT u m (TypeName Position)
scTypeId = liftM (\t -> TypeName (tLoc t) (tokenString t)) scIdentifier <?> "type id"

scTemplateArgId :: Monad m => ScParserT u m (TemplateArgName Position)
scTemplateArgId = liftM (\t -> TemplateArgName (tLoc t) (tokenString t)) scIdentifier <?> "template argument id"

scModuleId :: Monad m => ScParserT u m (ModuleName Position)
scModuleId = liftM (\t -> ModuleName (tLoc t) (tokenString t)) scIdentifier <?> "module id"

scIdentifier :: Monad m => ScParserT u m TokenInfo
scIdentifier = scTokPred (p . tSymb) <?> "id"
    where
    p (IDENTIFIER s) = True
    p _ = False

scEOF :: Monad m => ScParserT u m ()
scEOF = scTokPred (p . tSymb) >> return ()
    where
    p TokenEOF = True
    p _ = False

-- ** Program and variable declarations

scModuleFile :: Monad m => ScParserT u m (Module Position)
scModuleFile = scModule <* scEOF

scModule :: Monad m => ScParserT u m (Module Position)
scModule = ((apA4 (scTok MODULE) scModuleId (scChar ';') scProgram (\x1 x2 x3 x4 -> Module (loc x1) (Just x2) x4) <?> "named module")
       <|> (apA scProgram (\x1 -> Module (loc x1) Nothing x1) <?> "unamed module")
       )
    
scProgram :: Monad m => ScParserT u m (Program Position)
scProgram = apA2 scImportDeclarations scGlobalDeclarations (\x1 x2 -> Program (if null x1 then loc x2 else loc x1) x1 x2) <?> "program"

scImportDeclarations :: Monad m => ScParserT u m [ImportDeclaration Position]
scImportDeclarations = many scImportDeclaration <?> "import declarations"

scGlobalDeclarations :: Monad m => ScParserT u m [GlobalDeclaration Position]
scGlobalDeclarations = many1 scGlobalDeclaration <?> "global declarations"

scImportDeclaration :: Monad m => ScParserT u m (ImportDeclaration Position)
scImportDeclaration = apA3 (scTok IMPORT) scModuleId (scChar ';') (\x1 x2 x3 -> Import (loc x1) x2) <?> "import declaration"

scGlobalDeclaration :: Monad m => ScParserT u m (GlobalDeclaration Position)
scGlobalDeclaration = (apA2 scVariableDeclaration (scChar ';') (\x1 x2 -> GlobalVariable (loc x1) x1) <?> "variable declaration")
                 <||> (apA2 scDomainDeclaration (scChar ';') (\x1 x2 -> GlobalDomain (loc x1) x1) <?> "domain declaration")
                 <||> (apA2 scKindDeclaration (scChar ';') (\x1 x2 -> GlobalKind (loc x1) x1) <?> "kind declaration")
                 <||> (apA scProcedureDeclaration (\x1 -> GlobalProcedure (loc x1) x1) <?> "procedure declaration")
                 <||> (apA scStructureDeclaration (\x1 -> GlobalStructure (loc x1) x1) <?> "structure declaration")
                 <||> (apA scTemplateDeclaration (\x1 -> GlobalTemplate (loc x1) x1) <?> "template declaration")

scKindDeclaration :: Monad m => ScParserT u m (KindDeclaration Position)
scKindDeclaration = apA2 (scTok KIND) scKindId (\x1 x2 -> Kind (loc x1) x2) <?> "kind declaration"

scDomainDeclaration :: Monad m => ScParserT u m (DomainDeclaration Position)
scDomainDeclaration = apA3 (scTok DOMAIN) scDomainId scKindId (\x1 x2 x3 -> Domain (loc x1) x2 x3) <?> "domain declaration"

scVariableInitialization :: Monad m => ScParserT u m (VariableInitialization Position)
scVariableInitialization = apA3 scVarId (optionMaybe scDimensions) (optionMaybe (scChar '=' *> scExpression)) (\x1 x2 x3 -> VariableInitialization (loc x1) x1 x2 x3) <?> "variable initialization"

scVariableInitializations :: Monad m => ScParserT u m (NeList (VariableInitialization Position))
scVariableInitializations = apA (sepBy1 scVariableInitialization (scChar ',')) fromListNe <?> "variable initializations"

scVariableDeclaration :: Monad m => ScParserT u m (VariableDeclaration Position)
scVariableDeclaration = scTypeSpecifier $ \x1 -> apA scVariableInitializations (\x2 -> VariableDeclaration (loc x1) x1 x2) <?> "variable declaration"

scProcedureParameter :: Monad m => ScParserT u m (ProcedureParameter Position)
scProcedureParameter = scTypeSpecifier $ \x1 -> apA scVarId (\x2 -> ProcedureParameter (loc x1) x1 x2) <?> "procedure parameter"

scDimensions :: Monad m => ScParserT u m (Sizes Position)
scDimensions = apA (scBraces scDimensionList) Sizes <?> "dimensions"

scExpressionList :: Monad m => ScParserT u m (NeList (Expression Position))
scExpressionList = apA (sepBy1 scExpression (scChar ',')) fromListNe <?> "expression list"

scDimensionList :: Monad m => ScParserT u m (NeList (Expression Position))
scDimensionList = scExpressionList <?> "dimension list"

-- ** Types                                                                     

scTypeSpecifier :: Monad m => (TypeSpecifier Position -> ScParserT u m a) -> ScParserT u m a
scTypeSpecifier cont = (scMaybeCont scSecTypeSpecifier $ \x1 -> do
    x2 <- scDatatypeSpecifier
    x3 <- optionMaybe scDimtypeSpecifier
    let t = TypeSpecifier (maybe (loc x2) loc x1) x1 x2 x3
    cont t) <?> "type specifier"

scSecTypeSpecifier :: Monad m => ScParserT u m (SecTypeSpecifier Position)
scSecTypeSpecifier = (apA (scTok PUBLIC) (\x1 -> PublicSpecifier (loc x1)) <?> "public security type")
                 <|> (apA scDomainId (\x1 -> PrivateSpecifier (loc x1) x1) <?> "private security type")

scDatatypeSpecifier :: Monad m => ScParserT u m (DatatypeSpecifier Position)
scDatatypeSpecifier = (apA scPrimitiveDatatype (\x1 -> PrimitiveSpecifier (loc x1) x1) <?> "primitive type specifier")
                  <|> (scTemplateStructDatatypeSpecifier <?> "template type specifier")
                  <||> (apA scTypeId (\x1 -> VariableSpecifier (loc x1) x1) <?> "named type specifier")

scPrimitiveDatatype :: Monad m => ScParserT u m (PrimitiveDatatype Position)
scPrimitiveDatatype = (apA (scTok BOOL) (DatatypeBool . loc)
                  <|> apA (scTok INT) (DatatypeInt . loc)
                  <|> apA (scTok UINT) (DatatypeUint . loc)
                  <|> apA (scTok INT8) (DatatypeInt8 . loc)
                  <|> apA (scTok UINT8) (DatatypeUint8 . loc)
                  <|> apA (scTok INT16) (DatatypeUint16 . loc)
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
                  <|> apA (scTok XOR_UINT) (DatatypeXorUint . loc)
                  <|> apA (scTok FLOAT) (DatatypeFloat . loc)
                  <|> apA (scTok FLOAT32) (DatatypeFloat32 . loc)
                  <|> apA (scTok FLOAT64) (DatatypeFloat64 . loc)) <?> "primitive type"

scTemplateStructDatatypeSpecifier :: Monad m => ScParserT u m (DatatypeSpecifier Position)
scTemplateStructDatatypeSpecifier = apA2 scTypeId (scABrackets scTemplateTypeArguments) (\x1 x2 -> TemplateSpecifier (loc x1) x1 x2) <?> "template struct specifier"

scTemplateTypeArguments :: Monad m => ScParserT u m [TemplateTypeArgument Position]
scTemplateTypeArguments = sepBy1 scTemplateTypeArgument (scChar ',') <?> "template type arguments"

scTemplateTypeArgument :: Monad m => ScParserT u m (TemplateTypeArgument Position)
scTemplateTypeArgument = (apA (scTok PUBLIC) (PublicTemplateTypeArgument . loc) <?> "public template type argument")
                     <|> (apA2 scTypeId (scABrackets scTemplateTypeArguments) (\x1 x2 -> TemplateTemplateTypeArgument (loc x1) x1 x2) <?> "template template type argument")
                    <||> (apA scTemplateArgId (\x1 -> GenericTemplateTypeArgument (loc x1) x1) <?> "named template type argument") -- type, domain or variable identifier
                     <|> (apA scIntLiteral (\x1 -> IntTemplateTypeArgument (loc x1) (unLoc x1)) <?> "literal template type argument")
                     <|> (apA scPrimitiveDatatype (\x1 -> PrimitiveTemplateTypeArgument (loc x1) x1) <?> "primitive template type argument")

scDimtypeSpecifier :: Monad m => ScParserT u m (DimtypeSpecifier Position)
scDimtypeSpecifier = (scBrackets' $ \x1 -> scBrackets' $ \x2 ->
      apA scExpression (\x3 -> DimSpecifier (loc x1) x3)) <?> "dimension specifier"

-- ** Templates                                                               

scTemplateDeclaration :: Monad m => ScParserT u m (TemplateDeclaration Position)
scTemplateDeclaration = (do
    x1 <- scTok TEMPLATE
    x3 <- scABrackets scTemplateQuantifiers
    (    apA scStructure (templStruct x1 x3)
     <|> apA scProcedureDeclaration  (\x5 -> TemplateProcedureDeclaration (loc x1) x3 x5))) <?> "template declaration"
  where
    templStruct x1 x3 (Nothing,x5) = TemplateStructureDeclaration (loc x1) x3 x5
    templStruct x1 x3 (Just x4,x5) = TemplateStructureSpecialization (loc x1) x3 x4 x5

scTemplateQuantifiers :: Monad m => ScParserT u m [TemplateQuantifier Position]
scTemplateQuantifiers = (Text.Parsec.sepBy scTemplateQuantifier (scChar ',')) <?> "template quantifiers"

scTemplateQuantifier :: Monad m => ScParserT u m (TemplateQuantifier Position)
scTemplateQuantifier =
        (apA3 (scTok DOMAIN) scDomainId (optionMaybe (scChar ':' *> scKindId)) (\x1 x2 x3 -> DomainQuantifier (loc x1) x2 x3)
    <|> apA2 (scTok DIMENSIONALITY) scVarId (\x1 x2 -> DimensionQuantifier (loc x1) x2)
    <|> apA2 (scTok TYPE) scTypeId (\x1 x2 -> DataQuantifier (loc x1) x2)) <?> "template quantifier"

-- ** Structures                                                                 

scStructure :: Monad m => ScParserT u m (Maybe [TemplateTypeArgument Position],StructureDeclaration Position)
scStructure = apA4 (scTok STRUCT) scTypeId (optionMaybe $ scABrackets scTemplateTypeArguments) (scCBrackets scAttributeList) (\x1 x2 x3 x4 -> (x3,StructureDeclaration (loc x1) x2 x4)) <?> "structure declaration"

scStructureDeclaration :: Monad m => ScParserT u m (StructureDeclaration Position)
scStructureDeclaration = apA3 (scTok STRUCT) scTypeId (scCBrackets scAttributeList) (\x1 x2 x3 -> StructureDeclaration (loc x1) x2 x3) <?> "structure declaration"

scAttributeList :: Monad m => ScParserT u m [Attribute Position]
scAttributeList = many scAttribute <?> "attribute list"

scAttribute :: Monad m => ScParserT u m (Attribute Position)
scAttribute = scTypeSpecifier $ \x1 -> apA2 scAttributeId (scChar ';') (\x2 x3 -> Attribute (loc x1) x1 x2) <?> "attribute"

-- ** Procedures                                

scReturnTypeSpecifier :: Monad m => (ReturnTypeSpecifier Position -> ScParserT u m a) -> ScParserT u m a
scReturnTypeSpecifier cont = ((apA (scTok VOID) (\x1 -> ReturnType (loc x1) Nothing) >>= cont)
                         <|> scTypeSpecifier (\x1 -> let s = ReturnType (loc x1) (Just x1) in cont s))
                          <?> "return type specifier"

scProcedureDeclaration :: Monad m => ScParserT u m (ProcedureDeclaration Position)
scProcedureDeclaration = ((scReturnTypeSpecifier $ \x1 -> apA4 (scTok OPERATOR) scOp (scBraces scProcedureParameterList) scCompoundStatement (\x2 x3 x4 x5 -> OperatorDeclaration (loc x1) x1 x3 x4 (unLoc x5)))
                    <||> (scReturnTypeSpecifier $ \x1 -> apA3 scProcedureId (scBraces scProcedureParameterList) scCompoundStatement (\x2 x3 x4 -> ProcedureDeclaration (loc x1) x1 x2 x3 (unLoc x4)))) <?> "procedure definition"
    
scProcedureParameterList :: Monad m => ScParserT u m [ProcedureParameter Position]
scProcedureParameterList = sepBy1 scProcedureParameter (scChar ',') <?> "procedure parameters"

scOp :: Monad m => ScParserT u m (Op Position)
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
   <|> apA (scChar '!') (OpExcM . loc)
   <|> apA (scTok EQ_OP) (OpEq . loc)
   <|> apA (scTok GE_OP) (OpGe . loc)
   <|> apA (scTok LAND_OP) (OpLand . loc)
   <|> apA (scTok LE_OP) (OpLe . loc)
   <|> apA (scTok LOR_OP) (OpLor . loc)
   <|> apA (scTok NE_OP) (OpNe . loc)
   <|> apA (scTok SHL_OP) (OpShl . loc)
   <|> apA (scTok SHR_OP) (OpShr . loc)) <?> "op"

-- * Statements                                                           

scCompoundStatement :: Monad m => ScParserT u m (Loc Position [Statement Position])
scCompoundStatement = scCBrackets' $ \x1 -> apA (many scStatement) (\x2 -> Loc (loc x1) x2) <?> "compound statement"

scStatement :: Monad m => ScParserT u m (Statement Position)
scStatement = (apA scCompoundStatement (\x1 -> CompoundStatement (loc x1) (unLoc x1))
          <|> scIfStatement
          <|> scForStatement
          <|> scWhileStatement
          <|> scDowhileStatement
          <|> scAssertStatement
          <|> scPrintStatement
          <|> scSyscallStatement
          <|> apA2 scVariableDeclaration (scChar ';') (\x1 x2 -> VarStatement (loc x1) x1)
          <||> apA3 (scTok RETURN) (optionMaybe scExpression) (scChar ';') (\x1 x2 x3 -> ReturnStatement (loc x1) x2)
          <|> apA2 (scTok CONTINUE) (scChar ';') (\x1 x2 -> ContinueStatement (loc x1))
          <|> apA2 (scTok BREAK) (scChar ';') (\x1 x2 -> BreakStatement (loc x1))
          <|> apA (scChar ';') (\x1 -> CompoundStatement (loc x1) [])
          <|> apA2 scExpression (scChar ';') (\x1 x2 -> ExpressionStatement (loc x1) x1)
        ) <?> "statement"

scIfStatement :: Monad m => ScParserT u m (Statement Position)
scIfStatement = apA4 (scTok IF) (scBraces scExpression) scStatement (optionMaybe (scTok ELSE *> scStatement)) (\x1 x2 x3 x4 -> IfStatement (loc x1) x2 x3 x4) <?> "if statement"

scForInitializer :: Monad m => ScParserT u m (ForInitializer Position)
scForInitializer = (apA scVariableDeclaration InitializerVariable
               <||> apA (optionMaybe scExpression) InitializerExpression
             ) <?> "for initializer"

scForStatement :: Monad m => ScParserT u m (Statement Position)
scForStatement = (do
    x1 <- scTok FOR
    scChar '('
    x2 <- scForInitializer
    scChar ';'
    x3 <- optionMaybe scExpression
    scChar ';'
    x4 <- optionMaybe scExpression
    scChar ')'
    x5 <- scStatement
    return $ ForStatement (loc x1) x2 x3 x4 x5) <?> "for statement"

scWhileStatement :: Monad m => ScParserT u m (Statement Position)
scWhileStatement = apA3 (scTok WHILE) (scBraces scExpression) scStatement (\x1 x2 x3 -> WhileStatement (loc x1) x2 x3)
    <?> "while statement"

scPrintStatement :: Monad m => ScParserT u m (Statement Position)
scPrintStatement = apA3 (scTok PRINT) (scBraces scExpressionList) (scChar ';') (\x1 x2 x3 -> PrintStatement (loc x1) x2)
    <?> "print statement"

scDowhileStatement :: Monad m => ScParserT u m (Statement Position)
scDowhileStatement = apA5 (scTok DO) scStatement (scTok WHILE) (scBraces scExpression) (scChar ';') (\x1 x2 x3 x4 x5 -> DowhileStatement (loc x1) x2 x4)
    <?> "dowhile statement"

scAssertStatement :: Monad m => ScParserT u m (Statement Position)
scAssertStatement = apA3 (scTok ASSERT) (scBraces scExpression) (scChar ';') (\x1 x2 x3 -> AssertStatement (loc x1) x2)
    <?> "assert statement"

scSyscallStatement :: Monad m => ScParserT u m (Statement Position)
scSyscallStatement = apA3 (scTok SYSCALL) (scBraces sysparams) (scChar ';') (\x1 (x2,x3) x4 -> SyscallStatement (loc x1) x2 x3)
  <?> "syscall statement"
    where
    sysparams = liftM unLoc scStringLiteral
            >*< many (scChar ',' *> scSyscallParameter)

scSyscallParameter :: Monad m => ScParserT u m (SyscallParameter Position)
scSyscallParameter = (apA2 (scTok SYSCALL_RETURN) scVarId (\x1 x2 -> SyscallReturn (loc x1) x2)
                 <|> apA2 (scTok REF) scVarId (\x1 x2 -> SyscallPushRef (loc x1) x2)
                 <|> apA2 (scTok CREF) scExpression (\x1 x2 -> SyscallPushCRef (loc x1) x2)
                 <|> apA scExpression (\x1 -> SyscallPush (loc x1) x1)) <?> "syscall parameter"

-- ** Indices: not strictly expressions as they only appear in specific context  

scSubscript :: Monad m => ScParserT u m (Subscript Position)
scSubscript = scBrackets scIndices <?> "subsscript"

scIndices :: Monad m => ScParserT u m (NeList (Index Position))
scIndices = apA (sepBy1 scIndex (scChar ',')) fromListNe <?> "indices"

---- Precedence of slicing operator? Right now it binds weakest as it can appear
---- in very specific context. However, if we ever wish for "foo : bar" evaluate
---- to value in some other context we need to figure out sane precedence.
scIndex :: Monad m => ScParserT u m (Index Position)
scIndex = (apA3 (optionMaybe scExpression) (scChar ':') (optionMaybe scExpression) (\x1 x2 x3 -> IndexSlice (maybe (loc x2) loc x1) x1 x3)
     <||> apA scExpression (\x1 -> IndexInt (loc x1) x1)) <?> "index"

-- ** Expressions                                                               

scLvalue :: Monad m => ScParserT u m (PostfixExpression Position)
scLvalue = scPostfixExpression <?> "lvalue"

scExpression :: Monad m => ScParserT u m (Expression Position)
scExpression = scAssignmentExpression <?> "expression"

scAssignmentExpression :: Monad m => ScParserT u m (Expression Position)
scAssignmentExpression = (apA3 scLvalue op scAssignmentExpression (\x1 x2 x3 -> BinaryAssign (loc x1) x1 x2 x3)
                      <||> apA scQualifiedExpression (\x1 -> QualifiedAssignExpr (loc x1) x1)
                     ) <?> "assignment expression"
    where
    op = apA (scChar '=') (const BinaryAssignEqual)
     <|> apA (scTok MUL_ASSIGN) (const BinaryAssignDiv)
     <|> apA (scTok DIV_ASSIGN) (const BinaryAssignDiv)
     <|> apA (scTok MOD_ASSIGN) (const BinaryAssignMod)
     <|> apA (scTok ADD_ASSIGN) (const BinaryAssignAdd)                                                                                
     <|> apA (scTok SUB_ASSIGN) (const BinaryAssignSub)
     <|> apA (scTok AND_ASSIGN) (const BinaryAssignAnd)
     <|> apA (scTok OR_ASSIGN) (const BinaryAssignOr)
     <|> apA (scTok XOR_ASSIGN) (const BinaryAssignXor)

scQualifiedTypes :: Monad m => ScParserT u m (NeList (QualifiedType Position))
scQualifiedTypes = apA (many1 scQualifiedType) fromListNe <?> "qualified types"

scQualifiedType :: Monad m => ScParserT u m (QualifiedType Position)
scQualifiedType = (apA (scTok PUBLIC) (\x1 -> PublicQualifiedType (loc x1))
              <|> apA scPrimitiveDatatype (\x1 -> PrimitiveQualifiedType (loc x1) x1)
              <|> apA scDimtypeSpecifier (\x1 -> DimQualifiedType (loc x1) x1)
              <|> apA scIdentifier (\x1 -> GenericQualifiedType (loc x1) (tokenString x1))) <?> "qualified type"

scQualifiedExpression :: Monad m => ScParserT u m (QualifiedExpression Position)
scQualifiedExpression = scFoldl
    (\qe t -> return $ QualExpr (loc qe) qe t)
    (liftM (\x1 -> QualCond (loc x1) x1) scConditionalExpression)
    (scTok TYPE_QUAL *> scQualifiedTypes) <?> "qualified expression"

scConditionalExpression :: Monad m => ScParserT u m (ConditionalExpression Position)
scConditionalExpression = (do
    x1 <- scLogicalOrExpression 
    mb <- optionMaybe (scChar '?' *> scExpression >*< scChar ':' *> scExpression) 
    case mb of
        Nothing -> return $ LorExpr (loc x1) (LorExpression x1)
        Just (x2,x3) -> return $ CondExpr (loc x1) (LorExpression x1) x2 x3) <?> "conditional expression"

scLogicalOrExpression :: Monad m => ScParserT u m (NeList (LandExpression Position))
scLogicalOrExpression = apA (sepBy1 (liftM LandExpression scLogicalAndExpression) (scTok LOR_OP)) fromListNe <?> "logical or expression"

scLogicalAndExpression :: Monad m => ScParserT u m (NeList (BitwiseOrExpression Position))
scLogicalAndExpression = apA (sepBy1 (liftM BitwiseOrExpression scBitwiseOrExpression) (scTok LAND_OP)) fromListNe <?> "logical and expression"

scBitwiseOrExpression :: Monad m => ScParserT u m (NeList (BitwiseXorExpression Position))
scBitwiseOrExpression = apA (sepBy1 (liftM BitwiseXorExpression scBitwiseXorExpression) (scChar '|')) fromListNe <?> "bitwise or expression"

scBitwiseXorExpression :: Monad m => ScParserT u m (NeList (BitwiseAndExpression Position))
scBitwiseXorExpression = apA (sepBy1 (liftM BitwiseAndExpression scBitwiseAndExpression) (scChar '^')) fromListNe <?> "bitwise xor expression"

scBitwiseAndExpression :: Monad m => ScParserT u m (NeList (EqualityExpression Position))
scBitwiseAndExpression = apA (sepBy1 (liftM EqualityExpression scEqualityExpression) (scChar '&')) fromListNe <?> "bitwise and expression"

scEqualityExpression :: Monad m => ScParserT u m (SepList EqExprOp (RelationalExpression Position))
scEqualityExpression = scFoldl
    (\re1 (op,re2) -> return $ snocSep re1 op $ RelationalExpression re2)
    (liftM (WrapSep . RelationalExpression) scRelationalExpression)
    (ops >*< scRelationalExpression) <?> "equality expression"
  where
    ops = apA (scTok EQ_OP) (const EqOp)
      <|> apA (scTok NE_OP) (const NeOp)

scRelationalExpression :: Monad m => ScParserT u m (SepList RelExprOp (ShiftExpression Position))
scRelationalExpression = scFoldl
    (\se1 (op,se2) -> return $ snocSep se1 op $ ShiftExpression se2)
    (liftM (WrapSep . ShiftExpression) scShiftExpression)
    (ops >*< scShiftExpression) <?> "relational expression"
  where
    ops = apA (scTok LE_OP) (const LeOp)
      <|> apA (scTok GE_OP) (const GeOp)
      <|> apA (scChar '<') (const LtOp)
      <|> apA (scChar '>') (const GtOp)

scShiftExpression :: Monad m => ScParserT u m (SepList ShExprOp (AdditiveExpression Position))
scShiftExpression = scFoldl
    (\a1 (op,a2) -> return $ snocSep a1 op $ AdditiveExpression a2)
    (liftM (WrapSep . AdditiveExpression) scAdditiveExpression)
    (ops >*< scAdditiveExpression) <?> "shift expression"
  where
    ops = apA (scTok SHL_OP) (const ShlOp)
      <|> apA (scTok SHR_OP) (const ShrOp)

scAdditiveExpression :: Monad m => ScParserT u m (SepList AddExprOp (MultiplicativeExpression Position))
scAdditiveExpression = scFoldl
    (\a1 (op,a2) -> return $ snocSep a1 op $ MultiplicativeExpression a2)
    (liftM (WrapSep . MultiplicativeExpression) scMultiplicativeExpression)
    (ops >*< scMultiplicativeExpression) <?> "additive expression"
  where
    ops = apA (scChar '+') (const PlusOp)
      <|> apA (scChar '-') (const MinusOp)

scMultiplicativeExpression :: Monad m => ScParserT u m (SepList MulExprOp (CastExpression Position))
scMultiplicativeExpression = scFoldl
    (\a1 (op,a2) -> return $ snocSep a1 op a2)
    (liftM WrapSep scCastExpression)
    (ops >*< scCastExpression) <?> "multiplicative expression"
  where
    ops = apA (scChar '*') (const MulOp)
      <|> apA (scChar '/') (const DivOp)
      <|> apA (scChar '%') (const ModOp)

scCastExpression :: Monad m => ScParserT u m (CastExpression Position)
scCastExpression = (apA2 (scBraces' types) scCastExpression ($)
            <||> apA scPrefixOp (\x1 -> PrefixCastExpr (loc x1) x1)) <?> "cast expression"
  where
    types x1 = apA scPrimitiveDatatype (\x2 -> PrimCastExpr (loc x1) x2)
           <|> apA scTypeId (\x2 -> VarCastExpr (loc x1) x2)

scPrefixOp :: Monad m => ScParserT u m (PrefixOp Position)
scPrefixOp = (apA2 (scTok INC_OP) scLvalue (\x1 x2 -> PrefixInc (loc x1) x2)
         <|> apA2 (scTok DEC_OP) scLvalue (\x1 x2 -> PrefixDec (loc x1) x2)
         <|> apA scPostfixOp (\x1 -> PrefixPost (loc x1) x1)) <?> "prefix op"

scPostfixOp :: Monad m => ScParserT u m (PostfixOp Position)
scPostfixOp = ((scLvalue >>= \x1 ->
                    apA (scTok INC_OP) (const $ PostfixInc (loc x1) x1)
                <|> apA (scTok DEC_OP) (const $ PostfixDec (loc x1) x1)
              )
          <||> apA scUnaryExpression (\x1 -> PostfixUnary (loc x1) x1)) <?> "postix op"

scUnaryExpression :: Monad m => ScParserT u m (UnaryExpression Position)
scUnaryExpression = (apA2 (scChar '~') scCastExpression (\x1 x2 -> UinvExpr (loc x1) x2)
                <|> apA2 (scChar '!') scCastExpression (\x1 x2 -> UnegExpr (loc x1) x2)
                <|> apA2 (scChar '-') scCastExpression (\x1 x2 -> UminusExpr (loc x1) x2)
                <|> apA scPostfixExpression (\x1 -> Upost (loc x1) x1)) <?> "unary expression"

scPostfixExpression :: Monad m => ScParserT u m (PostfixExpression Position)
scPostfixExpression = scFoldl f scPostfixExpression' (scSubscript >+< (scChar '.' *> scAttributeId))
    where
    f pe (Left s) = return $ PostIndexExpr (loc pe) pe s
    f pe (Right v) = return $ SelectionExpr (loc pe) pe v

scPostfixExpression' :: Monad m => ScParserT u m (PostfixExpression Position)
scPostfixExpression' = (apA2 (scTok DECLASSIFY) (scBraces scExpression) (\x1 x2 -> DeclassifyExpr (loc x1) x2)
                  <|> apA2 (scTok SIZE) (scBraces scExpression) (\x1 x2 -> SizeExpr (loc x1) x2)
                  <|> apA2 (scTok SHAPE) (scBraces scExpression) (\x1 x2 -> ShapeExpr (loc x1) x2)
                  <|> apA scCatExpression (\x1 -> PostCatExpr (loc x1) x1)
                  <|> apA2 (scTok DOMAINID) (scBraces scSecTypeSpecifier) (\x1 x2 -> DomainIdExpr (loc x1) x2)
                  <|> apA2 (scTok RESHAPE) (scBraces scExpressionList) (\x1 x2 -> ReshapeExpr (loc x1) x2)
                  <|> apA2 (scTok TOSTRING) (scBraces scExpression) (\x1 x2 -> ToStringExpr (loc x1) x2)
                  <|> apA2 (scTok STRLEN) (scBraces scExpression) (\x1 x2 -> StrlenExpr (loc x1) x2)
                  <|> apA2 (scTok STRINGFROMBYTES) (scBraces scExpression) (\x1 x2 -> StringFromBytesExpr (loc x1) x2)
                  <|> apA2 (scTok BYTESFROMSTRING) (scBraces scExpression) (\x1 x2 -> BytesFromStringExpr (loc x1) x2)
                  <|> apA2 scProcedureId (scBraces (optionMaybe scExpressionList)) (\x1 x2 -> ProcCallExpr (loc x1) x1 (maybe [] Foldable.toList x2))
                  <||> apA scPrimaryExpression (\x1 -> PostPrimExpr (loc x1) x1)) <?> "postfix expression"

scCatExpression :: Monad m => ScParserT u m (CatExpression Position)
scCatExpression = (do
    x1 <- scTok CAT
    (x2,(x3,x4)) <- scBraces (scExpression <* scChar ',' >*< scExpression >*< optionMaybe (scChar ',' *> scIntLiteral))
    return $ CatExpr (loc x1) x2 x3 (fmap unLoc x4)) <?> "cat expression"

scPrimaryExpression :: Monad m => ScParserT u m (PrimaryExpression Position)
scPrimaryExpression = (scBraces' (\x1 -> apA scExpression (PExpr (loc x1)))
                  <|> scCBrackets' (\x1 -> apA scExpressionList (ArrayConstructorPExpr (loc x1)))
                  <|> apA scVarId (\x1 -> RVariablePExpr (loc x1) x1)
                  <|> apA scLiteral (\x1 -> LitPExpr (loc x1) x1)) <?> "primary expression"

scStringLiteral :: Monad m => ScParserT u m (Loc Position String)
scStringLiteral = apA (many1 scStringPart) mergeStrs <?> "string literal"
    where
    mergeStrs xs = Loc (loc $ head xs) (concatMap unLoc xs)

scStringPart :: Monad m => ScParserT u m (Loc Position String)
scStringPart = (apA scStrIdentifier (\x1 -> Loc (loc x1) (tokenString x1))
           <|> apA scStrFragment (\x1 -> Loc (loc x1) (tokenString x1))) <?> "string part"


scBoolLiteral :: Monad m => ScParserT u m (Loc Position Bool)
scBoolLiteral = (apA (scTok TRUE_B) (\x1 -> Loc (loc x1) (tokenBool x1))
            <|> apA (scTok FALSE_B) (\x1 -> Loc (loc x1) (tokenBool x1))) <?> "bool literal"

scLiteral :: Monad m => ScParserT u m (Literal Position)
scLiteral = (apA scIntLiteral (\x1 -> IntLit (loc x1) (unLoc x1))
        <|> apA scStringLiteral (\x1 -> StringLit (loc x1) (unLoc x1))
        <|> apA scBoolLiteral (\x1 -> BoolLit (loc x1) (unLoc x1))
        <|> apA scFloatLiteral (\x1 -> FloatLit (loc x1) (unLoc x1))) <?> "literal"

-- * Parsing functions

parseFileIO :: Options -> String -> IO (Module Position)
parseFileIO opts fn = ioSecrecM opts $ parseFile fn

parseFile :: String -> SecrecM (Module Position)
parseFile fn = do
    str <- liftIO (readFile fn)
    x <- parseSecreC fn str
    return x

parseSecreCIO :: Options -> String -> String -> IO (Module Position)
parseSecreCIO opts fn str = ioSecrecM opts $ parseSecreC fn str

parseSecreCIOWith :: PP a => Options -> String -> String -> ScParserT () Identity a -> IO a
parseSecreCIOWith opts fn str parse = ioSecrecM opts $ parseSecreCWith fn str parse

parseSecreC :: String -> String -> SecrecM (Module Position)
parseSecreC fn str = parseSecreCWith fn str scModuleFile

parseSecreCWith :: PP a => String -> String -> ScParserT () Identity a -> SecrecM a
parseSecreCWith fn str parser = do
    case runLexer fn str of
        Left err -> throwError $ parserError $ LexicalException err
        Right toks -> do
            opts <- ask
            when (debugLexer opts) $ liftIO $ hPutStrLn stderr ("Lexed " ++ fn ++ ":") >> hPutStrLn stderr (show $ map tSymb toks)
            let e = runParser parser () fn toks
            case e of
                Left err -> throwError $ parserError $ ParsecException err
                Right a -> do
                    when (debugParser opts) $ liftIO $ hPutStrLn stderr ("Parsed " ++ fn ++ ":") >> hPutStrLn stderr (ppr a)
                    return a
        