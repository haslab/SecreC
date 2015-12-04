{-# LANGUAGE TupleSections, TypeFamilies #-}

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

import Text.Parsec
import Text.Parsec.Pos

import Control.Applicative hiding ((<|>),optional,many)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ask)
import Control.Monad.Identity

import System.IO

import Safe

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

scFloatLiteral :: Monad m => ScParserT u m (Loc Position Double)
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

scKindId :: Monad m => ScParserT u m (KindName Identifier Position)
scKindId = liftM (\t -> KindName (tLoc t) (tokenString t)) scIdentifier <?> "kind id"

scVarId :: Monad m => ScParserT u m (VarName Identifier Position)
scVarId = liftM (\t -> VarName (tLoc t) (tokenString t)) scIdentifier <?> "variable id"

scAttributeId :: Monad m => ScParserT u m (AttributeName Identifier Position)
scAttributeId = liftM (\t -> AttributeName (tLoc t) (tokenString t)) scIdentifier <?> "attribute id"

scProcedureId :: Monad m => ScParserT u m (ProcedureName Identifier Position)
scProcedureId = liftM (\t -> ProcedureName (tLoc t) (tokenString t)) scIdentifier <?> "procedure id"

scDomainId :: Monad m => ScParserT u m (DomainName Identifier Position)
scDomainId = liftM (\t -> DomainName (tLoc t) (tokenString t)) scIdentifier <?> "domain id"

scTypeId :: Monad m => ScParserT u m (TypeName Identifier Position)
scTypeId = liftM (\t -> TypeName (tLoc t) (tokenString t)) scIdentifier <?> "type id"

scTemplateArgId :: Monad m => ScParserT u m (TemplateArgName Identifier Position)
scTemplateArgId = liftM (\t -> TemplateArgName (tLoc t) (tokenString t)) scIdentifier <?> "template argument id"

scModuleId :: Monad m => ScParserT u m (ModuleName Identifier Position)
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

scModuleFile :: Monad m => ScParserT u m (Module Identifier Position)
scModuleFile = scModule <* scEOF

scModule :: Monad m => ScParserT u m (Module Identifier Position)
scModule = ((apA4 (scTok MODULE) scModuleId (scChar ';') scProgram (\x1 x2 x3 x4 -> Module (loc x1) (Just x2) x4) <?> "named module")
       <|> (apA scProgram (\x1 -> Module (loc x1) Nothing x1) <?> "unamed module")
       )
    
scProgram :: Monad m => ScParserT u m (Program Identifier Position)
scProgram = do
    p <- scPosition
    apA2 scImportDeclarations scGlobalDeclarations (\x1 x2 -> Program (if null x1 then if null x2 then p else loc (head x2) else loc (head x1)) x1 x2) <?> "program"

scImportDeclarations :: Monad m => ScParserT u m [ImportDeclaration Identifier Position]
scImportDeclarations = many scImportDeclaration <?> "import declarations"

scGlobalDeclarations :: Monad m => ScParserT u m [GlobalDeclaration Identifier Position]
scGlobalDeclarations = many scGlobalDeclaration <?> "global declarations"

scImportDeclaration :: Monad m => ScParserT u m (ImportDeclaration Identifier Position)
scImportDeclaration = apA3 (scTok IMPORT) scModuleId (scChar ';') (\x1 x2 x3 -> Import (loc x1) x2) <?> "import declaration"

scGlobalDeclaration :: Monad m => ScParserT u m (GlobalDeclaration Identifier Position)
scGlobalDeclaration = (apA2 scVariableDeclaration (scChar ';') (\x1 x2 -> GlobalVariable (loc x1) x1) <?> "variable declaration")
                 <||> (apA2 scDomainDeclaration (scChar ';') (\x1 x2 -> GlobalDomain (loc x1) x1) <?> "domain declaration")
                 <||> (apA2 scKindDeclaration (scChar ';') (\x1 x2 -> GlobalKind (loc x1) x1) <?> "kind declaration")
                 <||> (apA scProcedureDeclaration (\x1 -> GlobalProcedure (loc x1) x1) <?> "procedure declaration")
                 <||> (apA scStructureDeclaration (\x1 -> GlobalStructure (loc x1) x1) <?> "structure declaration")
                 <||> (apA scTemplateDeclaration (\x1 -> GlobalTemplate (loc x1) x1) <?> "template declaration")

scKindDeclaration :: Monad m => ScParserT u m (KindDeclaration Identifier Position)
scKindDeclaration = apA2 (scTok KIND) scKindId (\x1 x2 -> Kind (loc x1) x2) <?> "kind declaration"

scDomainDeclaration :: Monad m => ScParserT u m (DomainDeclaration Identifier Position)
scDomainDeclaration = apA3 (scTok DOMAIN) scDomainId scKindId (\x1 x2 x3 -> Domain (loc x1) x2 x3) <?> "domain declaration"

scVariableInitialization :: Monad m => ScParserT u m (VariableInitialization Identifier Position)
scVariableInitialization = apA3 scVarId (optionMaybe scDimensions) (optionMaybe (scChar '=' *> scExpression)) (\x1 x2 x3 -> VariableInitialization (loc x1) x1 x2 x3) <?> "variable initialization"

scVariableInitializations :: Monad m => ScParserT u m (NeList (VariableInitialization Identifier Position))
scVariableInitializations = apA (sepBy1 scVariableInitialization (scChar ',')) fromListNe <?> "variable initializations"

scVariableDeclaration :: Monad m => ScParserT u m (VariableDeclaration Identifier Position)
scVariableDeclaration = scTypeSpecifier $ \x1 -> apA scVariableInitializations (\x2 -> VariableDeclaration (loc x1) x1 x2) <?> "variable declaration"

scProcedureParameter :: Monad m => ScParserT u m (ProcedureParameter Identifier Position)
scProcedureParameter = scTypeSpecifier $ \x1 -> apA scVarId (\x2 -> ProcedureParameter (loc x1) x1 x2) <?> "procedure parameter"

scDimensions :: Monad m => ScParserT u m (Sizes Identifier Position)
scDimensions = apA (scBraces scDimensionList) Sizes <?> "dimensions"

scExpressionList :: Monad m => ScParserT u m (NeList (Expression Identifier Position))
scExpressionList = apA (sepBy1 scExpression (scChar ',')) fromListNe <?> "expression list"

scDimensionList :: Monad m => ScParserT u m (NeList (Expression Identifier Position))
scDimensionList = scExpressionList <?> "dimension list"

-- ** Types                                                                     

scTypeSpecifier :: Monad m => (TypeSpecifier Identifier Position -> ScParserT u m a) -> ScParserT u m a
scTypeSpecifier cont = (scMaybeCont scSecTypeSpecifier $ \x1 -> do
    x2 <- scDatatypeSpecifier
    x3 <- optionMaybe scDimtypeSpecifier
    let t = TypeSpecifier (maybe (loc x2) loc x1) x1 x2 x3
    cont t) <?> "type specifier"

scSecTypeSpecifier :: Monad m => ScParserT u m (SecTypeSpecifier Identifier Position)
scSecTypeSpecifier = (apA (scTok PUBLIC) (\x1 -> PublicSpecifier (loc x1)) <?> "public security type")
                 <|> (apA scDomainId (\x1 -> PrivateSpecifier (loc x1) x1) <?> "private security type")

scDatatypeSpecifier :: Monad m => ScParserT u m (DatatypeSpecifier Identifier Position)
scDatatypeSpecifier = (apA scPrimitiveDatatype (\x1 -> PrimitiveSpecifier (loc x1) x1) <?> "primitive type specifier")
                  <|> (scTemplateStructDatatypeSpecifier <?> "template type specifier")
                  <||> (apA scTypeId (\x1 -> VariableSpecifier (loc x1) x1) <?> "named type specifier")

scPrimitiveDatatype :: Monad m => ScParserT u m (PrimitiveDatatype Position)
scPrimitiveDatatype = (apA (scTok BOOL) (DatatypeBool . loc)
                  <|> apA (scTok INT) (DatatypeInt . loc)
                  <|> apA (scTok UINT) (DatatypeUint . loc)
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
                  <|> apA (scTok XOR_UINT) (DatatypeXorUint . loc)
                  <|> apA (scTok FLOAT) (DatatypeFloat . loc)
                  <|> apA (scTok FLOAT32) (DatatypeFloat32 . loc)
                  <|> apA (scTok FLOAT64) (DatatypeFloat64 . loc)) <?> "primitive type"

scTemplateStructDatatypeSpecifier :: Monad m => ScParserT u m (DatatypeSpecifier Identifier Position)
scTemplateStructDatatypeSpecifier = apA2 scTypeId (scABrackets scTemplateTypeArguments) (\x1 x2 -> TemplateSpecifier (loc x1) x1 x2) <?> "template struct specifier"

scTemplateTypeArguments :: Monad m => ScParserT u m [TemplateTypeArgument Identifier Position]
scTemplateTypeArguments = sepBy1 scTemplateTypeArgument (scChar ',') <?> "template type arguments"

scTemplateTypeArgument :: Monad m => ScParserT u m (TemplateTypeArgument Identifier Position)
scTemplateTypeArgument = (apA (scTok PUBLIC) (PublicTemplateTypeArgument . loc) <?> "public template type argument")
                     <|> (apA2 scTypeId (scABrackets scTemplateTypeArguments) (\x1 x2 -> TemplateTemplateTypeArgument (loc x1) x1 x2) <?> "template template type argument")
                    <||> (apA scTemplateArgId (\x1 -> GenericTemplateTypeArgument (loc x1) x1) <?> "named template type argument") -- type, domain or variable identifier
                     <|> (apA scExpression (\x1 -> ExprTemplateTypeArgument (loc x1) x1) <?> "expression template type argument")
                     <||> (apA scPrimitiveDatatype (\x1 -> PrimitiveTemplateTypeArgument (loc x1) x1) <?> "primitive template type argument")

scDimtypeSpecifier :: Monad m => ScParserT u m (DimtypeSpecifier Identifier Position)
scDimtypeSpecifier = (scBrackets' $ \x1 -> scBrackets' $ \x2 ->
      apA scExpression (\x3 -> DimSpecifier (loc x1) x3)) <?> "dimension specifier"

-- ** Templates                                                               

scTemplateDeclaration :: Monad m => ScParserT u m (TemplateDeclaration Identifier Position)
scTemplateDeclaration = (do
    x1 <- scTok TEMPLATE
    x3 <- scABrackets scTemplateQuantifiers
    (    apA scStructure (templStruct x1 x3)
     <|> apA scProcedureDeclaration  (\x5 -> TemplateProcedureDeclaration (loc x1) x3 x5))) <?> "template declaration"
  where
    templStruct x1 x3 (Nothing,x5) = TemplateStructureDeclaration (loc x1) x3 x5
    templStruct x1 x3 (Just x4,x5) = TemplateStructureSpecialization (loc x1) x3 x4 x5

scTemplateQuantifiers :: Monad m => ScParserT u m [TemplateQuantifier Identifier Position]
scTemplateQuantifiers = (Text.Parsec.sepBy scTemplateQuantifier (scChar ',')) <?> "template quantifiers"

scTemplateQuantifier :: Monad m => ScParserT u m (TemplateQuantifier Identifier Position)
scTemplateQuantifier =
        (apA3 (scTok DOMAIN) scDomainId (optionMaybe (scChar ':' *> scKindId)) (\x1 x2 x3 -> DomainQuantifier (loc x1) x2 x3)
    <|> apA2 (scTok DIMENSIONALITY) scVarId (\x1 x2 -> DimensionQuantifier (loc x1) x2)
    <|> apA2 (scTok TYPE) scTypeId (\x1 x2 -> DataQuantifier (loc x1) x2)) <?> "template quantifier"

-- ** Structures                                                                 

scStructure :: Monad m => ScParserT u m (Maybe [TemplateTypeArgument Identifier Position],StructureDeclaration Identifier Position)
scStructure = apA4 (scTok STRUCT) scTypeId (optionMaybe $ scABrackets scTemplateTypeArguments) (scCBrackets scAttributeList) (\x1 x2 x3 x4 -> (x3,StructureDeclaration (loc x1) x2 x4)) <?> "structure declaration"

scStructureDeclaration :: Monad m => ScParserT u m (StructureDeclaration Identifier Position)
scStructureDeclaration = apA3 (scTok STRUCT) scTypeId (scCBrackets scAttributeList) (\x1 x2 x3 -> StructureDeclaration (loc x1) x2 x3) <?> "structure declaration"

scAttributeList :: Monad m => ScParserT u m [Attribute Identifier Position]
scAttributeList = many scAttribute <?> "attribute list"

scAttribute :: Monad m => ScParserT u m (Attribute Identifier Position)
scAttribute = scTypeSpecifier $ \x1 -> apA2 scAttributeId (scChar ';') (\x2 x3 -> Attribute (loc x1) x1 x2) <?> "attribute"

-- ** Procedures                                

scReturnTypeSpecifier :: Monad m => (ReturnTypeSpecifier Identifier Position -> ScParserT u m a) -> ScParserT u m a
scReturnTypeSpecifier cont = ((apA (scTok VOID) (\x1 -> ReturnType (loc x1) Nothing) >>= cont)
                         <|> scTypeSpecifier (\x1 -> let s = ReturnType (loc x1) (Just x1) in cont s))
                          <?> "return type specifier"

scProcedureDeclaration :: Monad m => ScParserT u m (ProcedureDeclaration Identifier Position)
scProcedureDeclaration = ((scReturnTypeSpecifier $ \x1 -> apA4 (scTok OPERATOR) scOp (scBraces scProcedureParameterList) scCompoundStatement (\x2 x3 x4 x5 -> OperatorDeclaration (loc x1) x1 x3 x4 (unLoc x5)))
                    <||> (scReturnTypeSpecifier $ \x1 -> apA3 scProcedureId (scBraces scProcedureParameterList) scCompoundStatement (\x2 x3 x4 -> ProcedureDeclaration (loc x1) x1 x2 x3 (unLoc x4)))) <?> "procedure definition"
    
scProcedureParameterList :: Monad m => ScParserT u m [ProcedureParameter Identifier Position]
scProcedureParameterList = sepBy scProcedureParameter (scChar ',') <?> "procedure parameters"

scOp :: Monad m => ScParserT u m (Op Identifier Position)
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
   <|> apA scCastType (\x1 -> OpCast (loc x1) x1) ) <?> "op"

-- * Statements                                                           

scCompoundStatement :: Monad m => ScParserT u m (Loc Position [Statement Identifier Position])
scCompoundStatement = scCBrackets' $ \x1 -> apA (many scStatement) (\x2 -> Loc (loc x1) x2) <?> "compound statement"

scStatement :: Monad m => ScParserT u m (Statement Identifier Position)
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

scIfStatement :: Monad m => ScParserT u m (Statement Identifier Position)
scIfStatement = apA4 (scTok IF) (scBraces scExpression) scStatement (optionMaybe (scTok ELSE *> scStatement)) (\x1 x2 x3 x4 -> IfStatement (loc x1) x2 x3 x4) <?> "if statement"

scForInitializer :: Monad m => ScParserT u m (ForInitializer Identifier Position)
scForInitializer = (apA scVariableDeclaration InitializerVariable
               <||> apA (optionMaybe scExpression) InitializerExpression
             ) <?> "for initializer"

scForStatement :: Monad m => ScParserT u m (Statement Identifier Position)
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

scWhileStatement :: Monad m => ScParserT u m (Statement Identifier Position)
scWhileStatement = apA3 (scTok WHILE) (scBraces scExpression) scStatement (\x1 x2 x3 -> WhileStatement (loc x1) x2 x3)
    <?> "while statement"

scPrintStatement :: Monad m => ScParserT u m (Statement Identifier Position)
scPrintStatement = apA3 (scTok PRINT) (scBraces scExpressionList) (scChar ';') (\x1 x2 x3 -> PrintStatement (loc x1) x2)
    <?> "print statement"

scDowhileStatement :: Monad m => ScParserT u m (Statement Identifier Position)
scDowhileStatement = apA5 (scTok DO) scStatement (scTok WHILE) (scBraces scExpression) (scChar ';') (\x1 x2 x3 x4 x5 -> DowhileStatement (loc x1) x2 x4)
    <?> "dowhile statement"

scAssertStatement :: Monad m => ScParserT u m (Statement Identifier Position)
scAssertStatement = apA3 (scTok ASSERT) (scBraces scExpression) (scChar ';') (\x1 x2 x3 -> AssertStatement (loc x1) x2)
    <?> "assert statement"

scSyscallStatement :: Monad m => ScParserT u m (Statement Identifier Position)
scSyscallStatement = apA3 (scTok SYSCALL) (scBraces sysparams) (scChar ';') (\x1 (x2,x3) x4 -> SyscallStatement (loc x1) x2 x3)
  <?> "syscall statement"
    where
    sysparams = liftM unLoc scStringLiteral
            >*< many (scChar ',' *> scSyscallParameter)

scSyscallParameter :: Monad m => ScParserT u m (SyscallParameter Identifier Position)
scSyscallParameter = (apA2 (scTok SYSCALL_RETURN) scVarId (\x1 x2 -> SyscallReturn (loc x1) x2)
                 <|> apA2 (scTok REF) scVarId (\x1 x2 -> SyscallPushRef (loc x1) x2)
                 <|> apA2 (scTok CREF) scExpression (\x1 x2 -> SyscallPushCRef (loc x1) x2)
                 <|> apA scExpression (\x1 -> SyscallPush (loc x1) x1)) <?> "syscall parameter"

-- ** Indices: not strictly expressions as they only appear in specific context  

scSubscript :: Monad m => ScParserT u m (Subscript Identifier Position)
scSubscript = scBrackets scIndices <?> "subsscript"

scIndices :: Monad m => ScParserT u m (NeList (Index Identifier Position))
scIndices = apA (sepBy1 scIndex (scChar ',')) fromListNe <?> "indices"

---- Precedence of slicing operator? Right now it binds weakest as it can appear
---- in very specific context. However, if we ever wish for "foo : bar" evaluate
---- to value in some other context we need to figure out sane precedence.
scIndex :: Monad m => ScParserT u m (Index Identifier Position)
scIndex = (apA3 (optionMaybe scExpression) (scChar ':') (optionMaybe scExpression) (\x1 x2 x3 -> IndexSlice (maybe (loc x2) loc x1) x1 x3)
     <||> apA scExpression (\x1 -> IndexInt (loc x1) x1)) <?> "index"

-- ** Expressions                                                               

scLvalue :: Monad m => ScParserT u m (Expression Identifier Position)
scLvalue = scPostfixExpression <?> "lvalue"

scExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scExpression = scAssignmentExpression <?> "expression"

scAssignmentExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scAssignmentExpression = (apA3 scLvalue op scAssignmentExpression (\x1 x2 x3 -> BinaryAssign (loc x1) x1 x2 x3)
                      <||> scQualifiedExpression
                     ) <?> "assignment expression"
    where
    op = apA (scChar '=') (BinaryAssignEqual . loc)
     <|> apA (scTok MUL_ASSIGN) (BinaryAssignDiv . loc)
     <|> apA (scTok DIV_ASSIGN) (BinaryAssignDiv . loc)
     <|> apA (scTok MOD_ASSIGN) (BinaryAssignMod . loc)
     <|> apA (scTok ADD_ASSIGN) (BinaryAssignAdd . loc)                                                                                
     <|> apA (scTok SUB_ASSIGN) (BinaryAssignSub . loc)
     <|> apA (scTok AND_ASSIGN) (BinaryAssignAnd . loc)
     <|> apA (scTok OR_ASSIGN) (BinaryAssignOr . loc)
     <|> apA (scTok XOR_ASSIGN) (BinaryAssignXor . loc)

scQualifiedExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scQualifiedExpression = scFoldl
    (\qe t -> return $ QualExpr (loc qe) qe t)
    scConditionalExpression
    (scTok TYPE_QUAL *> scTypeSpecifier return) <?> "qualified expression"

scConditionalExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scConditionalExpression = (do
    x1 <- scLogicalOrExpression 
    mb <- optionMaybe (scChar '?' *> scExpression >*< scChar ':' *> scExpression) 
    case mb of
        Nothing -> return x1
        Just (x2,x3) -> return $ CondExpr (loc x1) x1 x2 x3) <?> "conditional expression"

scLogicalOrExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scLogicalOrExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scLogicalAndExpression
    (ops >*< scLogicalAndExpression) <?> "logical or expression"
  where
    ops = apA (scTok LOR_OP) (OpLor . loc)

scLogicalAndExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scLogicalAndExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scBitwiseOrExpression
    (ops >*< scBitwiseOrExpression) <?> "logical and expression"
  where
    ops = apA (scTok LAND_OP) (OpLand . loc)

scBitwiseOrExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scBitwiseOrExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scBitwiseXorExpression
    (ops >*< scBitwiseXorExpression) <?> "bitwise or expression"
  where
    ops = apA (scChar '|') (OpBor . loc)

scBitwiseXorExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scBitwiseXorExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scBitwiseAndExpression
    (ops >*< scBitwiseAndExpression) <?> "bitwise xor expression"
  where
    ops = apA (scChar '^') (OpXor . loc)
    
scBitwiseAndExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scBitwiseAndExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scEqualityExpression
    (ops >*< scEqualityExpression) <?> "bitwise and expression"
  where
    ops = apA (scChar '&') (OpBand . loc)

scEqualityExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scEqualityExpression = scFoldl
    (\re1 (op,re2) -> return $ BinaryExpr (loc re1) re1 op re2)
    scRelationalExpression
    (ops >*< scRelationalExpression) <?> "equality expression"
  where
    ops = apA (scTok EQ_OP) (OpEq . loc)
      <|> apA (scTok NE_OP) (OpNe . loc)

scRelationalExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scRelationalExpression = scFoldl
    (\se1 (op,se2) -> return $ BinaryExpr (loc se1) se1 op se2)
    scShiftExpression
    (ops >*< scShiftExpression) <?> "relational expression"
  where
    ops = apA (scTok LE_OP) (OpLe . loc)
      <|> apA (scTok GE_OP) (OpGe . loc)
      <|> apA (scChar '<') (OpLt . loc)
      <|> apA (scChar '>') (OpGt . loc)

scShiftExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scShiftExpression = scFoldl
    (\a1 (op,a2) -> return $ BinaryExpr (loc a1) a1 op a2)
    scAdditiveExpression
    (ops >*< scAdditiveExpression) <?> "shift expression"
  where
    ops = apA (scTok SHL_OP) (OpShl . loc)
      <|> apA (scTok SHR_OP) (OpShr . loc)

scAdditiveExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scAdditiveExpression = scFoldl
    (\a1 (op,a2) -> return $ BinaryExpr (loc a1) a1 op a2)
    scMultiplicativeExpression
    (ops >*< scMultiplicativeExpression) <?> "additive expression"
  where
    ops = apA (scChar '+') (OpAdd . loc)
      <|> apA (scChar '-') (OpSub . loc)

scMultiplicativeExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scMultiplicativeExpression = scFoldl
    (\a1 (op,a2) -> return $ BinaryExpr (loc a1) a1 op a2)
    scCastExpression
    (ops >*< scCastExpression) <?> "multiplicative expression"
  where
    ops = apA (scChar '*') (OpMul . loc)
      <|> apA (scChar '/') (OpDiv . loc)
      <|> apA (scChar '%') (OpMod . loc)

scCastExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scCastExpression = (apA2 scCastType scCastExpression (\x1 x2 -> CastExpr (loc x1) x1 x2)
            <||> scPrefixOp) <?> "cast expression"
  where

scCastType :: Monad m => ScParserT u m (CastType Identifier Position)
scCastType = scBraces' $ \x1 ->
    apA scPrimitiveDatatype (CastPrim (loc x1))
    <|> apA scTypeId (CastTy (loc x1))

scPrefixOp :: Monad m => ScParserT u m (Expression Identifier Position)
scPrefixOp = (apA2 (scTok INC_OP) scLvalue (\x1 x2 -> PreOp (loc x1) (OpAdd $ loc x1) x2)
         <|> apA2 (scTok DEC_OP) scLvalue (\x1 x2 -> PreOp (loc x1) (OpSub $ loc x1) x2)
         <|> scPostfixOp) <?> "prefix op"

scPostfixOp :: Monad m => ScParserT u m (Expression Identifier Position)
scPostfixOp = ((scLvalue >>= \x1 ->
                    apA (scTok INC_OP) (\x2 -> PostOp (loc x1) (OpAdd (loc x2)) x1)
                <|> apA (scTok DEC_OP) (\x2 -> PostOp (loc x1) (OpSub (loc x2)) x1)
              )
          <||> scUnaryExpression) <?> "postix op"

scUnaryExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scUnaryExpression = liftM unaryLitExpr (apA2 (scChar '~') scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpInv (loc x1)) x2)
                <|> apA2 (scChar '!') scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpNot (loc x1)) x2)
                <|> apA2 (scChar '-') scCastExpression (\x1 x2 -> UnaryExpr (loc x1) (OpSub (loc x1)) x2)
                <|> scPostfixExpression) <?> "unary expression"

scPostfixExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scPostfixExpression = scFoldl f scPostfixExpression' (scSubscript >+< (scChar '.' *> scAttributeId))
    where
    f pe (Left s) = return $ PostIndexExpr (loc pe) pe s
    f pe (Right v) = return $ SelectionExpr (loc pe) pe v

scPostfixExpression' :: Monad m => ScParserT u m (Expression Identifier Position)
scPostfixExpression' = (apA2 (scTok DOMAINID) (scBraces scSecTypeSpecifier) (\x1 x2 -> DomainIdExpr (loc x1) x2)
                  <|> apA2 (scTok STRINGFROMBYTES) (scBraces scExpression) (\x1 x2 -> StringFromBytesExpr (loc x1) x2)
                  <|> apA2 (scTok BYTESFROMSTRING) (scBraces scExpression) (\x1 x2 -> BytesFromStringExpr (loc x1) x2)
                  <|> apA2 scProcedureId (scBraces (optionMaybe scExpressionList)) (\x1 x2 -> ProcCallExpr (loc x1) x1 (maybe [] Foldable.toList x2))
                  <||> scPrimaryExpression) <?> "postfix expression"

scPrimaryExpression :: Monad m => ScParserT u m (Expression Identifier Position)
scPrimaryExpression = (scBraces scExpression
                  <|> scCBrackets' (\x1 -> apA scExpressionList (ArrayConstructorPExpr (loc x1)))
                  <|> apA scVarId (\x1 -> RVariablePExpr (loc x1) x1)
                  <|> apA scLiteral (\x1 -> LitPExpr (loc x1) x1)) <?> "primary expression"

scStringLiteral :: Monad m => ScParserT u m (Loc Position String)
scStringLiteral = apA (many1 scStringPart) mergeStrs <?> "string literal"
    where
    mergeStrs xs = Loc (loc $ headNote "head parsec" xs) (concatMap unLoc xs)

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

parseFileIO :: Options -> String -> IO (Module Identifier Position)
parseFileIO opts fn = ioSecrecM opts $ parseFile fn

parseFile :: String -> SecrecM (Module Identifier Position)
parseFile fn = do
    str <- liftIO (readFile fn)
    x <- parseSecreC fn str
    return x

parseSecreCIO :: Options -> String -> String -> IO (Module Identifier Position)
parseSecreCIO opts fn str = ioSecrecM opts $ parseSecreC fn str

parseSecreCIOWith :: PP a => Options -> String -> String -> ScParserT () Identity a -> IO a
parseSecreCIOWith opts fn str parse = ioSecrecM opts $ parseSecreCWith fn str parse

parseSecreC :: String -> String -> SecrecM (Module Identifier Position)
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
scPosition :: Monad m => ScParserT u m Position
scPosition = liftM sourcePosToPosition getPosition
