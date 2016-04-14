module Language.SecreC.Parser.Derp (
    parseFile,parseFileIO,
    parseSecreC,parseSecreCWith,parseSecreCIO,parseSecreCIOWith
 ) where

import Language.SecreC.Position
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Monad
import Language.SecreC.Pretty hiding (sepBy)
import Language.SecreC.Parser.Tokens
import Language.SecreC.Parser.Lexer

import Control.Applicative hiding ((<|>),optional,many)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (ask)
import Control.Monad.Identity

import System.IO

import qualified Data.Foldable as Foldable

import Text.Derp hiding (Token)
import qualified Text.Derp as Derp
import Text.Derp.Combinator as Derp

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Maybe

import Safe

type ScParser a = Parser TokenInfo a

scTok :: Token -> ScParser TokenInfo
scTok t = scTokPred ((==t) . tSymb)

scTokPred :: (TokenInfo -> Bool) -> ScParser TokenInfo
scTokPred p = terPrim p

scChar :: Char -> ScParser TokenInfo
scChar c = scTokPred (p . tSymb)
    where
    p (CHAR c') = c == c'
    p _ = False

scParens :: Ord a => ScParser a -> ScParser a
scParens p = (scChar '(' ~> p) <~ scChar ')'

scBraces :: Ord a => ScParser a -> ScParser a
scBraces p = (scChar '{' ~> p) <~ scChar '}'

scBrackets :: Ord a => ScParser a -> ScParser a
scBrackets p = (scChar '[' ~> p) <~ scChar ']'

scABrackets :: Ord a => ScParser a -> ScParser a
scABrackets p = (scChar '<' ~> p) <~ scChar '>'

scCBrackets :: Ord a => ScParser a -> ScParser a
scCBrackets p = (scChar '{' ~> p) <~ scChar '}'

scFoldl :: (Ord a,Ord b) => (a -> b -> a) -> ScParser a -> ScParser b -> ScParser a
scFoldl f ma mb = ma <~> many mb ==> (\(x,ys) -> Foldable.foldl' f x ys)

-- * Grammar

-- ** Literals

scIntLiteral :: ScParser (Loc Position Integer)
scIntLiteral = (scTokPred p) ==> (\x1 -> Loc (loc x1) (tokenInteger x1))
    where
    p (TokenInfo (BIN_LITERAL _) _ _) = True
    p (TokenInfo (DEC_LITERAL _) _ _) = True
    p (TokenInfo (HEX_LITERAL _) _ _) = True
    p (TokenInfo (OCT_LITERAL _) _ _) = True
    p _ = False

scFloatLiteral :: ScParser (Loc Position Double)
scFloatLiteral = (scTokPred p) ==> (\x1 -> Loc (loc x1) (tokenFloat x1))
    where
    p (TokenInfo (FLOAT_LITERAL _) _ _) = True
    p _ = False

scStrFragment :: ScParser TokenInfo
scStrFragment = scTokPred p
    where
    p (TokenInfo (STR_FRAGMENT _) _ _) = True
    p _ = False

scStrIdentifier :: ScParser TokenInfo
scStrIdentifier = scTokPred p
    where
    p (TokenInfo (STR_IDENTIFIER _) _ _) = True
    p _ = False

-- ** Identifiers

scKindId :: ScParser (KindName Identifier Position)
scKindId = scIdentifier ==> (\t -> KindName (tLoc t) (tokenString t))

scVarId :: ScParser (VarName Identifier Position)
scVarId = scIdentifier ==> (\t -> VarName (tLoc t) (tokenString t))

scAttributeId :: ScParser (AttributeName Identifier Position)
scAttributeId = scIdentifier ==> (\t -> AttributeName (tLoc t) (tokenString t))

scProcedureId :: ScParser (ProcedureName Identifier Position)
scProcedureId = scIdentifier ==> (\t -> ProcedureName (tLoc t) (tokenString t))

scDomainId :: ScParser (DomainName Identifier Position)
scDomainId = scIdentifier ==> (\t -> DomainName (tLoc t) (tokenString t))

scTypeId :: ScParser (TypeName Identifier Position)
scTypeId = scIdentifier ==> (\t -> TypeName (tLoc t) (tokenString t))

scTemplateArgId :: ScParser (TemplateArgName Identifier Position)
scTemplateArgId = scIdentifier ==> (\t -> TemplateArgName (tLoc t) (tokenString t))

scModuleId :: ScParser (ModuleName Identifier Position)
scModuleId = scIdentifier ==> (\t -> ModuleName (tLoc t) (tokenString t))

scIdentifier :: ScParser TokenInfo
scIdentifier = scTokPred (p . tSymb)
    where
    p (IDENTIFIER s) = True
    p _ = False

scEOF :: ScParser ()
scEOF = scTokPred (p . tSymb) ==> (const ())
    where
    p TokenEOF = True
    p _ = False

-- ** Program and variable declarations

scModuleFile :: ScParser (Module Identifier Position)
scModuleFile = scModule <~ scEOF

scModule :: ScParser (Module Identifier Position)
scModule = (scTok MODULE) <~> scModuleId <~ (scChar ';') <~> scProgram ==> (\(x1,(x2,x3)) -> Module (loc x1) (Just x2) x3)
       <|> scProgram ==> (\x1 -> Module (loc x1) Nothing x1)
    
scProgram :: ScParser (Program Identifier Position)
scProgram = scImportDeclarations <~> scGlobalDeclarations ==> (\(x1,x2) -> Program (if null x1 then if null x2 then UnhelpfulPos "start" else loc (head x2) else loc (head x1)) x1 x2)

scImportDeclarations :: ScParser [ImportDeclaration Identifier Position]
scImportDeclarations = many scImportDeclaration

scGlobalDeclarations :: ScParser [GlobalDeclaration Identifier Position]
scGlobalDeclarations = many scGlobalDeclaration 

scImportDeclaration :: ScParser (ImportDeclaration Identifier Position)
scImportDeclaration = (scTok IMPORT) <~> scModuleId <~ (scChar ';') ==> (\(x1,x2) -> Import (loc x1) x2)

scGlobalDeclaration :: ScParser (GlobalDeclaration Identifier Position)
scGlobalDeclaration = scConstDeclaration <~> scChar ';' ==> (\(x1,x2) -> GlobalConst (loc x1) x1)
                  <|> scVariableDeclaration <~> scChar ';' ==> (\(x1,x2) -> GlobalVariable (loc x1) x1)
                  <|> scDomainDeclaration <~> scChar ';' ==> (\(x1,x2) -> GlobalDomain (loc x1) x1)
                  <|> scKindDeclaration <~> scChar ';' ==> (\(x1,x2) -> GlobalKind (loc x1) x1)
                  <|> scProcedureDeclaration ==> (\x1 -> GlobalProcedure (loc x1) x1)
                  <|> scStructureDeclaration ==> (\x1 -> GlobalStructure (loc x1) x1)
                  <|> scTemplateDeclaration ==> (\x1 -> GlobalTemplate (loc x1) x1)
    
scKindDeclaration :: ScParser (KindDeclaration Identifier Position)
scKindDeclaration = scTok KIND <~> scKindId ==> (\(x1,x2) -> Kind (loc x1) x2)

scDomainDeclaration :: ScParser (DomainDeclaration Identifier Position)
scDomainDeclaration = scTok DOMAIN <~> scDomainId <~> scKindId ==> (\(x1,(x2,x3)) -> Domain (loc x1) x2 x3)

scVariableInitialization :: ScParser (VariableInitialization Identifier Position)
scVariableInitialization = scVarId <~> optionMaybe scSizes <~> optionMaybe (scChar '=' ~> scExpression) ==> (\(x1,(x2,x3)) -> VariableInitialization (loc x1) x1 x2 x3)

scConstInitialization :: ScParser (ConstInitialization Identifier Position)
scConstInitialization = scVarId <~> optionMaybe scSizes <~> optionMaybe (scChar '=' ~> scExpression) ==> (\(x1,(x2,x3)) -> ConstInitialization (loc x1) x1 x2 x3)

scVariableInitializations :: ScParser (NeList (VariableInitialization Identifier Position))
scVariableInitializations = sepBy1 scVariableInitialization (scChar ',') ==> fromListNe

scConstInitializations :: ScParser (NeList (ConstInitialization Identifier Position))
scConstInitializations = sepBy1 scConstInitialization (scChar ',') ==> fromListNe

scVariableDeclaration :: ScParser (VariableDeclaration Identifier Position)
scVariableDeclaration = scTypeSpecifier <~> scVariableInitializations ==> (\(x1,x2) -> VariableDeclaration (loc x1) x1 x2)

scConstDeclaration :: ScParser (ConstDeclaration Identifier Position)
scConstDeclaration = scTok CONST <~> scTypeSpecifier <~> scConstInitializations ==> (\(x0,(x1,x2)) -> ConstDeclaration (loc x0) x1 x2)

scProcedureParameter :: ScParser (ProcedureParameter Identifier Position)
scProcedureParameter =
    (scTok CONST ~> scTypeSpecifier <~> scVariadic <~> scVarId <~> scInvariant ==> (\(x1,(x2,(x3,(x4)))) -> ConstProcedureParameter (loc x1) x1 x2 x3 x4))
    <|> (scTypeSpecifier <~> scVariadic <~> scVarId==> (\(x1,(x2,(x3))) -> ProcedureParameter (loc x1) x1 x2 x3))

scVariadic :: ScParser IsVariadic
scVariadic = optionMaybe (scTok VARIADIC) ==> isJust

scVariadicExpression :: ScParser (Expression Identifier Position,IsVariadic)
scVariadicExpression = scExpression <~> scVariadic

scInvariant :: ScParser (Maybe (Expression Identifier Position))
scInvariant = optionMaybe (scBraces scExpression) 

scSizes :: ScParser (Sizes Identifier Position)
scSizes = scParens scVariadicExpressionList1 ==> Sizes 

scExpressionList :: ScParser [Expression Identifier Position]
scExpressionList = sepBy scExpression (scChar ',')

scVariadicExpressionList :: ScParser [(Expression Identifier Position,IsVariadic)]
scVariadicExpressionList = sepBy scVariadicExpression (scChar ',')

scVariadicExpressionList1 :: ScParser (NeList (Expression Identifier Position,IsVariadic))
scVariadicExpressionList1 = sepBy1 scVariadicExpression (scChar ',') ==> fromListNe

-- ** Types                                                                     

scTypeSpecifier :: ScParser (TypeSpecifier Identifier Position)
scTypeSpecifier = optionMaybe scSecTypeSpecifier <~> scDatatypeSpecifier <~> optionMaybe scDimtypeSpecifier ==> (\(x1,(x2,x3)) -> TypeSpecifier (maybe (loc x2) loc x1) x1 x2 x3)
    
scSecTypeSpecifier :: ScParser (SecTypeSpecifier Identifier Position)
scSecTypeSpecifier = scTok PUBLIC ==> (\x1 -> PublicSpecifier (loc x1))
                 <|> scDomainId ==> (\x1 -> PrivateSpecifier (loc x1) x1)

scDatatypeSpecifier :: ScParser (DatatypeSpecifier Identifier Position)
scDatatypeSpecifier = scPrimitiveDatatype ==> (\x1 -> PrimitiveSpecifier (loc x1) x1)
                  <|> scTemplateStructDatatypeSpecifier
                  <|> scTypeId ==> (\x1 -> VariableSpecifier (loc x1) x1)

scPrimitiveDatatype :: ScParser (PrimitiveDatatype Position)
scPrimitiveDatatype = scTok BOOL ==> (DatatypeBool . loc)
                  <|> scTok INT ==> (DatatypeInt64 . loc)
                  <|> scTok UINT ==> (DatatypeUint64 . loc)
                  <|> scTok INT8 ==> (DatatypeInt8 . loc)
                  <|> scTok UINT8 ==> (DatatypeUint8 . loc)
                  <|> scTok INT16 ==> (DatatypeInt16 . loc)
                  <|> scTok UINT16 ==> (DatatypeUint16 . loc)
                  <|> scTok INT32 ==> (DatatypeInt32 . loc)
                  <|> scTok UINT32 ==> (DatatypeUint32 . loc)
                  <|> scTok INT64 ==> (DatatypeInt64 . loc)
                  <|> scTok UINT64 ==> (DatatypeUint64 . loc)
                  <|> scTok STRING ==> (DatatypeString . loc)
                  <|> scTok XOR_UINT8 ==> (DatatypeXorUint8 . loc)
                  <|> scTok XOR_UINT16 ==> (DatatypeXorUint16 . loc)
                  <|> scTok XOR_UINT32 ==> (DatatypeXorUint32 . loc)
                  <|> scTok XOR_UINT64 ==> (DatatypeXorUint64 . loc)
                  <|> scTok XOR_UINT ==> (DatatypeXorUint64 . loc)
                  <|> scTok FLOAT ==> (DatatypeFloat32 . loc)
                  <|> scTok FLOAT32 ==> (DatatypeFloat32 . loc)
                  <|> scTok FLOAT64 ==> (DatatypeFloat64 . loc)

scTemplateStructDatatypeSpecifier :: ScParser (DatatypeSpecifier Identifier Position)
scTemplateStructDatatypeSpecifier = scTypeId <~> scABrackets scTemplateTypeArguments ==> (\(x1,x2) -> TemplateSpecifier (loc x1) x1 x2)

scTemplateTypeArguments :: ScParser [(TemplateTypeArgument Identifier Position,IsVariadic)]
scTemplateTypeArguments = sepBy (scTemplateTypeArgument <~> scVariadic) (scChar ',')

scTemplateTypeArgument :: ScParser (TemplateTypeArgument Identifier Position)
scTemplateTypeArgument = scTok PUBLIC ==> (PublicTemplateTypeArgument . loc)
                     <|> scTypeId <~> scABrackets scTemplateTypeArguments ==> (\(x1,x2) -> TemplateTemplateTypeArgument (loc x1) x1 x2)
                     <|> scTemplateArgId ==> (\x1 -> GenericTemplateTypeArgument (loc x1) x1) -- type, domain or variable identifier
                     <|> scExpression ==> (\x1 -> ExprTemplateTypeArgument (loc x1) x1)
                     <|> scPrimitiveDatatype ==> (\x1 -> PrimitiveTemplateTypeArgument (loc x1) x1)

scDimtypeSpecifier :: ScParser (DimtypeSpecifier Identifier Position)
scDimtypeSpecifier = (scChar '[' <~ scChar '[') <~> (scExpression) <~ (scChar ']' <~ scChar ']') ==> f
    where
    f (x1,x2) = DimSpecifier (loc x1) x2

-- ** Templates                                                               

scTemplateDeclaration :: ScParser (TemplateDeclaration Identifier Position)
scTemplateDeclaration = scTok TEMPLATE <~> scABrackets scTemplateQuantifiers <~> (scStructure <+> scProcedureDeclaration) ==> f
    where
    f (x1,(x2,Left (Nothing,x4))) = TemplateStructureDeclaration (loc x1) x2 x4
    f (x1,(x2,Left (Just x3,x4))) = TemplateStructureSpecialization (loc x1) x2 x3 x4
    f (x1,(x2,(Right x3))) = TemplateProcedureDeclaration (loc x1) x2 x3

scTemplateQuantifiers :: ScParser [TemplateQuantifier Identifier Position]
scTemplateQuantifiers = Derp.sepBy scTemplateQuantifier (scChar ',')

scTemplateQuantifier :: ScParser (TemplateQuantifier Identifier Position)
scTemplateQuantifier = scTok DOMAIN <~> scVariadic <~> scDomainId <~> optionMaybe (scChar ':' ~> scKindId) ==> (\(x1,(x2,(x3,x4))) -> DomainQuantifier (loc x1) x2 x3 x4)
                   <|> scTok DIMENSIONALITY <~> scVariadic <~> scVarId <~> scInvariant ==> (\(x1,(x2,(x3,x4))) -> DimensionQuantifier (loc x1) x2 x3 x4)
                   <|> scTok TYPE <~> scVariadic <~> scTypeId ==> (\(x1,(x2,x3)) -> DataQuantifier (loc x1) x2 x3)

-- ** Structures                                                                 

scStructure :: ScParser (Maybe [(TemplateTypeArgument Identifier Position,IsVariadic)],StructureDeclaration Identifier Position)
scStructure = scTok STRUCT <~> scTypeId <~> optionMaybe (scABrackets scTemplateTypeArguments) <~> scCBrackets scAttributeList ==> (\(x1,(x2,(x3,x4))) -> (x3,StructureDeclaration (loc x1) x2 x4))

scStructureDeclaration :: ScParser (StructureDeclaration Identifier Position)
scStructureDeclaration = scTok STRUCT <~> scTypeId <~> scCBrackets scAttributeList ==> (\(x1,(x2,x3)) -> StructureDeclaration (loc x1) x2 x3)

scAttributeList :: ScParser [Attribute Identifier Position]
scAttributeList = many scAttribute 

scAttribute :: ScParser (Attribute Identifier Position)
scAttribute = scTypeSpecifier <~> (scAttributeId <~ (scChar ';')) ==> (\(x1,x2) -> Attribute (loc x1) x1 x2)

-- ** Procedures                                

scReturnTypeSpecifier :: ScParser (ReturnTypeSpecifier Identifier Position)
scReturnTypeSpecifier = scTok VOID ==> (\x1 -> ReturnType (loc x1) Nothing)
                    <|> scTypeSpecifier ==> (\(x1) -> ReturnType (loc x1) (Just x1))

scProcedureDeclaration :: ScParser (ProcedureDeclaration Identifier Position)
scProcedureDeclaration = scReturnTypeSpecifier <~> ((scTok OPERATOR ~> scOp) <+> scProcedureId) <~> scParens scProcedureParameterList <~> scCompoundStatement ==> f
    where
    f (x1,(Left x2,(x3,x4))) = OperatorDeclaration (loc x1) x1 x2 x3 (unLoc x4)
    f (x1,(Right x2,(x3,x4))) = ProcedureDeclaration (loc x1) x1 x2 x3 (unLoc x4)

scProcedureParameterList :: ScParser [ProcedureParameter Identifier Position]
scProcedureParameterList = sepBy scProcedureParameter (scChar ',')

scOp :: ScParser (Op Identifier Position)
scOp = scChar '+' ==> (OpAdd . loc)
   <|> scChar '&' ==> (OpBand . loc)
   <|> scChar '|' ==> (OpBor . loc)
   <|> scChar '/' ==> (OpDiv . loc)
   <|> scChar '>' ==> (OpGt . loc)
   <|> scChar '<' ==> (OpLt . loc)
   <|> scChar '%' ==> (OpMod . loc)
   <|> scChar '*' ==> (OpMul . loc)
   <|> scChar '-' ==> (OpSub . loc)
   <|> scChar '^' ==> (OpXor . loc)
   <|> scChar '!' ==> (OpNot . loc )
   <|> scTok EQ_OP ==> (OpEq . loc)
   <|> scTok GE_OP ==> (OpGe . loc)
   <|> scTok LAND_OP ==> (OpLand . loc)
   <|> scTok LE_OP ==> (OpLe . loc)
   <|> scTok LOR_OP ==> (OpLor . loc)
   <|> scTok NE_OP ==> (OpNe . loc)
   <|> scTok SHL_OP ==> (OpShl . loc)
   <|> scTok SHR_OP ==> (OpShr . loc)
   <|> scChar '('  <~> scCastType <~ scChar ')' ==> (\(x1,x2) -> OpCast (loc x1) x2)

-- * Statements                                                           

scCompoundStatement :: ScParser (Loc Position [Statement Identifier Position])
scCompoundStatement = scChar '{' <~> many scStatement <~ scChar '}' ==> (\(x1,x2) -> Loc (loc x1) x2)

scStatement :: ScParser (Statement Identifier Position)
scStatement = scCompoundStatement ==> (\x1 -> CompoundStatement (loc x1) (unLoc x1))
          <|> scIfStatement
          <|> scForStatement
          <|> scWhileStatement
          <|> scDowhileStatement
          <|> scAssertStatement
          <|> scPrintStatement
          <|> scSyscallStatement
          <|> scConstDeclaration <~> scChar ';' ==> (\(x1,x2) -> ConstStatement (loc x1) x1)
          <|> scVariableDeclaration <~> scChar ';' ==> (\(x1,x2) -> VarStatement (loc x1) x1)
          <|> scTok RETURN <~> optionMaybe scExpression <~> scChar ';' ==> (\(x1,(x2,x3)) -> ReturnStatement (loc x1) x2)
          <|> scTok CONTINUE <~> scChar ';' ==> (\(x1,x2) -> ContinueStatement (loc x1))
          <|> scTok BREAK <~> scChar ';' ==> (\(x1,x2) -> BreakStatement (loc x1))
          <|> scChar ';' ==> (\x1 -> CompoundStatement (loc x1) [])
          <|> scExpression  <~ scChar ';' ==> (\x1 -> ExpressionStatement (loc x1) x1)

scIfStatement :: ScParser (Statement Identifier Position)
scIfStatement = scTok IF <~> scParens scExpression <~> scStatement  <~> optionMaybe (scTok ELSE ~> scStatement) ==> (\(x1,(x2,(x3,x4))) -> IfStatement (loc x1) x2 x3 x4)

scForInitializer :: ScParser (ForInitializer Identifier Position)
scForInitializer = optionMaybe scExpression ==> InitializerExpression
               <|> scVariableDeclaration ==> InitializerVariable

scForStatement :: ScParser (Statement Identifier Position)
scForStatement = scTok FOR <~> (scChar '(' ~> scForInitializer) <~ scChar ';' <~> optionMaybe scExpression <~ scChar ';' <~> optionMaybe scExpression <~ scChar ')' <~> scStatement ==> (\(x1,(x2,(x3,(x4,x5)))) -> ForStatement (loc x1) x2 x3 x4 x5)

scWhileStatement :: ScParser (Statement Identifier Position)
scWhileStatement = scTok WHILE <~> scParens scExpression <~> scStatement ==> (\(x1,(x2,x3)) -> WhileStatement (loc x1) x2 x3)

scPrintStatement :: ScParser (Statement Identifier Position)
scPrintStatement = scTok PRINT <~> scParens scVariadicExpressionList <~ scChar ';' ==> (\(x1,x2) -> PrintStatement (loc x1) x2)

scDowhileStatement :: ScParser (Statement Identifier Position)
scDowhileStatement = scTok DO <~> scStatement <~ scTok WHILE <~> scParens scExpression <~ scChar ';' ==> (\(x1,(x2,x3)) -> DowhileStatement (loc x1) x2 x3)

scAssertStatement :: ScParser (Statement Identifier Position)
scAssertStatement = scTok ASSERT <~> scParens scExpression <~ scChar ';' ==> (\(x1,x2) -> AssertStatement (loc x1) x2)

scSyscallStatement :: ScParser (Statement Identifier Position)
scSyscallStatement = scTok SYSCALL <~> (scParens sysparams <~ scChar ';') ==> (\(x1,(x2,x3)) -> SyscallStatement (loc x1) x2 x3)
    where
        sysparams = (scStringLiteral ==> unLoc)
                <~> many (scChar ',' ~> scSyscallParameter)

scSyscallParameter :: ScParser (SyscallParameter Identifier Position)
scSyscallParameter = scTok SYSCALL_RETURN <~> scVarId ==> (\(x1,x2) -> SyscallReturn (loc x1) x2)
                 <|> scTok REF <~> scVarId ==> (\(x1,x2) -> SyscallPushRef (loc x1) x2)
                 <|> scTok CREF <~> scExpression ==> (\(x1,x2) -> SyscallPushCRef (loc x1) x2)
                 <|> scExpression ==> (\x1 -> SyscallPush (loc x1) x1)

-- ** Indices: not strictly expressions as they only appear in specific context  

scSubscript :: ScParser (Subscript Identifier Position)
scSubscript = scBrackets scIndices 

scIndices :: ScParser (NeList (Index Identifier Position))
scIndices = sepBy1 scIndex (scChar ',') ==> fromListNe 

---- Precedence of slicing operator? Right now it binds weakest as it can appear
---- in very specific context. However, if we ever wish for "foo : bar" evaluate
---- to value in some other context we need to figure out sane precedence.
scIndex :: ScParser (Index Identifier Position)
scIndex = optionMaybe scExpression <~> scChar ':' <~> optionMaybe scExpression ==> (\(x1,(x2,x3)) -> IndexSlice (maybe (loc x2) loc x1) x1 x3)
     <|> scExpression ==> (\x1 -> IndexInt (loc x1) x1)

-- ** Expressions                                                               

scLvalue :: ScParser (Expression Identifier Position)
scLvalue = scPostfixExpression

scExpression :: ScParser (Expression Identifier Position)
scExpression = scAssignmentExpression

scAssignmentExpression :: ScParser (Expression Identifier Position)
scAssignmentExpression = scLvalue <~> op <~> scAssignmentExpression ==> (\(x1,(x2,x3)) -> BinaryAssign (loc x1) x1 x2 x3)
                      <|> scQualifiedExpression
    where
    op = scChar '=' ==> (BinaryAssignEqual . loc)
     <|> scTok MUL_ASSIGN ==> (BinaryAssignMul . loc)
     <|> scTok DIV_ASSIGN ==> (BinaryAssignDiv . loc)
     <|> scTok MOD_ASSIGN ==> (BinaryAssignMod . loc)
     <|> scTok ADD_ASSIGN ==> (BinaryAssignAdd . loc)                                                                                
     <|> scTok SUB_ASSIGN ==> (BinaryAssignSub . loc)
     <|> scTok AND_ASSIGN ==> (BinaryAssignAnd . loc)
     <|> scTok OR_ASSIGN ==> (BinaryAssignOr . loc)
     <|> scTok XOR_ASSIGN ==> (BinaryAssignXor . loc)

scQualifiedExpression :: ScParser (Expression Identifier Position)
scQualifiedExpression = scFoldl
    (\qe t -> QualExpr (loc qe) qe t)
    scConditionalExpression
    (scTok TYPE_QUAL ~> scTypeSpecifier)

scConditionalExpression :: ScParser (Expression Identifier Position)
scConditionalExpression = scLogicalOrExpression
                      <~> optionMaybe (scChar '?' ~> scExpression <~> scChar ':' ~> scExpression) 
                      ==> f
  where
  f (x1,Nothing) = x1
  f (x1,Just (x2,x3)) = CondExpr (loc x1) x1 x2 x3

scLogicalOrExpression :: ScParser (Expression Identifier Position)
scLogicalOrExpression = scFoldl
    (\re1 (op,re2) -> BinaryExpr (loc re1) re1 op re2)
    scLogicalAndExpression
    (ops <~> scLogicalAndExpression)
  where
    ops = scTok LOR_OP ==> (OpLor . loc)

scLogicalAndExpression :: ScParser (Expression Identifier Position)
scLogicalAndExpression = scFoldl
    (\re1 (op,re2) -> BinaryExpr (loc re1) re1 op re2)
    scBitwiseOrExpression
    (ops <~> scBitwiseOrExpression)
  where
    ops = scTok LAND_OP ==> (OpLand . loc)

scBitwiseOrExpression :: ScParser (Expression Identifier Position)
scBitwiseOrExpression = scFoldl
    (\re1 (op,re2) -> BinaryExpr (loc re1) re1 op re2)
    scBitwiseXorExpression
    (ops <~> scBitwiseXorExpression)
  where
    ops = scChar '|' ==> (OpBor . loc)

scBitwiseXorExpression :: ScParser (Expression Identifier Position)
scBitwiseXorExpression = scFoldl
    (\re1 (op,re2) -> BinaryExpr (loc re1) re1 op re2)
    scBitwiseAndExpression
    (ops <~> scBitwiseAndExpression)
  where
    ops = scChar '^' ==> (OpXor . loc)

scBitwiseAndExpression :: ScParser (Expression Identifier Position)
scBitwiseAndExpression = scFoldl
    (\re1 (op,re2) -> BinaryExpr (loc re1) re1 op re2)
    scEqualityExpression
    (ops <~> scEqualityExpression)
  where
    ops = scChar '&' ==> (OpBand . loc)

scEqualityExpression :: ScParser (Expression Identifier Position)
scEqualityExpression = scFoldl
    (\re1 (op,re2) -> BinaryExpr (loc re1) re1 op re2)
    scRelationalExpression
    (ops <~> scRelationalExpression)
  where
    ops = scTok EQ_OP ==> (OpEq . loc)
      <|> scTok NE_OP ==> (OpNe . loc)

scRelationalExpression :: ScParser (Expression Identifier Position)
scRelationalExpression = scFoldl
    (\se1 (op,se2) -> BinaryExpr (loc se1) se1 op se2)
    scShiftExpression
    (ops <~> scShiftExpression) 
  where
    ops = scTok LE_OP ==> (OpLe . loc)
      <|> scTok GE_OP ==> (OpGe . loc)
      <|> scChar '<' ==> (OpLt . loc)
      <|> scChar '>' ==> (OpGt . loc)

scShiftExpression :: ScParser (Expression Identifier Position)
scShiftExpression = scFoldl
    (\a1 (op,a2) -> BinaryExpr (loc a1) a1 op a2)
    scAdditiveExpression
    (ops <~> scAdditiveExpression) 
  where
    ops = scTok SHL_OP ==> (OpShl . loc)
      <|> scTok SHR_OP ==> (OpShr . loc)

scAdditiveExpression :: ScParser (Expression Identifier Position)
scAdditiveExpression = scFoldl
    (\a1 (op,a2) -> BinaryExpr (loc a1) a1 op a2)
    scMultiplicativeExpression
    (ops <~> scMultiplicativeExpression) 
  where
    ops = scChar '+' ==> (OpAdd . loc)
      <|> scChar '-' ==> (OpSub . loc)

scMultiplicativeExpression :: ScParser (Expression Identifier Position)
scMultiplicativeExpression = scFoldl
    (\a1 (op,a2) -> BinaryExpr (loc a1) a1 op a2)
    scCastExpression
    (ops <~> scCastExpression)
  where
    ops = scChar '*' ==> (OpMul . loc)
      <|> scChar '/' ==> (OpDiv . loc)
      <|> scChar '%' ==> (OpMod . loc)

scCastExpression :: ScParser (Expression Identifier Position)
scCastExpression = scCastType <~> scCastExpression ==> (\(x1,x2) -> UnaryExpr (loc x1) (OpCast (loc x1) x1) x2)
               <|> scPrefixOp
    
scCastType :: ScParser (CastType Identifier Position)
scCastType = scChar '(' <~> scPrimitiveDatatype <~ scChar ')' ==> (\(x1,x2) -> CastPrim x2)
         <|> scChar '(' <~> scTypeId <~ scChar ')' ==> (\(x1,x2) -> CastTy x2)
    
scPrefixOp :: ScParser (Expression Identifier Position)
scPrefixOp = scTok INC_OP <~> scLvalue ==> (\(x1,x2) -> PreOp (loc x1) (OpAdd $ loc x1) x2)
         <|> scTok DEC_OP <~> scLvalue ==> (\(x1,x2) -> PreOp (loc x1) (OpSub $ loc x1) x2)
         <|> scPostfixOp

scPostfixOp :: ScParser (Expression Identifier Position)
scPostfixOp = scLvalue <~> scTok INC_OP ==> (\(x1,x2) -> PostOp (loc x1) (OpAdd $ loc x2) x1)
          <|> scLvalue <~> scTok DEC_OP ==> (\(x1,x2) -> PostOp (loc x1) (OpAdd $ loc x1) x1)
          <|> scUnaryExpression

scUnaryExpression :: ScParser (Expression Identifier Position)
scUnaryExpression = (scChar '~' <~> scCastExpression ==> (\(x1,x2) -> UnaryExpr (loc x1) (OpInv $ loc x1) x2)
                <|> scChar '!' <~> scCastExpression ==> (\(x1,x2) -> UnaryExpr (loc x1) (OpNot $ loc x1) x2)
                <|> scChar '-' <~> scCastExpression ==> (\(x1,x2) -> UnaryExpr (loc x1) (OpSub $ loc x1) x2)
                <|> scPostfixExpression) ==> unaryLitExpr

scPostfixExpression :: ScParser (Expression Identifier Position)
scPostfixExpression = scFoldl f scPostfixExpression' (scSubscript <+> (scChar '.' ~> scAttributeId))
    where
    f pe (Left s) = PostIndexExpr (loc pe) pe s
    f pe (Right v) =  SelectionExpr (loc pe) pe v

scPostfixExpression' :: ScParser (Expression Identifier Position)
scPostfixExpression' = scTok DOMAINID <~> scParens scSecTypeSpecifier ==> (\(x1,x2) -> DomainIdExpr (loc x1) x2)
                  <|> scTok BYTESFROMSTRING <~> scParens scExpression ==> (\(x1,x2) -> BytesFromStringExpr (loc x1) x2)
                  <|> scTok STRINGFROMBYTES <~> scParens scExpression ==> (\(x1,x2) -> StringFromBytesExpr (loc x1) x2)
                  <|> scTok VSIZE <~> scParens scExpression ==> (\(x1,x2) -> VArraySizeExpr (loc x1) x2)
                  <|> scTok VARRAY <~> scParens (scExpression <~> scChar ',' ~> scExpression) ==> (\(x1,(x2,x3)) -> VArrayExpr (loc x1) x2 x3)
                  <|> scProcedureId <~> (optionMaybe $ scABrackets scTemplateTypeArguments) <~> scParens (optionMaybe scVariadicExpressionList) ==> (\(x1,(x2,x3)) -> ProcCallExpr (loc x1) x1 x2 (maybe [] Foldable.toList x3))
                  <|> scPrimaryExpression

scPrimaryExpression :: ScParser (Expression Identifier Position)
scPrimaryExpression = scChar '(' ~> (scExpression <~ scChar ')')
                  <|> scChar '{' <~> scExpressionList <~ scChar '}' ==> (\(x1,x2) -> ArrayConstructorPExpr (loc x1) x2)
                  <|> scVarId ==> (\x1 -> RVariablePExpr (loc x1) x1)
                  <|> scLiteral ==> (\x1 -> LitPExpr (loc x1) x1)

scStringLiteral :: ScParser (Loc Position String)
scStringLiteral = many1 scStringPart ==> mergeStrs 
    where
    mergeStrs xs = Loc (loc $ headNote "head derp" xs) (concatMap unLoc xs)

scStringPart :: ScParser (Loc Position String)
scStringPart = scStrIdentifier ==> (\x1 -> Loc (loc x1) (tokenString x1))
           <|> scStrFragment ==> (\x1 -> Loc (loc x1) (tokenString x1))


scBoolLiteral :: ScParser (Loc Position Bool)
scBoolLiteral = scTok TRUE_B ==> (\x1 -> Loc (loc x1) (tokenBool x1))
            <|> scTok FALSE_B ==> (\x1 -> Loc (loc x1) (tokenBool x1))

scLiteral :: ScParser (Literal Position)
scLiteral = scIntLiteral ==> (\x1 -> IntLit (loc x1) (unLoc x1))
        <|> scStringLiteral ==> (\x1 -> StringLit (loc x1) (unLoc x1))
        <|> scBoolLiteral ==> (\x1 -> BoolLit (loc x1) (unLoc x1))
        <|> scFloatLiteral ==> (\x1 -> FloatLit (loc x1) (unLoc x1))

-- * Parsing functions

parseFileIO :: Options -> String -> IO (Module Identifier Position)
parseFileIO opts fn = runSecrecM opts $ parseFile fn

parseFile :: MonadIO m => String -> SecrecM m (Module Identifier Position)
parseFile fn = do
    str <- liftIO (readFile fn)
    x <- parseSecreC fn str
    return x

parseSecreCIO :: Options -> String -> String -> IO (Module Identifier Position)
parseSecreCIO opts fn str = runSecrecM opts $ parseSecreC fn str

parseSecreCIOWith :: (Ord a,PP a) => Options -> String -> String -> ScParser a -> IO a
parseSecreCIOWith opts fn str parse = runSecrecM opts $ parseSecreCWith fn str parse

parseSecreC :: MonadIO m => String -> String -> SecrecM m (Module Identifier Position)
parseSecreC fn str = parseSecreCWith fn str scModuleFile

parseSecreCWith :: (MonadIO m,Ord a,PP a) => String -> String -> ScParser a -> SecrecM m a
parseSecreCWith fn str parser = do
    case runLexer fn str of
        Left err -> throwError $ parserError $ LexicalException err
        Right toks -> do
            opts <- ask
            when (debugLexer opts) $ liftIO $ hPutStrLn stderr "Lexer Tokens:" >> hPutStrLn stderr (show $ map tSymb toks)
            let res = runParse parser (derpToks toks)
            case Set.toList res of
                [] -> throwError $ parserError $ DerpException "no parse"
                [x] -> do
                    when (debugParser opts) $ liftIO $ hPutStrLn stderr ("Parsed " ++ fn ++ ":") >> hPutStrLn stderr (ppr x)
                    return x
                xs -> throwError $ parserError $ DerpException $ "Ambiguous file " ++ concatMap (\x -> ppr x ++ "\n\n") xs
        
derpToks :: [TokenInfo] -> [Derp.Token TokenInfo]
derpToks xs = map (\t -> Derp.Token t (ppr t)) xs
 
