{

module Language.SecreC.Parser.Parser (
    parseFile,
    parseSecreC
 ) where

import Data.Foldable

import Control.Monad.Error
import Control.Monad.State

import Language.SecreC.Position
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Parser.Tokens
import Language.SecreC.Parser.Lexer
import Language.SecreC.Location
import Language.SecreC.Utils

}

%expect 2
%name parse Module
%tokentype { TokenInfo }
%error { parseError }
%monad      { Alex       }
%lexer      { lexer      }{ TokenInfo TokenEOF _ _ }


%token

-- Keywords:
ASSERT              { TokenInfo ASSERT _ _ }
BOOL                { TokenInfo BOOL _ _ }
BREAK               { TokenInfo BREAK _ _ }
BYTESFROMSTRING     { TokenInfo BYTESFROMSTRING _ _ }
CAT                 { TokenInfo CAT _ _ }
CONTINUE            { TokenInfo CONTINUE _ _ }
CREF                { TokenInfo CRef _ _ }
DECLASSIFY          { TokenInfo DECLASSIFY _ _ }
DIMENSIONALITY      { TokenInfo DIMENSIONALITY _ _ }
DO                  { TokenInfo DO _ _ }
DOMAIN              { TokenInfo DOMAIN _ _ }
DOMAINID            { TokenInfo DOMAINID _ _ }
ELSE                { TokenInfo ELSE _ _ }
FALSE_B             { TokenInfo FALSE_B _ _ }
FLOAT               { TokenInfo FLOAT _ _ }
FLOAT32             { TokenInfo FLOAT32 _ _ }
FLOAT64             { TokenInfo FLOAT64 _ _ }
FOR                 { TokenInfo FOR _ _ }
IF                  { TokenInfo IF _ _ }
IMPORT              { TokenInfo IMPORT _ _ }
INT                 { TokenInfo INT _ _ }
INT16               { TokenInfo INT16 _ _ }
INT32               { TokenInfo INT32 _ _ }
INT64               { TokenInfo INT64 _ _ }
INT8                { TokenInfo INT8 _ _ }
KIND                { TokenInfo KIND _ _ }
MODULE              { TokenInfo MODULE _ _ }
OPERATOR            { TokenInfo OPERATOR _ _ }
PRINT               { TokenInfo PRINT _ _ }
PUBLIC              { TokenInfo PUBLIC _ _ }
REF                 { TokenInfo REF _ _ }
RESHAPE             { TokenInfo RESHAPE _ _ }
RETURN              { TokenInfo RETURN _ _ }
SHAPE               { TokenInfo SHAPE _ _ }
SIZE                { TokenInfo SIZE _ _ }
STRING              { TokenInfo STRING _ _ }
STRINGFROMBYTES     { TokenInfo STRINGFROMBYTES _ _ }
SYSCALL             { TokenInfo SYSCALL _ _ }
TEMPLATE            { TokenInfo TEMPLATE _ _ }
TOSTRING            { TokenInfo TOSTRING _ _ }
TRUE_B              { TokenInfo TRUE_B _ _ }
UINT                { TokenInfo UINT _ _ }
UINT16              { TokenInfo UINT16 _ _ }
UINT32              { TokenInfo UINT32 _ _ }
UINT64              { TokenInfo UINT64 _ _ }
UINT8               { TokenInfo UINT8 _ _ }
WHILE               { TokenInfo WHILE _ _ }
VOID                { TokenInfo VOID _ _ }
XOR_UINT            { TokenInfo XOR_UINT _ _ }
XOR_UINT16          { TokenInfo XOR_UINT16 _ _ }
XOR_UINT32          { TokenInfo XOR_UINT32 _ _ }
XOR_UINT64          { TokenInfo XOR_UINT64 _ _ }
XOR_UINT8           { TokenInfo XOR_UINT8 _ _ }
SYSCALL_RETURN      { TokenInfo SYSCALL_RETURN _ _ }
TYPE                { TokenInfo TYPE _ _ }
STRUCT              { TokenInfo STRUCT _ _ }
STRLEN              { TokenInfo STRLEN _ _ }

-- Identifiers:
kindid              { TokenInfo (IDENTIFIER _ (Just KindID)) _ _ }
domainid            { TokenInfo (IDENTIFIER _ (Just DomainID)) _ _ }
varid               { TokenInfo (IDENTIFIER _ (Just VarID)) _ _ }
procedureid         { TokenInfo (IDENTIFIER _ (Just ProcedureID)) _ _ }
typeid              { TokenInfo (IDENTIFIER _ (Just TypeID)) _ _ }
templateargid       { TokenInfo (IDENTIFIER _ (Just TemplateArgID)) _ _ }
moduleid            { TokenInfo (IDENTIFIER _ (Just ModuleID)) _ _ }
identifier          { TokenInfo (IDENTIFIER _ Nothing) _ _ }

-- Literals:
bin_literal         { TokenInfo (BIN_LITERAL _) _ _ }
dec_literal         { TokenInfo (DEC_LITERAL _) _ _ }
float_literal       { TokenInfo (FLOAT_LITERAL _) _ _ }
hex_literal         { TokenInfo (HEX_LITERAL _) _ _ }
oct_literal         { TokenInfo (OCT_LITERAL _) _ _ }
str_fragment        { TokenInfo (STR_FRAGMENT _) _ _ }
str_identifier      { TokenInfo (STR_IDENTIFIER _) _ _ }

-- Operators from higher to lower precedence:
'='                 { TokenInfo (CHAR '=') _ _ }
AND_ASSIGN          { TokenInfo AND_ASSIGN _ _ }
OR_ASSIGN           { TokenInfo OR_ASSIGN _ _ }
XOR_ASSIGN          { TokenInfo XOR_ASSIGN _ _ }
ADD_ASSIGN          { TokenInfo ADD_ASSIGN _ _ }
SUB_ASSIGN          { TokenInfo SUB_ASSIGN _ _ }
MUL_ASSIGN          { TokenInfo MUL_ASSIGN _ _ }
DIV_ASSIGN          { TokenInfo DIV_ASSIGN _ _ }
MOD_ASSIGN          { TokenInfo MOD_ASSIGN _ _ }
TYPE_QUAL           { TokenInfo TYPE_QUAL _ _ }
'?'                 { TokenInfo (CHAR '?') _ _ }
':'                 { TokenInfo (CHAR ':') _ _ }
LOR_OP              { TokenInfo LOR_OP _ _ }
LAND_OP             { TokenInfo LAND_OP _ _ }
'|'                 { TokenInfo (CHAR '|') _ _ }
'^'                 { TokenInfo (CHAR '^') _ _ }
'&'                 { TokenInfo (CHAR '&') _ _ }
EQ_OP               { TokenInfo EQ_OP _ _ }
NE_OP               { TokenInfo NE_OP _ _ }
'<'                 { TokenInfo (CHAR '<') _ _ }
'>'                 { TokenInfo (CHAR '>') _ _ }
LE_OP               { TokenInfo LE_OP _ _ }
GE_OP               { TokenInfo GE_OP _ _ }
SHL_OP              { TokenInfo SHL_OP _ _ }
SHR_OP              { TokenInfo SHR_OP _ _ }
'+'                 { TokenInfo (CHAR '+') _ _ }
'-'                 { TokenInfo (CHAR '-') _ _ }
'*'                 { TokenInfo (CHAR '*') _ _ }
'/'                 { TokenInfo (CHAR '/') _ _ }
'%'                 { TokenInfo (CHAR '%') _ _ }
INC_OP              { TokenInfo INC_OP _ _ }
DEC_OP              { TokenInfo DEC_OP _ _ }
'.'                 { TokenInfo (CHAR '.') _ _ }
','                 { TokenInfo (CHAR ',') _ _ }
'('                 { TokenInfo (CHAR '(') _ _ }
')'                 { TokenInfo (CHAR ')') _ _ }
'{'                 { TokenInfo (CHAR '{') _ _ }
'}'                 { TokenInfo (CHAR '}') _ _ }
'!'                 { TokenInfo (CHAR '!') _ _ }
'~'                 { TokenInfo (CHAR '~') _ _ }
'['                 { TokenInfo (CHAR '[') _ _ }
']'                 { TokenInfo (CHAR ']') _ _ }
';'                 { TokenInfo (CHAR ';') _ _ }


%right '=' AND_ASSIGN OR_ASSIGN XOR_ASSIGN ADD_ASSIGN SUB_ASSIGN MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN
%left TYPE_QUAL
%left '?' ':'
%left LOR_OP
%left LAND_OP
%left '|'
%left '^'
%left '&'
%nonassoc EQ_OP NE_OP
%nonassoc '<' '>' LE_OP GE_OP
%left SHL_OP SHR_OP
%left '+' '-'
%left '*' '/' '%'
%nonassoc INC_OP
%nonassoc DEC_OP
%right UINV UNEG UMINUS
%left '.'

%%

-- Identifiers

KindId :: { KindName Position }
KindId : kindid { KindName (loc $1) (tokenString $1) }
DomainId :: { DomainName Position }
DomainId : domainid { DomainName (loc $1) (tokenString $1) }
VarId :: { VarName Position }
VarId : varid { VarName (loc $1) (tokenString $1) }
ProcedureId :: { ProcedureName Position }
ProcedureId : procedureid { ProcedureName (loc $1) (tokenString $1) }
TypeId :: { TypeName Position }
TypeId : typeid { TypeName (loc $1) (tokenString $1) }
TemplateArgId :: { TemplateArgName Position }
TemplateArgId : templateargid { TemplateArgName (loc $1) (tokenString $1) }
ModuleId :: { ModuleName Position }
ModuleId : moduleid { ModuleName (loc $1) (tokenString $1) }


-- Program and variable declarations:                                          

Module :: { Module Position }
Module
    : MODULE ModuleId ';' Program { Module (loc $1) (Just $2) $4 }
    | Program { Module (loc $1) Nothing $1 }

Program :: { Program Position }
Program
    : Import_declarations Global_declarations { Program (loc $1) $1 $2 }
    | Global_declarations { Program (loc $1) [] $1 }

Global_declarations :: { [GlobalDeclaration Position] }
Global_declarations
    : Global_declarations Global_declaration { $1 ++ [$2] }
    | Global_declaration { [$1] }

Import_declarations :: { [ImportDeclaration Position] }
Import_declarations
    : Import_declarations Import_declaration { $1 ++ [$2] }
    | Import_declaration { [$1] }

Import_declaration :: { ImportDeclaration Position }
Import_declaration
    : IMPORT ModuleId ';' { Import (loc $1) $2 }

Global_declaration :: { GlobalDeclaration Position }
Global_declaration
    : Variable_declaration ';' { GlobalVariable (loc $1) $1 }
    | Domain_declaration ';' { GlobalDomain (loc $1) $1 }
    | Kind_declaration ';' { GlobalKind (loc $1) $1 }
    | Procedure_definition { GlobalProcedure (loc $1) $1 }
    | Structure_declaration { GlobalStructure (loc $1) $1 }
    | Template_declaration { GlobalTemplate (loc $1) $1 }

Kind_declaration :: { KindDeclaration Position }
Kind_declaration
    : KIND KindId { Kind (loc $1) $2 }

Domain_declaration :: { DomainDeclaration Position }
Domain_declaration
    : DOMAIN DomainId KindId { Domain (loc $1) $2 $3 }

Maybe_dimensions :: { Maybe (Sizes Position) }
Maybe_dimensions
    : {- nothing -} { Nothing }
    | Dimensions { Just $1 }

Variable_initialization :: { VariableInitialization Position }
Variable_initialization
    : VarId Maybe_dimensions { VariableInitialization (loc $1) $1 $2 Nothing }
    | VarId Maybe_dimensions '=' Expression { VariableInitialization (loc $1) $1 $2 (Just $4) }

Variable_initializations :: { NeList (VariableInitialization Position) }
Variable_initializations
    : Variable_initializations ',' Variable_initialization { snocNe $1 $3 }
    | Variable_initialization { WrapNe $1 }

Variable_declaration :: { VariableDeclaration Position }
Variable_declaration
    : Type_specifier Variable_initializations { VariableDeclaration (loc $1) $1 $2 }

Procedure_parameter :: { ProcedureParameter Position }
Procedure_parameter
    : Type_specifier VarId { ProcedureParameter (loc $1) $1 $2 }

Dimensions :: { Sizes Position }
Dimensions
    : '(' Dimension_list ')' { Sizes $2 }

Expression_list :: { NeList (Expression Position) }
Expression_list
    : Expression_list ',' Expression { snocNe $1 $3 }
    | Expression { WrapNe $1 }

Dimension_list :: { NeList (Expression Position) }
Dimension_list
    : Expression_list { $1 }


-- Types:                                                                     

Type_specifier :: { TypeSpecifier Position }
Type_specifier
    : Maybe_sectype_specifier Datatype_specifier Maybe_dimtype_specifier { TypeSpecifier (maybe (loc $2) loc $1) $1 $2 $3 }

Maybe_sectype_specifier :: { Maybe (SecTypeSpecifier Position) }
Maybe_sectype_specifier
    : {- nothing -} { Nothing }
    | Sectype_specifier { Just $1 }

Maybe_dimtype_specifier :: { Maybe (DimtypeSpecifier Position) }
Maybe_dimtype_specifier
    : {- nothing -} { Nothing }
    | Dimtype_specifier { Just $1 }

Sectype_specifier :: { SecTypeSpecifier Position }
Sectype_specifier
    : PUBLIC { PublicSpecifier (loc $1) }
    | DomainId { PrivateSpecifier (loc $1) $1 }

Datatype_specifier :: { DatatypeSpecifier Position }
Datatype_specifier
    : Primitive_datatype { PrimitiveSpecifier (loc $1) $1 }
    | Template_struct_datatype_specifier { $1 }
    | TypeId { VariableSpecifier (loc $1) $1 }

Primitive_datatype :: { PrimitiveDatatype Position }
Primitive_datatype
    : BOOL       { DatatypeBool       (loc $1) }
    | INT        { DatatypeInt        (loc $1) }
    | UINT       { DatatypeUint       (loc $1) }
    | INT8       { DatatypeInt8       (loc $1) }
    | UINT8      { DatatypeUint8      (loc $1) }
    | INT16      { DatatypeInt16      (loc $1) }
    | UINT16     { DatatypeUint16     (loc $1) }
    | INT32      { DatatypeInt32      (loc $1) }
    | UINT32     { DatatypeUint32     (loc $1) }
    | INT64      { DatatypeInt64      (loc $1) }
    | UINT64     { DatatypeUint64     (loc $1) }
    | STRING     { DatatypeString     (loc $1) }
    | XOR_UINT8  { DatatypeXorUint8   (loc $1) }
    | XOR_UINT16 { DatatypeXorUint16  (loc $1) }
    | XOR_UINT32 { DatatypeXorUint32  (loc $1) }
    | XOR_UINT64 { DatatypeXorUint64  (loc $1) }
    | XOR_UINT   { DatatypeXorUint    (loc $1) }
    | FLOAT      { DatatypeFloat      (loc $1) }
    | FLOAT32    { DatatypeFloat32    (loc $1) }
    | FLOAT64    { DatatypeFloat64    (loc $1) }

Template_struct_datatype_specifier :: { DatatypeSpecifier Position }
Template_struct_datatype_specifier
    : TypeId '<' Template_type_arguments '>' { TemplateSpecifier (loc $1) $1 $3 }

Template_type_argument :: { TemplateTypeArgument Position }
Template_type_argument
    : TemplateArgId { GenericTemplateTypeArgument (loc $1) $1 } -- type, domain or variable identifier
    | TypeId '<' Template_type_arguments '>' { TemplateTemplateTypeArgument (loc $1) $1 $3 }
    | Primitive_datatype { PrimitiveTemplateTypeArgument (loc $1) $1 }
    | Int_literal { IntTemplateTypeArgument (loc $1) (unLoc $1) }
    | PUBLIC { PublicTemplateTypeArgument (loc $1) }

Template_type_arguments :: { [TemplateTypeArgument Position] }
Template_type_arguments
    : Template_type_arguments ',' Template_type_argument { $1 ++ [$3] }
    | Template_type_argument { [$1] }

Dimtype_specifier :: { DimtypeSpecifier Position }
Dimtype_specifier
    : '[' '[' Expression ']' ']' { DimSpecifier (loc $1) $1 }

-- Templates:                                                                

Template_declaration :: { TemplateDeclaration Position }
Template_declaration
    : TEMPLATE '<' Template_quantifiers '>' Structure_declaration { TemplateStructureDeclaration (loc $1) $3 $5 } 
    | TEMPLATE '<' Template_quantifiers '>' Procedure_definition { TemplateProcedureDeclaration (loc $1) $3 $5 }

Template_quantifiers :: { NeList (TemplateQuantifier Position) }
Template_quantifiers
    : Template_quantifiers ',' Template_quantifier { snocNe $1 $3 }
    | Template_quantifier { WrapNe $1 }

Template_quantifier :: { TemplateQuantifier Position }
Template_quantifier
    : DOMAIN DomainId ':' KindId { DomainQuantifier (loc $1) $2 (Just $4)  }
    | DOMAIN DomainId { DomainQuantifier (loc $1) $2 Nothing }
    | DIMENSIONALITY VarId { DimensionQuantifier (loc $1) $2 }
    | TYPE TypeId { DataQuantifier (loc $1) $2 }

-- Structures:                                                                 
Structure_declaration :: { StructureDeclaration Position }
Structure_declaration
    : STRUCT TypeId '{' Attribute_list '}' { StructureDeclaration (loc $1) $2 $4 }

Attribute_list :: { [Attribute Position] }
Attribute_list
    : Attribute_list Attribute { $1 ++ [$2] }
    | {- empty -} { [] }

Attribute :: { Attribute Position }
Attribute
    : Type_specifier VarId ';' { Attribute (loc $1) $1 $2 }

-- Procedures:                                                                

Return_type_specifier :: { ReturnTypeSpecifier Position }
Return_type_specifier
    : VOID { ReturnType (loc $1) Nothing }
    | Type_specifier { ReturnType (loc $1) (Just $1) }

Procedure_definition :: { ProcedureDeclaration Position }
Procedure_definition
    : Operator_definition { $1 }
    | Return_type_specifier ProcedureId '(' Procedure_parameter_list ')' Compound_statement { ProcedureDeclaration (loc $1) $1 $2 $4 (unLoc $6) }
  
Procedure_parameter_list :: { [ProcedureParameter Position] }
Procedure_parameter_list
    : Procedure_parameter_list ',' Procedure_parameter { $1 ++ [$3] }
    | Procedure_parameter { [$1] }
    | {- empty -} { [] }

Op_helper :: { ([ProcedureParameter Position],[Statement Position]) }
Op_helper
    : '(' Procedure_parameter_list ')' Compound_statement { ($2,unLoc $4) }

Op :: { Op }
Op
    : '+'     { OpAdd  }
    | '&'     { OpBand }
    | '|'     { OpBor  }
    | '/'     { OpDiv  }
    | '>'     { OpGt   }
    | '<'     { OpLt   }
    | '%'     { OpMod  }
    | '*'     { OpMul  }
    | '-'     { OpSub  }
    | '^'     { OpXor  }
    | '!'     { OpExcM }
    | EQ_OP   { OpEq   }
    | GE_OP   { OpGe   }
    | LAND_OP { OpLand }
    | LE_OP   { OpLe   }
    | LOR_OP  { OpLor  }
    | NE_OP   { OpNe   }
    | SHL_OP  { OpShl  }
    | SHR_OP  { OpShr  }

Operator_definition :: { ProcedureDeclaration Position }
Operator_definition
    :  Return_type_specifier OPERATOR Op Op_helper { let (ps,ss) = $4 in OperatorDeclaration (loc $1) $1 $3 ps ss }

-- Statements:                                                              

Compound_statement :: { Loc Position [Statement Position] }
Compound_statement
    : '{' '}' { Loc (loc $1) [] }
    | '{' Statement_list '}' { Loc (loc $1) $2 }

Statement_list :: { [Statement Position] }
Statement_list
    : Statement_list Statement { $1 ++ [$2] }
    | Statement { [$1] }

Statement :: { Statement Position }
Statement
    : Compound_statement { CompoundStatement (loc $1) (unLoc $1) }
    | If_statement { $1 }
    | For_statement { $1 }
    | While_statement { $1 }
    | Dowhile_statement { $1 }
    | Assert_statement { $1 }
    | Print_statement { $1 }
    | Syscall_statement { $1 }
    | Variable_declaration ';' { VarStatement (loc $1) $1 } 
    | RETURN Expression ';' { ReturnStatement (loc $1) (Just $2) }
    | RETURN ';' { ReturnStatement (loc $1) Nothing }
    | CONTINUE ';' { ContinueStatement (loc $1) }
    | BREAK ';' { BreakStatement (loc $1) }
    | ';' { CompoundStatement (loc $1) [] }
    | Expression ';' { ExpressionStatement (loc $1) $1 }

If_statement :: { Statement Position }
If_statement
    : IF '(' Expression ')' Statement Else_statement { IfStatement (loc $1) $3 $5 $6 }

Else_statement :: { Maybe (Statement Position) }
Else_statement
    : {- empty -} { Nothing }
    | ELSE Statement { Just $2 }

For_initializer :: { ForInitializer Position }
For_initializer
    : Maybe_expression { InitializerExpression $1 }
    | Variable_declaration { InitializerVariable $1 }

For_statement :: { Statement Position }
For_statement
    : FOR '(' For_initializer  ';' Maybe_expression ';' Maybe_expression ')' Statement { ForStatement (loc $1) $3 $5 $7 $9 }

Maybe_expression :: { Maybe (Expression Position) }
Maybe_expression
    : {- empty -} { Nothing } 
    | Expression { Just $1 }

While_statement :: { Statement Position }
While_statement
    : WHILE '(' Expression ')' Statement { WhileStatement (loc $1) $3 $5 }

Print_statement :: { Statement Position }
Print_statement
    : PRINT '(' Expression_list ')' ';' { PrintStatement (loc $1) $3 }

Dowhile_statement :: { Statement Position }
Dowhile_statement
    : DO Statement WHILE '(' Expression ')' ';' { DowhileStatement (loc $1) $2 $5 }

Assert_statement :: { Statement Position }
Assert_statement
    : ASSERT '(' Expression ')' ';' { AssertStatement (loc $1) $3 }

Syscall_statement :: { Statement Position }
Syscall_statement
    : SYSCALL '(' String_literal ')' ';' { SyscallStatement (loc $1) (unLoc $3) [] }
    | SYSCALL '(' String_literal ',' Syscall_parameters ')' ';' { SyscallStatement (loc $1) (unLoc $3) $5 }

Syscall_parameters :: { [SyscallParameter Position] }
Syscall_parameters
    : Syscall_parameters ',' Syscall_parameter { $1 ++ [$3] }
    | Syscall_parameter { [$1] }

Syscall_parameter :: { SyscallParameter Position }
Syscall_parameter
    : SYSCALL_RETURN VarId { SyscallReturn (loc $1) $2 }
    | REF VarId { SyscallPushRef (loc $1) $2 }
    | CREF Expression { SyscallPushCRef (loc $1) $2 }
    | Expression { SyscallPush (loc $1) $1 }

-- Indices: not strictly expressions as they only appear in specific context  

Subscript :: { Subscript Position }
Subscript
    : '[' Indices ']' { $2 }
   
Indices :: { NeList (Index Position) }
Indices 
    : Indices ',' Index { snocNe $1 $3 }
    | Index { WrapNe $1 }

-- Precedence of slicing operator? Right now it binds weakest as it can appear
-- in very specific context. However, if we ever wish for "foo : bar" evaluate
-- to value in some other context we need to figure out sane precedence.
Index :: { Index Position }
Index
    : Maybe_expression ':' Maybe_expression { IndexSlice (maybe (loc $2) loc $1) $1 $3 }
    | Expression { IndexInt (loc $1) $1 }

-- Expressions:                                                                

Lvalue :: { PostfixExpression Position }
Lvalue
    : Postfix_expression { $1 }

Expression :: { Expression Position }
Expression
    : Assignment_expression { $1 }

Assignment_expression :: { Expression Position }
Assignment_expression {- WARNING: RIGHT RECURSION -}
    : Lvalue '=' Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignEqual $3 }
    | Lvalue MUL_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignMul $3 }
    | Lvalue DIV_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignDiv $3 }
    | Lvalue MOD_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignMod $3 }
    | Lvalue ADD_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignAdd $3 }
    | Lvalue SUB_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignSub $3 }
    | Lvalue AND_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignAnd $3 }
    | Lvalue OR_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignOr $3 }
    | Lvalue XOR_ASSIGN Assignment_expression { BinaryAssign (loc $1) $1 BinaryAssignXor $3 }
    | Qualified_expression { QualifiedAssignExpr (loc $1) $1 }

Qualified_type :: { QualifiedType Position }
Qualified_type
    : PUBLIC { PublicQualifiedType (loc $1) }
    | Primitive_datatype { PrimitiveQualifiedType (loc $1) $1 }
    | Dimtype_specifier { DimQualifiedType (loc $1) $1 }
    | identifier { GenericQualifiedType (loc $1) (tokenString $1) }

Qualified_types :: { NeList (QualifiedType Position) }
Qualified_types
    : Qualified_types Qualified_type { snocNe $1 $2 }
    | Qualified_type { WrapNe $1 }

Qualified_expression :: { QualifiedExpression Position }
Qualified_expression
    : Qualified_expression TYPE_QUAL Qualified_types { QualExpr (loc $1) $1 $3 }
    | Conditional_expression { QualCond (loc $1) $1 }

Conditional_expression :: { ConditionalExpression Position }
Conditional_expression
    : Logical_or_expression '?' Expression ':' Expression { CondExpr (loc $1) (LorExpression $1) $3 $5 }
    | Logical_or_expression { LorExpr (loc $1) (LorExpression $1) }

Logical_or_expression :: { NeList (LandExpression Position) }
Logical_or_expression
    : Logical_or_expression LOR_OP Logical_and_expression { snocNe $1 (LandExpression $3) }
    | Logical_and_expression { WrapNe $ LandExpression $1 }

Logical_and_expression :: { NeList (BitwiseOrExpression Position) }
Logical_and_expression
    : Logical_and_expression LAND_OP Bitwise_or_expression { snocNe $1 (BitwiseOrExpression $3) }
    | Bitwise_or_expression { WrapNe $ BitwiseOrExpression $1 }

Bitwise_or_expression :: { NeList (BitwiseXorExpression Position) }
Bitwise_or_expression
    : Bitwise_or_expression '|' Bitwise_xor_expression { snocNe $1 (BitwiseXorExpression $3) }
    | Bitwise_xor_expression { WrapNe $ BitwiseXorExpression $1 }

Bitwise_xor_expression :: { NeList (BitwiseAndExpression Position) }
Bitwise_xor_expression
    : Bitwise_xor_expression '^' Bitwise_and_expression { snocNe $1 (BitwiseAndExpression $3) }
    | Bitwise_and_expression { WrapNe $ BitwiseAndExpression $1 }

Bitwise_and_expression :: { NeList (EqualityExpression Position) }
Bitwise_and_expression
    : Bitwise_and_expression '&' Equality_expression { snocNe $1 (EqualityExpression $3) }
    | Equality_expression { WrapNe $ EqualityExpression $1 }

Equality_expression :: { SepList EqExprOp (RelationalExpression Position) }
Equality_expression
    : Equality_expression EQ_OP Relational_expression { snocSep $1 EqOp (RelationalExpression $3) }
    | Equality_expression NE_OP Relational_expression { snocSep $1 NeOp (RelationalExpression $3) }
    | Relational_expression { WrapSep $ RelationalExpression $1 }

Relational_expression :: { SepList RelExprOp (ShiftExpression Position) }
Relational_expression
    : Relational_expression LE_OP Shift_expression { snocSep $1 LeOp (ShiftExpression $3) }
    | Relational_expression GE_OP Shift_expression { snocSep $1 GeOp (ShiftExpression $3) }
    | Relational_expression '<' Shift_expression { snocSep $1 LtOp (ShiftExpression $3) }
    | Relational_expression '>' Shift_expression { snocSep $1 GtOp (ShiftExpression $3) }
    | Shift_expression { WrapSep $ ShiftExpression $1 }

Shift_expression :: { SepList ShExprOp (AdditiveExpression Position) }
Shift_expression
    : Shift_expression SHL_OP Additive_expression { snocSep $1 ShlOp (AdditiveExpression $3) }
    | Shift_expression SHR_OP Additive_expression { snocSep $1 ShrOp (AdditiveExpression $3) }
    | Additive_expression { WrapSep $ AdditiveExpression $1 }

Additive_expression :: { SepList AddExprOp (MultiplicativeExpression Position) }
Additive_expression
    : Additive_expression '+' Multiplicative_expression { snocSep $1 PlusOp (MultiplicativeExpression $3) }
    | Additive_expression '-' Multiplicative_expression { snocSep $1 MinusOp (MultiplicativeExpression $3) }
    | Multiplicative_expression { WrapSep $ MultiplicativeExpression $1 }

Multiplicative_expression :: { SepList MulExprOp (CastExpression Position) }
Multiplicative_expression
    : Multiplicative_expression '*' Cast_expression { snocSep $1 MulOp $3 }
    | Multiplicative_expression '/' Cast_expression { snocSep $1 DivOp $3 }
    | Multiplicative_expression '%' Cast_expression { snocSep $1 ModOp $3 }
    | Cast_expression { WrapSep $1 }

-- I would use the following rule, but bison seems to think that
-- this would cause a reduce/reduce conflict. I don't quite
-- understand why, but right now I'll be using this workaround.
-- I think it's a LALR(1) specific limitation.
-- 
--  cast_expression
--   : '(' datatype_specifier ')' cast_expression
--     { ... }
--   | prefix_op
--   ;

Cast_expression :: { CastExpression Position }
Cast_expression
    : '(' Primitive_datatype ')' Cast_expression { PrimCastExpr (loc $1) $2 $4 }
    | '(' TypeId ')' Cast_expression { VarCastExpr (loc $1) $2 $4 }
    | Prefix_op { PrefixCastExpr (loc $1) $1 }

Prefix_op :: { PrefixOp Position }
Prefix_op
    : INC_OP Lvalue { PrefixInc (loc $1) $2 }
    | DEC_OP Lvalue { PrefixDec (loc $1) $2 }
    | Postfix_op { PrefixPost (loc $1) $1 }

Postfix_op :: { PostfixOp Position }
Postfix_op
    : Lvalue INC_OP { PostfixInc (loc $1) $1 }
    | Lvalue DEC_OP { PostfixDec (loc $1) $1 }
    | Unary_expression { PostfixUnary (loc $1) $1 }

Unary_expression :: { UnaryExpression Position }
Unary_expression
    : '-' Cast_expression %prec UMINUS { UminusExpr (loc $1) $2 }
    | '!' Cast_expression %prec UNEG { UnegExpr (loc $1) $2 }
    | '~' Cast_expression %prec UINV { UinvExpr (loc $1) $2 }
    | Postfix_expression { Upost (loc $1) $1 }

Cat_expression :: { CatExpression Position }
Cat_expression
    : CAT '(' Expression ',' Expression ',' Int_literal ')' { CatExpr (loc $1) $3 $5 (Just $ unLoc $7) }
    | CAT '(' Expression ',' Expression ')' { CatExpr (loc $1) $3 $5 Nothing }

Postfix_expression :: { PostfixExpression Position }
Postfix_expression
    : DECLASSIFY '(' Expression ')' { DeclassifyExpr (loc $1) $3 }
    | SIZE '(' Expression ')' { SizeExpr (loc $1) $3 }
    | SHAPE '(' Expression ')' { ShapeExpr (loc $1) $3 }
    | Cat_expression { PostCatExpr (loc $1) $1 }
    | DOMAINID '(' Sectype_specifier ')' { DomainIdExpr (loc $1) $3 }
    | RESHAPE '(' Expression_list ')' { ReshapeExpr (loc $1) $3 }
    | TOSTRING '(' Expression ')' { ToStringExpr (loc $1) $3 }
    | STRLEN '(' Expression ')' { StrlenExpr (loc $1) $3 }
    | STRINGFROMBYTES '(' Expression ')' { StringFromBytesExpr (loc $1) $3 }
    | BYTESFROMSTRING '(' Expression ')' { BytesFromStringExpr (loc $1) $3 }
    | ProcedureId '(' ')' { ProcCallExpr (loc $1) $1 [] }
    | ProcedureId '(' Expression_list ')' { ProcCallExpr (loc $1) $1 (toList $3) }
    | Postfix_expression Subscript { PostIndexExpr (loc $1) $1 $2 }
    | Postfix_expression '.' VarId { SelectionExpr (loc $1) $1 $3 }
    | Primary_expression { PostPrimExpr (loc $1) $1 }

Primary_expression :: { PrimaryExpression Position }
Primary_expression
    : '(' Expression ')' {PExpr (loc $1) $2 }
    | '{' Expression_list '}' { ArrayConstructorPExpr (loc $1) $2 }
    | VarId { RVariablePExpr (loc $1) $1 }
    | Literal { LitPExpr (loc $1) $1 }

Int_literal :: { Loc Position Integer }
Int_literal
    : bin_literal { Loc (loc $1) (tokenInteger $1) }
    | oct_literal { Loc (loc $1) (tokenInteger $1) }
    | dec_literal { Loc (loc $1) (tokenInteger $1) }
    | hex_literal { Loc (loc $1) (tokenInteger $1) }

Float_literal :: { Loc Position Float }
Float_literal
    : float_literal { Loc (loc $1) (tokenFloat $1) }

String_literal :: { Loc Position String }
String_literal
    : String_literal String_part { Loc (loc $1) (unLoc $1 ++ unLoc $2) }
    | String_part { $1 }

String_part :: { Loc Position String }
String_part
    : str_identifier { Loc (loc $1) (tokenString $1) }
    | str_fragment { Loc (loc $1) (tokenString $1) }

Bool_literal :: { Loc Position Bool }
Bool_literal
    : TRUE_B { Loc (loc $1) (tokenBool $1) }
    | FALSE_B { Loc (loc $1) (tokenBool $1) }

Literal :: { Literal Position }
Literal
    : Int_literal { IntLit (loc $1) (unLoc $1) }
    | String_literal { StringLit (loc $1) (unLoc $1) }
    | Bool_literal { BoolLit (loc $1) (unLoc $1) }
    | Float_literal { FloatLit (loc $1) (unLoc $1) }


{

-- Parser Functions ------------------------------------------------------------

parseFile :: String -> IO (Module Position)
parseFile fn = do
    str <- liftIO (readFile fn)
    let toks = runIdAlexTokens fn str
    print toks
    parseSecreC fn str

parseSecreC :: String -> String -> IO (Module Position)
parseSecreC fn str = case runIdAlex fn str parse of
    Left err -> fail err
    Right a -> return a

parseError :: TokenInfo -> Alex a
parseError info = do
    flushLexer 
    f <- gets filename 
    let e = case tSymb info of
            TokenError -> LexicalException info
            TokenEOF   -> EOFException
            _          -> ParsingException info
    throwError $ parserError (tLoc info) f e

}
