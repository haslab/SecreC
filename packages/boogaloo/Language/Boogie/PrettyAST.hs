{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

-- | Pretty printing of AST nodes
module Language.Boogie.PrettyAST (
  idpretty,
  refDoc,
  logDoc
) where

import Language.Boogie.Pretty
import Language.Boogie.AST
import Language.Boogie.Position
import Language.Boogie.Tokens
import Data.Maybe
import qualified Data.Map as M

{- Interface -}

-- | Pretty-printed program
instance Pretty Program where 
  pretty (Program decls) = (vsep . punctuate linebreak . map (either pretty pretty)) decls
      
{- Types -}

-- | Pretty-printed type
instance Pretty Type where 
  pretty BoolType = text "bool"
  pretty IntType = text "int"
  pretty RealType = text "real"
  pretty (MapType fv domains range) = parens (typeArgsDoc fv <> 
    brackets (commaSep (map pretty domains)) <+>
    pretty range)
  pretty (IdType id args) = condParens (length args > 0) (text id <+> hsep (map pretty args))
  
{- Expressions -}

-- | Binding power of an expression
power :: BareExpression -> Int
power (Literal _) = 10
power (Logical _ _) = 10
power (Var _) = 10
power (Application _ _) = 10
power (Old _) = 10
power (IfExpr _ _ _) = 10
power (Quantified _ _ _ _ _) = 10
power (MapSelection _ _) = 9
power (MapUpdate _ _ _) = 9
power (Coercion _ _) = 8
power (UnaryExpression _ _) = 7
power (BinaryExpression op _ _) 
  | op `elem` [Times, Div, Mod] = 6 
  | op `elem` [Plus, Minus] = 5
  | op `elem` [Eq, Neq, Ls, Leq, Gt, Geq, Lc] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies, Explies] = 1
  | op `elem` [Equiv] = 0

-- | Pretty-printed expression  
exprDoc :: Expression -> Doc
exprDoc e = exprDocAt (-1) e

-- | 'exprDocAt' @n expr@ : print @expr@ in a context with binding power @n@
exprDocAt :: Int -> Expression -> Doc
exprDocAt n (Pos _ e) = condParens (n' <= n) (
  case e of
    Literal v -> pretty v
    Logical t r -> logDoc r
    Var id -> text id
    Application id args -> text id <> parens (commaSep (map exprDoc args))
    MapSelection m args -> exprDocAt n' m <> brackets (commaSep (map exprDoc args))
    MapUpdate m args val -> exprDocAt n' m <> brackets (commaSep (map exprDoc args) <+> text ":=" <+> exprDoc val)
    Old e -> text "old" <+> parens (exprDoc e)
    IfExpr cond e1 e2 -> text "if" <+> exprDoc cond <+> text "then" <+> exprDoc e1 <+> text "else" <+> exprDoc e2
    Coercion e t -> exprDocAt n' e <+> text ":" <+> pretty t
    UnaryExpression unOp e -> pretty unOp <> exprDocAt n' e
    BinaryExpression binOp e1 e2 -> exprDocAt n' e1 <+> pretty binOp <+> exprDocAt n' e2
    Quantified qOp fv vars trggs e -> parens (pretty qOp <+> typeArgsDoc fv <+> commaSep (map idpretty vars) <+> text "::" <+> hsep (map qTriggerAttsDoc trggs) <+> exprDoc e)
  )
  where
    n' = power e

qTriggerAttsDoc :: QTriggerAttribute -> Doc
qTriggerAttsDoc (Left trggs) = braces $ commaSep $ map pretty trggs
qTriggerAttsDoc (Right att) = pretty att

instance Pretty BareExpression where pretty e = exprDoc (gen e)

{- Statements -}

-- | Pretty-printed statement
statementDoc :: Statement -> Doc
statementDoc (Pos _ s) = case s of
  Predicate attrs (SpecClause _ isAssume e) -> (if isAssume then text "assume" else text "assert") <+> hsep (map pretty attrs) <+> pretty e <> semi
  Havoc vars -> text "havoc" <+> commaSep (map text vars) <> semi
  Assign lhss rhss -> commaSep (map lhsDoc lhss) <+> 
    text ":=" <+> commaSep (map pretty rhss) <> semi
  Call atts lhss name args -> text "call" <+>
    hsep (map pretty atts) <+> 
    commaSep (map text lhss) <+>
    option (not (null lhss)) (text ":=") <+> 
    text name <> 
    parens (commaSep (map pretty args)) <> 
    semi
  CallForall name args -> text "call forall" <+> 
    text name <> 
    parens (commaSep (map wildcardDoc args)) <> 
    semi
  If cond thenBlock elseBlock -> text "if" <+> parens (wildcardDoc cond) <+> 
    bracedBlockDoc thenBlock <+>
    optionMaybe elseBlock elseDoc
  While cond invs b -> nestDef (
      text "while" <+> parens (wildcardDoc cond) $+$
      vsep (map specClauseDoc invs)
    ) $+$ bracedBlockDoc b
  Break ml -> (text "break" <+> optionMaybe ml text) <> semi
  Return -> text "return" <> semi
  Goto ids -> text "goto" <+> commaSep (map text ids) <> semi
  Skip -> empty
  where
    lhsDoc (id, selects) = text id <> hcat (map (\sel -> brackets (commaSep (map pretty sel))) selects)
    wildcardDoc Wildcard = text "*"
    wildcardDoc (Expr e) = pretty e
    elseDoc b = text "else" <+> bracedBlockDoc b
    
instance Pretty BareStatement where pretty s = statementDoc (gen s)

{- Blocks -}

commentDoc c = text c

blockDoc block = vsep (map (either commentDoc lStatementDoc) block)
  where
    lStatementDoc (Pos _ (lbs, s)) = hsep (map labelDoc lbs) <+> statementDoc s
    
bracedBlockDoc block = 
  nestDef (lbrace $+$ blockDoc block) $+$
  rbrace

bodyDoc :: Body -> Doc
bodyDoc (vars, block) =
  nestDef (lbrace $+$ (vsep (map (uncurry varDeclDoc) vars) $+$ blockDoc block)) $+$
  rbrace
  
transformedBlockDoc block = vsep (map basicBlockDoc block)
  where
    basicBlockDoc (l, stmts) = nestDef (labelDoc l $+$ vsep (map statementDoc stmts))

labelDoc l = text l <> text ":"

{- Specs -}     

specpretty Precondition = text "precondition"
specpretty Postcondition = text "postcondition"
specpretty LoopInvariant = text "invariant"

specClauseDoc (SpecClause t free e) = option free (text "free") <+> specpretty t <+> pretty e <> semi

{- Declarations -}

-- | Pretty-printed top-level declaration
instance Pretty BareDecl where 
  pretty d = case d of
    TypeDecl atts ts -> typeDeclDoc atts ts
    ConstantDecl atts unique names t orderSpec complete -> constantDoc atts unique names t orderSpec complete
    FunctionDecl attrs name fv args ret mb -> functionDoc attrs name fv args ret mb
    AxiomDecl atts e -> text "axiom" <+> hsep (map pretty atts) <+> pretty e <> semi
    VarDecl atts vars -> varDeclDoc atts vars
    ProcedureDecl atts name fv args rets specs mb -> procedureDoc atts name fv args rets specs mb
    ImplementationDecl atts name fv args rets bodies -> implementationDoc atts name fv args rets bodies
  
typeDeclDoc atts ts = 
  text "type" <+> 
  hsep (map pretty atts) <+> 
  commaSep (map newpretty ts) <> 
  semi
  where
    newpretty (NewType id args mVal) = text id <+> hsep (map text args) <+> optionMaybe mVal (\t -> text "=" <+> pretty t)
    
constantDoc atts unique names t orderSpec complete =
  (text "const" <+>
  hsep (map pretty atts) <+> 
  option unique (text "unique") <+>
  commaSep (map text names) <>
  text ":" <+> pretty t <+>
  optionMaybe orderSpec orderSpecDoc <+>
  option complete (text "complete")) <> 
  semi
  where
    orderSpecDoc parents = text "extends" <+> commaSep (map parentDoc parents)
    parentDoc (u, id) = option u (text "unique") <+> text id
    
functionDoc attrs name fv args ret mb =
  text "function" <+>
  hsep (map pretty attrs) <+>
  text name <>
  typeArgsDoc fv <>
  parens (commaSep (map fArgDoc args)) <+>
  text "returns" <+>
  parens (fArgDoc ret) <>
  option (isNothing mb) semi $+$
  optionMaybe mb (braces . spaces . pretty)
  where
    fArgDoc (Nothing, t) = pretty t
    fArgDoc (Just id, t) = idpretty (id, t) 

varDeclDoc :: [Attribute] -> [IdTypeWhere] -> Doc
varDeclDoc atts vars =
  text "var" <+>
  hsep (map pretty atts) <+> 
  commaSep (map idTypeWhereDoc vars) <>
  semi
      
procedureDoc atts name fv args rets specs mb =
  nestDef (
  text "procedure" <+>
  hsep (map pretty atts) <+> 
  text name <>
  typeArgsDoc fv <>
  parens (commaSep (map idTypeWhereDoc args)) <+>
  text "returns" <+>
  parens (commaSep (map idTypeWhereDoc rets)) <>
  option (isNothing mb) semi $+$
  vsep (map specDoc specs)) $+$
  optionMaybe mb bodyDoc
  where
    specDoc (Requires free e) = option free (text "free") <+>
      text "requires" <+>
      pretty e <>
      semi
    specDoc (Ensures free e) = option free (text "free") <+>
      text "ensures" <+>
      pretty e <>
      semi
    specDoc (Modifies free ids) = option free (text "free") <+>
      text "modifies" <+>
      commaSep (map text ids) <>
      semi
    
implementationDoc atts name fv args rets bodies =
  text "implementation" <+>
  hsep (map pretty atts) <+> 
  text name <>
  typeArgsDoc fv <>
  parens (commaSep (map idpretty args)) <+>
  text "returns" <+>
  parens (commaSep (map idpretty rets)) $+$
  vsep (map bodyDoc bodies)
  
{- Values -}

-- | Pretty-printed map reference
refDoc :: Ref -> Doc
refDoc r = text "m'" <> int r

-- | Pretty-printed logical variable
logDoc :: Ref -> Doc
logDoc r = text "l'" <> int r
    
-- | Pretty-printed value
instance Pretty Value where
  pretty (IntValue n) = integer n
  pretty (BoolValue False) = text "false"
  pretty (BoolValue True) = text "true"
  pretty (CustomValue t n) = pretty t <+> int n
  pretty (Reference _ r) = refDoc r  
  
{- Attributes and triggers -}

instance Pretty AttrValue where
  pretty (EAttr expr) = pretty expr
  pretty (SAttr str) = dquotes $ text str
  
instance Pretty Attribute where
  pretty attr = braces $ text ":" <> text (aTag attr) <+> commaSep (map pretty $ aValues attr)
  
{- Misc -}

defaultIndent = 4
-- | Nest with default indentation
nestDef = nest defaultIndent
    
-- | Pretty-printed type arguments     
typeArgsDoc tv = option (not (null tv)) (angles (commaSep (map text tv)))

-- | Pretty-printed name declaration
idpretty (id, t) = text id <> text ":" <+> pretty t

-- | Pretty-printed name declaration with a where clause
idTypeWhereDoc (IdTypeWhere id t w) = idpretty (id, t) <+> case w of
  (Pos _ (Literal (BoolValue True))) -> empty
  e -> text "where" <+> pretty e

instance Pretty a => Pretty (Pos a) where
  pretty (Pos _ x) = pretty x
