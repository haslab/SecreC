-- Happy is a LALR(1) parser generator, so we use an intermediate Parsec parser with infinite lookahead to resolve conflicts with ambiguous ids.

{-# LANGUAGE ViewPatterns, FlexibleContexts #-}

module Language.SecreC.Parser.IdLexer where
    
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Error
import Language.SecreC.Position

import Text.Regex.Applicative

import Control.Monad
import Control.Monad.Except
    
-- * Regular expression rules
    
type ScRE = RE TokenInfo [TokenInfo]

scToken :: Token -> ScRE
scToken t = (:[]) <$> psym (\c -> tSymb c == t) 

scTokenPred :: (Token -> Bool) -> ScRE
scTokenPred p = (:[]) <$> psym (p . tSymb) 

scIdentifier :: IdentifierType -> ScRE
scIdentifier ty = msym (\c -> case tSymb c of
    IDENTIFIER str Nothing -> Just [c { tSymb = IDENTIFIER str (Just ty) }]
    otherwise -> Nothing)

scVarId :: ScRE
scVarId = scIdentifier VarID

scTypeId :: ScRE
scTypeId = scIdentifier TypeID

scKindId :: ScRE
scKindId = scIdentifier KindID

scDomainId :: ScRE
scDomainId = scIdentifier DomainID

scModuleId :: ScRE
scModuleId = scIdentifier ModuleID

scTemplateArgId :: ScRE
scTemplateArgId = scIdentifier TemplateArgID

scProcedureId :: ScRE
scProcedureId = scIdentifier ProcedureID

scOptional :: ScRE -> ScRE
scOptional r = (maybe [] id) <$> optional r

(<++>) :: ScRE -> ScRE -> ScRE
r1 <++> r2 = (pure (++) <*> r1) <*> r2

scAny :: ScRE
scAny = (:[]) <$> anySym

scMany :: ScRE -> ScRE
scMany r = concat <$> many r

scSome :: ScRE -> ScRE
scSome r = concat <$> some r

scSepBy1 :: ScRE -> ScRE -> ScRE
scSepBy1 r sep = r <++> scMany (sep <++> r)

scSepBy :: ScRE -> ScRE -> ScRE
scSepBy r sep = scOptional (scSepBy1 r sep)

-- lex module ids
scModules :: ScRE
scModules = (scToken MODULE <++> scModuleId)
        <|> (scToken IMPORT <++> scModuleId) 

-- lex kind ids
scKinds :: ScRE
scKinds = (scToken KIND <++> scKindId)
      <|> (scToken DOMAIN <++> scDomainId <++> scKindId)
      <|> (scToken DOMAIN <++> scDomainId <++> scOptional (scToken (CHAR ':') <++> scKindId))

-- lex type ids
scTypes :: ScRE
scTypes = (scToken STRUCT <++> scTypeId)
      <|> (scToken TYPE <++> scTypeId)

-- return type ids
scRetType :: ScRE
scRetType = (scOptional scSecType) <++> scDataType <++> (scOptional scDimType) <++> scRetTypeVar

scRetTypeVar :: ScRE
scRetTypeVar = (scProcedureId <++> (scBraces scProcedureTypeArgs))
               <|> (scVarId <++> (scToken (CHAR '=') <|> scToken (CHAR ',') <|> scToken (CHAR ';')))
               <|> (scToken OPERATOR)

scProcedureTypeArgs :: ScRE
scProcedureTypeArgs = scSepBy scTyArg (scToken (CHAR ','))

scTyArg :: ScRE
scTyArg = scDataType <++> scVarId

-- types in cast expressions
--scCastExprType :: ScRE
--scCastExprType = scBraces scTypeId

scSecType :: ScRE
scSecType = scToken PUBLIC <|> scDomainId

scDataType :: ScRE
scDataType = scPrimType
         <|> scTemplateStructType
         <|> scTypeId

scTemplateStructType :: ScRE
scTemplateStructType = scTypeId <++> scABrackets scTemplateTypeArgs
    where
    scTemplateTypeArgs = scSepBy scTemplateTypeArg (scToken (CHAR ','))
    scTemplateTypeArg = scTemplateArgId
                    <|> scPrimType
                    <|> scIntLit
                    <|> scToken PUBLIC 
--                    <|> scTemplateStructType -- TODO: make this recursive

scPrimType :: ScRE
scPrimType = scTokenPred isPrimitiveTypeToken

scDimType :: ScRE
scDimType = scBrackets $ scBrackets (scIntLit <|> scVarId)

scIntLit :: ScRE
scIntLit = scTokenPred isIntToken

scProcedures :: ScRE
scProcedures = scProcedureId <++> scToken (CHAR '(') -- procedure call

scBraces :: ScRE -> ScRE
scBraces r = scToken (CHAR '(') <++> r <++> scToken (CHAR ')')

scABrackets :: ScRE -> ScRE
scABrackets r = scToken (CHAR '<') <++> r <++> scToken (CHAR '>')

scBrackets :: ScRE -> ScRE
scBrackets r = scToken (CHAR '[') <++> r <++> scToken (CHAR ']')

-- * Rewrite rules

type Rule = [TokenInfo] -> Maybe [TokenInfo]

oneOrMoreR :: Rule -> Rule
oneOrMoreR r input = case r input of
    Nothing -> Nothing
    Just output -> zeroOrMoreR r output

zeroOrMoreR :: Rule -> Rule
zeroOrMoreR r input = case (oneOrMoreR r) input of
    Nothing -> Just input
    Just output -> Just output

-- alternative rule application
oneOfR :: [Rule] -> Rule
oneOfR [] input = Nothing
oneOfR [r] input = r input
oneOfR (r:rs) input = case r input of
    Nothing -> oneOfR rs input
    Just output -> Just output

-- regular expression application
screR :: ScRE -> Rule
screR re input = case findFirstInfix re input of
    Just (pre,x,pos) -> Just (pre ++ x ++ pos)
    Nothing -> Nothing

-- * Top-level identifier lexer

runIdLexer :: MonadError SecrecError m => String -> [TokenInfo] -> m [TokenInfo]
runIdLexer fn input = case idLexer input of
    Just output -> return output
    Nothing -> return input

idLexer :: Rule
idLexer = zeroOrMoreR $ oneOfR [screR scModules,screR scKinds,screR scTypes,screR scRetType,screR scProcedures,{-screR scCastExprType,-}screR scVarId]
