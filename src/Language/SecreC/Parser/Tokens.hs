{-# LANGUAGE FlexibleInstances, TypeFamilies, DeriveDataTypeable, ScopedTypeVariables, MultiParamTypeClasses #-}

module Language.SecreC.Parser.Tokens where

import Safe

import Data.Generics
import Text.PrettyPrint

import Data.Digits (digits, unDigits)
import Data.List as List

import Language.SecreC.Pretty
import Language.SecreC.Position
import Language.SecreC.Location

import Control.Monad

data TokenInfo
    = TokenInfo 
        { tSymb :: Token
        , tText :: !String
        , tLoc  :: Position
        }
  deriving (Show,Read,Data,Typeable)

instance Eq TokenInfo where
    x == y = tSymb x == tSymb y
instance Ord TokenInfo where
    compare x y = compare (tSymb x) (tSymb y)

instance Located TokenInfo where
    type LocOf TokenInfo = Position
    loc = tLoc
    updLoc t l = t { tLoc = l }
 
instance Monad m => PP m TokenInfo where
    pp = pp . tSymb
 
data Token 
    = STR_IDENTIFIER String
    | STR_FRAGMENT String
    | CHAR Char
    | PURE
    | READONLY
    | READWRITE
    | COERCE
    | ASSERT
    | LEMMA
    | CONST
    | BOOL
    | BREAK
    | CONTINUE 
    | DIMENSIONALITY
    | DO
    | DOMAIN
    | ELSE
    | FALSE_B
    | FLOAT
    | FLOAT32
    | FLOAT64
    | FOR
    | CONTEXT
    | IF
    | IMPORT
    | INT
    | INT16
    | INT32
    | INT64
    | INT8
    | KIND
    | MODULE
    | OPERATOR
    | PRINT
    | PUBLIC
    | RETURN
    | STRING
    | STRUCT
    | TEMPLATE
    | TRUE_B
    | TYPE
    | UINT
    | UINT16
    | UINT32
    | UINT64
    | UINT8
    | VOID
    | WHILE
    | XOR_UINT
    | XOR_UINT16
    | XOR_UINT32
    | XOR_UINT64
    | XOR_UINT8
    | BYTESFROMSTRING
    | CREF
    | DOMAINID
    | REF
    | STRINGFROMBYTES
    | SYSCALL_RETURN
    | SYSCALL
    | BUILTIN
    | IDENTIFIER String
    | BIN_LITERAL Integer
    | OCT_LITERAL Integer
    | HEX_LITERAL Integer
    | FLOAT_LITERAL Double
    | DEC_LITERAL Integer
    | ADD_ASSIGN
    | AND_ASSIGN
    | DEC_OP
    | DIV_ASSIGN
    | EQ_OP
    | SEQ_OP
    | GE_OP
    | INC_OP
    | LAND_OP
    | LE_OP
    | LOR_OP
    | SHR_OP
    | SHL_OP
    | MOD_ASSIGN
    | MUL_ASSIGN
    | NE_OP
    | OR_ASSIGN
    | SUB_ASSIGN
    | TYPE_QUAL
    | XOR_ASSIGN
    | VARIADIC
    | VSIZE
    | REQUIRES
    | ENSURES
    | ASSUME
    | LEAKAGE
    | DECREASES
    | INVARIANT
    | TokenEOF
    | TokenError
    | RESULT
    | FORALL
    | EXISTS
    | NONPUBLIC
    | PRIMITIVE
    | NUMERIC
    | IMPLIES_OP
    | EQUIV_OP
    | MULTISET
    | SET
    | FREE
    | ANNOTATION [String]
    | FUNCTION
    | PREDICATE
    | AXIOM
    | HAVOC
    | INLINE
    | NOINLINE
  deriving (Show,Read,Data,Typeable,Eq,Ord)

instance Monad m => PP m Token where
    pp COERCE           =       return $ text "<~"
    pp (STR_FRAGMENT s) =       return $ text s
    pp (CONST) =                return $ text "const"
    pp (STR_IDENTIFIER s) =     return $ text s
    pp NONPUBLIC =              return $ text "nonpublic"
    pp NUMERIC =                return $ text "numeric"
    pp CONTEXT =                return $ text "context"
    pp PRIMITIVE =              return $ text "primitive"
    pp (CHAR c) =               return $ char c
    pp ASSERT =                 return $ text "assert"
    pp BOOL =                   return $ text "bool"
    pp BREAK =                  return $ text "break"
    pp CONTINUE =               return $ text "continue"
    pp DIMENSIONALITY =         return $ text " =dim"
    pp DO =                     return $ text "do"
    pp DOMAIN =                 return $ text "domain"
    pp ELSE =                   return $ text "else"
    pp FALSE_B =                return $ text "false"
    pp FLOAT =                  return $ text "float"
    pp FLOAT32 =                return $ text "float32"
    pp FLOAT64 =                return $ text "float64"
    pp FOR =                    return $ text "for"
    pp IF =                     return $ text "if"
    pp IMPORT =                 return $ text "import"
    pp INT =                    return $ text "int"
    pp INT16 =                  return $ text "int16"
    pp INT32 =                  return $ text "int32"
    pp INT64 =                  return $ text "int64"
    pp INT8 =                   return $ text "int8"
    pp KIND =                   return $ text "kind"
    pp MODULE =                 return $ text "module"
    pp OPERATOR =               return $ text "operator"
    pp PRINT =                  return $ text "print"
    pp PUBLIC =                 return $ text "public"
    pp RETURN =                 return $ text "return"
    pp STRING =                 return $ text "string"
    pp STRUCT =                 return $ text "struct"
    pp TEMPLATE =               return $ text "template"
    pp TRUE_B =                 return $ text "true"
    pp TYPE =                   return $ text "type"
    pp UINT =                   return $ text "uint"
    pp UINT16 =                 return $ text "uint16"
    pp UINT32 =                 return $ text "uint32"
    pp UINT64 =                 return $ text "uint64"
    pp UINT8 =                  return $ text "uint8"
    pp VOID =                   return $ text "void"
    pp WHILE =                  return $ text "while"
    pp XOR_UINT =               return $ text "xor_uint"
    pp XOR_UINT16 =             return $ text "xor_uint16"
    pp XOR_UINT32 =             return $ text "xor_uint32"
    pp XOR_UINT64 =             return $ text "xor_uint64"
    pp XOR_UINT8 =              return $ text "xor_uint8"
    pp BYTESFROMSTRING =        return $ text "__bytes_from_string"
    pp CREF =                   return $ text "__cref"
    pp DOMAINID =               return $ text "__domainid"
    pp REF =                    return $ text "__ref"
    pp STRINGFROMBYTES =        return $ text "__string_from_bytes"
    pp SYSCALL_RETURN =         return $ text "__return"
    pp SYSCALL =                return $ text "__syscall"
    pp BUILTIN =                return $ text "__builtin"
    pp (IDENTIFIER s) =         return $ text s
    pp (BIN_LITERAL i) =        return $ text (convert_from_base 2 i)
    pp (OCT_LITERAL i) =        return $ text (convert_from_base 8 i)
    pp (HEX_LITERAL i) =        return $ text (convert_from_base 1 i)
    pp (FLOAT_LITERAL i) =      return $ text (show i)
    pp (DEC_LITERAL i) =        return $ text (convert_from_base 10 i)
    pp ADD_ASSIGN =             return $ text "+="
    pp AND_ASSIGN =             return $ text "&="
    pp DEC_OP =                 return $ text "--"
    pp DIV_ASSIGN =             return $ text "/="
    pp EQ_OP =                  return $ text "=="
    pp SEQ_OP =                 return $ text "==="
    pp GE_OP =                  return $ text ">="
    pp INC_OP =                 return $ text "++"
    pp LAND_OP =                return $ text "&&"
    pp LE_OP =                  return $ text "<="
    pp LOR_OP =                 return $ text "||"
    pp SHR_OP =                 return $ text ">>"
    pp SHL_OP =                 return $ text "<<"
    pp IMPLIES_OP =             return $ text "==>"
    pp EQUIV_OP =               return $ text "<==>"
    pp MOD_ASSIGN =             return $ text "%="
    pp MUL_ASSIGN =             return $ text "*="
    pp NE_OP =                  return $ text "!="
    pp OR_ASSIGN =              return $ text "|="
    pp SUB_ASSIGN =             return $ text "-="
    pp TYPE_QUAL =              return $ text "::"
    pp XOR_ASSIGN =             return $ text "^="
    pp VARIADIC =               return $ text "..."
    pp VSIZE =                  return $ text "size..."
    pp REQUIRES =               return $ text "requires"
    pp ENSURES =                return $ text "ensures"
    pp LEAKAGE =                return $ text "leakage"
    pp DECREASES =              return $ text "decreases"
    pp INVARIANT =              return $ text "invariant"
    pp ASSUME =                 return $ text "assume"
    pp TokenEOF =               return $ text "<EOF>"
    pp TokenError =             return $ text "error <unknown>"
    pp RESULT =                 return $ text "\\result"
    pp FORALL =                 return $ text "forall"
    pp EXISTS =                 return $ text "exists"
    pp MULTISET =               return $ text "multiset"
    pp PREDICATE =              return $ text "predicate"
    pp SET =                    return $ text "set"
    pp FREE =                   return $ text "free"
    pp FUNCTION =               return $ text "function"
    pp AXIOM =                  return $ text "axiom"
    pp HAVOC =                  return $ text "HAVOC"
    pp INLINE =                 return $ text "inline"
    pp NOINLINE =               return $ text "noinline"
    pp LEMMA =                  return $ text "lemma"
    pp PURE =                   return $ text "pure"
    pp READONLY =               return $ text "readonly"
    pp READWRITE =              return $ text "readwrite"
    pp (ANNOTATION anns) =      return $ text "/*" <+> vcat (map (\ann -> text "@" <> text ann) anns) <+> text "*/"

isAnnotation :: String -> Maybe [String]
isAnnotation s = if ok then Just (map (takeWhile (/='@') . tail . dropWhile (/='@')) toks) else Nothing
    where
    toks = lines s
    ok = not (List.null toks) && and (map (maybe False (=="@") . headMay . words) toks)

isIntToken :: Token -> Bool
isIntToken (BIN_LITERAL i) = True
isIntToken (OCT_LITERAL i) = True
isIntToken (HEX_LITERAL i) = True
isIntToken (DEC_LITERAL i) = True
isIntToken _ = False

convertBase :: Integral a => a -> a -> [a] -> [a]
convertBase from to = digits to . unDigits from

convert_to_base :: Int -> String -> Integer
convert_to_base base input = unDigits (toEnum base) $ convertBase 10 (toEnum base) $ digits 10 $ readInteger input

convert_from_base :: Int -> Integer -> String
convert_from_base base input = concatMap show ds10
    where
    dsBase :: [Integer] = digits (toEnum base) input
    ds10 :: [Integer] = convertBase (toEnum base) 10 dsBase
    
isPrimitiveTypeToken :: Token -> Bool
isPrimitiveTypeToken BOOL       = True
isPrimitiveTypeToken INT        = True
isPrimitiveTypeToken UINT       = True
isPrimitiveTypeToken INT8       = True
isPrimitiveTypeToken UINT8      = True
isPrimitiveTypeToken INT16      = True
isPrimitiveTypeToken UINT16     = True
isPrimitiveTypeToken INT32      = True
isPrimitiveTypeToken UINT32     = True
isPrimitiveTypeToken INT64      = True
isPrimitiveTypeToken UINT64     = True
isPrimitiveTypeToken STRING     = True
isPrimitiveTypeToken XOR_UINT8  = True
isPrimitiveTypeToken XOR_UINT16 = True
isPrimitiveTypeToken XOR_UINT32 = True
isPrimitiveTypeToken XOR_UINT64 = True
isPrimitiveTypeToken XOR_UINT   = True
isPrimitiveTypeToken FLOAT      = True
isPrimitiveTypeToken FLOAT32    = True
isPrimitiveTypeToken FLOAT64    = True
isPrimitiveTypeToken _          = False

tokenString :: TokenInfo -> String
tokenString (TokenInfo (STR_FRAGMENT s) _ _) = s
tokenString (TokenInfo (STR_IDENTIFIER s) _ _) = s
tokenString (TokenInfo (IDENTIFIER s) _ _) = s

tokenInteger :: TokenInfo -> Integer
tokenInteger (TokenInfo (BIN_LITERAL i) _ _) = i
tokenInteger (TokenInfo (OCT_LITERAL i) _ _) = i
tokenInteger (TokenInfo (DEC_LITERAL i) _ _) = i
tokenInteger (TokenInfo (HEX_LITERAL i) _ _) = i

tokenBool :: TokenInfo -> Bool
tokenBool (TokenInfo TRUE_B _ _) = True
tokenBool (TokenInfo FALSE_B _ _) = False

tokenFloat :: TokenInfo -> Double
tokenFloat (TokenInfo (FLOAT_LITERAL f) _ _) = f

readFloat :: String -> Double
readFloat = readNote "read Float"

readInteger :: String -> Integer
readInteger = readNote "read Integer"


