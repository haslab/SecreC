{-# LANGUAGE TypeFamilies, DeriveDataTypeable, ScopedTypeVariables, MultiParamTypeClasses #-}

module Language.SecreC.Parser.Tokens where

import Safe

import Data.Generics
import Text.PrettyPrint

import Data.Digits (digits, unDigits)

import Language.SecreC.Pretty
import Language.SecreC.Position
import Language.SecreC.Location

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
 
instance PP TokenInfo where
    pp = pp . tSymb
 
data Token 
    = STR_IDENTIFIER String
    | STR_FRAGMENT String
    | CHAR Char
    | ASSERT
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
    | VARRAY
    | TokenEOF
    | TokenError
  deriving (Show,Read,Data,Typeable,Eq,Ord)

instance PP Token where
    pp (STR_FRAGMENT s) = text s
    pp (CONST) = text "const"
    pp (STR_IDENTIFIER s) = text s
    pp (CHAR c) = char c
    pp ASSERT = text "assert"
    pp BOOL = text "bool"
    pp BREAK = text "break"
    pp CONTINUE = text "continue"
    pp DIMENSIONALITY = text " =dim"
    pp DO = text "do"
    pp DOMAIN = text "domain"
    pp ELSE = text "else"
    pp FALSE_B = text "false"
    pp FLOAT = text "float"
    pp FLOAT32 = text "float32"
    pp FLOAT64 = text "float64"
    pp FOR = text "for"
    pp IF = text "if"
    pp IMPORT = text "import"
    pp INT = text "int"
    pp INT16 = text "int16"
    pp INT32 = text "int32"
    pp INT64 = text "int64"
    pp INT8 = text "int8"
    pp KIND = text "kind"
    pp MODULE = text "module"
    pp OPERATOR = text "operator"
    pp PRINT = text "print"
    pp PUBLIC = text "public"
    pp RETURN = text "return"
    pp STRING = text "string"
    pp STRUCT = text "struct"
    pp TEMPLATE = text "template"
    pp TRUE_B = text "true"
    pp TYPE = text "type"
    pp UINT = text "uint"
    pp UINT16 = text "uint16"
    pp UINT32 = text "uint32"
    pp UINT64 = text "uint64"
    pp UINT8 = text "uint8"
    pp VOID = text "void"
    pp WHILE = text "while"
    pp XOR_UINT = text "xor_uint"
    pp XOR_UINT16 = text "xor_uint16"
    pp XOR_UINT32 = text "xor_uint32"
    pp XOR_UINT64 = text "xor_uint64"
    pp XOR_UINT8 = text "xor_uint8"
    pp BYTESFROMSTRING = text "__bytes_from_string"
    pp CREF = text "__cref"
    pp DOMAINID = text "__domainid"
    pp REF = text "__ref"
    pp STRINGFROMBYTES = text "__string_from_bytes"
    pp SYSCALL_RETURN = text "__return"
    pp SYSCALL = text "__syscall"
    pp (IDENTIFIER s) = text s
    pp (BIN_LITERAL i) = text (convert_from_base 2 i)
    pp (OCT_LITERAL i) = text (convert_from_base 8 i)
    pp (HEX_LITERAL i) = text (convert_from_base 1 i)
    pp (FLOAT_LITERAL i) = text (show i)
    pp (DEC_LITERAL i) = text (convert_from_base 10 i)
    pp ADD_ASSIGN = text "+="
    pp AND_ASSIGN = text "&="
    pp DEC_OP = text "--"
    pp DIV_ASSIGN = text "/="
    pp EQ_OP = text "=="
    pp GE_OP = text ">="
    pp INC_OP = text "++"
    pp LAND_OP = text "&&"
    pp LE_OP = text "<="
    pp LOR_OP = text "||"
    pp SHR_OP = text ">>"
    pp SHL_OP = text "<<"
    pp MOD_ASSIGN = text "%="
    pp MUL_ASSIGN = text "*="
    pp NE_OP = text "!="
    pp OR_ASSIGN = text "|="
    pp SUB_ASSIGN = text "-="
    pp TYPE_QUAL = text "::"
    pp XOR_ASSIGN = text "^="
    pp VARIADIC = text "..."
    pp VSIZE = text "size..."
    pp VARRAY = text "varray"
    pp TokenEOF = text "<EOF>"
    pp TokenError = text "error <unknown>"

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


