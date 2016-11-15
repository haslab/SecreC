{

{-# LANGUAGE MultiParamTypeClasses #-}

module Language.SecreC.Parser.Lexer where

import Control.Monad.Except
import Control.Monad.State

import Language.SecreC.Parser.Tokens
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Error

import Text.PrettyPrint

}

%wrapper "monadUserState"

-- Character classes

$binarydigit     = [0-1]
$octaldigit      = [0-7]
$digit           = [0-9]
$hexdigit        = [0-9a-fA-F]
$underscore      = _
$whitespace      = [ \t]
$uppercase       = [A-Z]
$lowercase       = [a-z]
$simpleop        = [\.\-\,\;\:\!\?\/\^\~\(\)\[\]\{\}\*\&\%\+\<\=\>\|]

@newline         = (\n\r|\r\n|\n|\r)
@letter          = ($uppercase|$lowercase)
@nondigit        = ($uppercase|$lowercase|$underscore)
@decimal         = 0|[1-9]$digit*
@exponent        = (e|E)[\+\-]?@decimal
@identifier      = @nondigit(@nondigit|$digit)*
@binarylit       = 0b$binarydigit+
@octallit        = 0o$octaldigit+
@hexlit          = 0x$hexdigit+
@simplefloat     = @decimal@exponent
@scientificfloat = @decimal\.$digit*@exponent?

tokens :-


<0>       "//".*                                { lineComment }
<0>       "#".*                                 ;
<0>       \/\*                                  { enterNewComment }
<comment> \/\*                                  { embedComment    }
<comment> \*\/                                  { unembedComment  }
<comment> @newline                              { bufferComment }
<comment> .                                     { bufferComment }

<0>       $white+           ;
                        
-- String literals:   
<0>                     \"                      { enterStateString }
<state_string>          \"                      { leaveStateString }
<state_string>          \$                      { enterStateStringVariable }
<state_string>          \\n                     { bufferChar (const '\n') }
<state_string>          \\t                     { bufferChar (const '\t') }
<state_string>          \\r                     { bufferChar (const '\r') }
<state_string>          \\\.                    { bufferChar (!!1) }
<state_string>          .                       { bufferChar (!!0) }

-- String identifier:
<state_string_variable> @identifier             { leaveStateStringVariable }

-- Keywords:
<0>                     nonpublic               { lexerTokenInfo NONPUBLIC }
<0>                     readonly                { lexerTokenInfo READONLY }
<0>                     readwrite               { lexerTokenInfo READWRITE }
<0>                     pure                    { lexerTokenInfo PURE }
<0>                     context                 { lexerTokenInfo CONTEXT }
<0>                     numeric                 { lexerTokenInfo NUMERIC }
<0>                     primitive               { lexerTokenInfo PRIMITIVE }
<0>                     function                { lexerTokenInfo FUNCTION }
<0>                     havoc                   { lexerTokenInfo HAVOC }
<0>                     \\result                { lexerAnnTokenInfo RESULT }
<0>                     forall                  { lexerAnnTokenInfo FORALL }
<0>                     exists                  { lexerAnnTokenInfo EXISTS }
<0>                     assert                  { lexerTokenInfo ASSERT }
<0>                     const                   { lexerTokenInfo CONST }
<0>                     bool                    { lexerTokenInfo BOOL }
<0>                     break                   { lexerTokenInfo BREAK }
<0>                     continue                { lexerTokenInfo CONTINUE }
<0>                     dim                     { lexerTokenInfo DIMENSIONALITY }
<0>                     do                      { lexerTokenInfo DO }
<0>                     domain                  { lexerTokenInfo DOMAIN }
<0>                     else                    { lexerTokenInfo ELSE }
<0>                     false                   { lexerTokenInfo FALSE_B }
<0>                     float                   { lexerTokenInfo FLOAT }
<0>                     float32                 { lexerTokenInfo FLOAT32 }
<0>                     float64                 { lexerTokenInfo FLOAT64 }
<0>                     for                     { lexerTokenInfo FOR }
<0>                     if                      { lexerTokenInfo IF }
<0>                     import                  { lexerTokenInfo IMPORT }
<0>                     int                     { lexerTokenInfo INT }
<0>                     int16                   { lexerTokenInfo INT16 }
<0>                     int32                   { lexerTokenInfo INT32 }
<0>                     int64                   { lexerTokenInfo INT64 }
<0>                     int8                    { lexerTokenInfo INT8 }
<0>                     kind                    { lexerTokenInfo KIND }
<0>                     module                  { lexerTokenInfo MODULE }
<0>                     operator                { lexerTokenInfo OPERATOR }
<0>                     print                   { lexerTokenInfo PRINT }
<0>                     public                  { lexerTokenInfo PUBLIC }
<0>                     return                  { lexerTokenInfo RETURN }
<0>                     string                  { lexerTokenInfo STRING }
<0>                     struct                  { lexerTokenInfo STRUCT }
<0>                     template                { lexerTokenInfo TEMPLATE }
<0>                     true                    { lexerTokenInfo TRUE_B }
<0>                     type                    { lexerTokenInfo TYPE }
<0>                     uint                    { lexerTokenInfo UINT }
<0>                     uint16                  { lexerTokenInfo UINT16 }
<0>                     uint32                  { lexerTokenInfo UINT32 }
<0>                     uint64                  { lexerTokenInfo UINT64 }
<0>                     uint8                   { lexerTokenInfo UINT8 }
<0>                     void                    { lexerTokenInfo VOID }
<0>                     while                   { lexerTokenInfo WHILE }
<0>                     xor_uint                { lexerTokenInfo XOR_UINT }
<0>                     xor_uint16              { lexerTokenInfo XOR_UINT16 }
<0>                     xor_uint32              { lexerTokenInfo XOR_UINT32 }
<0>                     xor_uint64              { lexerTokenInfo XOR_UINT64 }
<0>                     xor_uint8               { lexerTokenInfo XOR_UINT8 }
<0>                     requires                { lexerTokenInfo REQUIRES }
<0>                     ensures                 { lexerAnnTokenInfo ENSURES }
<0>                     multiset                { lexerAnnTokenInfo MULTISET }
<0>                     set                     { lexerAnnTokenInfo SET }
<0>                     free                    { lexerAnnTokenInfo FREE }
<0>                     assume                  { lexerAnnTokenInfo ASSUME }
<0>                     leakage                 { lexerAnnTokenInfo LEAKAGE }
<0>                     axiom                   { lexerAnnTokenInfo AXIOM }
<0>                     lemma                   { lexerAnnTokenInfo LEMMA }
<0>                     invariant               { lexerAnnTokenInfo INVARIANT }
<0>                     inline                  { lexerAnnTokenInfo INLINE }
<0>                     noinline                { lexerAnnTokenInfo NOINLINE }
<0>                     decreases               { lexerAnnTokenInfo DECREASES }

-- built-in functions:
<0>                     "size..."               { lexerTokenInfo VSIZE }
<0>                     __bytes_from_string     { lexerTokenInfo BYTESFROMSTRING }
<0>                     __cref                  { lexerTokenInfo CREF }
<0>                     __domainid              { lexerTokenInfo DOMAINID }
<0>                     __ref                   { lexerTokenInfo REF }
<0>                     __string_from_bytes     { lexerTokenInfo STRINGFROMBYTES }
<0>                     __return                { lexerTokenInfo SYSCALL_RETURN }
<0>                     __syscall               { lexerTokenInfo SYSCALL }
<0>                     __builtin               { lexerTokenInfo BUILTIN }

<0>                     @identifier             { lexerTokenInfoFunc (return . IDENTIFIER) }
<0>                     @binarylit              { lexerTokenInfoFunc (return . BIN_LITERAL . convert_to_base 2) }
<0>                     @octallit               { lexerTokenInfoFunc (return . OCT_LITERAL . convert_to_base 8) }
<0>                     @hexlit                 { lexerTokenInfoFunc (return . HEX_LITERAL . convert_to_base 16) }
<0>                     @simplefloat            { lexerTokenInfoFunc (return . FLOAT_LITERAL . readFloat) }
<0>                     @scientificfloat        { lexerTokenInfoFunc (return . FLOAT_LITERAL . readFloat) }
<0>                     @decimal                { lexerTokenInfoFunc (return . DEC_LITERAL . convert_to_base 10) }

<0>                     ==\>                    { lexerTokenInfo IMPLIES_OP }
<0>                     \<==\>                  { lexerTokenInfo EQUIV_OP }
<0>                     "..."                   { lexerTokenInfo VARIADIC }
<0>                     \<\~                    { lexerTokenInfo COERCE }
<0>                     \+=                     { lexerTokenInfo ADD_ASSIGN }
<0>                     &=                      { lexerTokenInfo AND_ASSIGN }
<0>                     \-\-                    { lexerTokenInfo DEC_OP }
<0>                     \/=                     { lexerTokenInfo DIV_ASSIGN }
<0>                     ==                      { lexerTokenInfo EQ_OP }
<0>                     >=                      { lexerTokenInfo GE_OP }
<0>                     \+\+                    { lexerTokenInfo INC_OP }
<0>                     &&                      { lexerTokenInfo LAND_OP }
<0>                     \<=                     { lexerTokenInfo LE_OP }
<0>                     \|\|                    { lexerTokenInfo LOR_OP }
<0>                     >>                      { lexerTokenInfo SHR_OP }
<0>                     \<\<                    { lexerTokenInfo SHL_OP }
<0>                     \%=                     { lexerTokenInfo MOD_ASSIGN }
<0>                     \*=                     { lexerTokenInfo MUL_ASSIGN }
<0>                     !=                      { lexerTokenInfo NE_OP }
<0>                     \|=                     { lexerTokenInfo OR_ASSIGN }
<0>                     \-=                     { lexerTokenInfo SUB_ASSIGN }
<0>                     ::                      { lexerTokenInfo TYPE_QUAL }
<0>                     ^=                      { lexerTokenInfo XOR_ASSIGN }

<0>                     $simpleop               { simpleOp }
<0>                     @newline                { skip }
<0>                     $whitespace             { skip }

<0>                     .                       { lexerTokenInfoFunc handleError     }

{

-- Token Functions -------------------------------------------------------------

lexerAnnTokenInfo :: Token -> AlexInput -> Int -> Alex TokenInfo
lexerAnnTokenInfo t inp l = do
    aus <- get
    if lexAnn aus
        then lexerTokenInfo t inp l
        else lexerTokenInfoFunc (return . IDENTIFIER) inp l

lexerTokenInfo :: Token -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfo t (AlexPn a ln c, _, _, s) l = do
    fn <- alexFilename
    return $ TokenInfo t (take l $ s) (pos fn ln c a)

lexerTokenInfoFunc :: (String -> Alex Token) -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfoFunc f (AlexPn a ln c, _, _, s) l = do 
    r <- f (take (fromIntegral l) s)
    fn <- alexFilename
    return $ TokenInfo r (take (fromIntegral l) s) (pos fn ln c a)

simpleOp :: AlexInput -> Int -> Alex TokenInfo
simpleOp input len = lexerTokenInfoFunc (return . CHAR . head) input len

handleError :: String -> Alex Token
handleError _ = return TokenError

bufferChar :: (String -> Char) -> AlexInput -> Int -> Alex TokenInfo
bufferChar f input@(AlexPn a ln c, _, _, s) len = do
    modify (\ aus -> aus { stateString = stateString aus ++ [f (take len s)] } )
    skip input len

enterStateString :: AlexInput -> Int -> Alex TokenInfo
enterStateString input len = do
    modify (\ aus -> aus { stateString = "" } )
    alexSetStartCode state_string
    skip input len
    
enterStateStringVariable :: AlexInput -> Int -> Alex TokenInfo
enterStateStringVariable input len = do
    alexSetStartCode state_string_variable
    saveStateString input len

leaveStateString :: AlexInput -> Int -> Alex TokenInfo
leaveStateString i n = do
    alexSetStartCode 0
    saveStateString i n
    
saveStateString :: AlexInput -> Int -> Alex TokenInfo
saveStateString input len = do
    aus <- get
    modify (\ aus -> aus { stateString = "" } )
    lexerTokenInfo (STR_FRAGMENT $ stateString aus) input len

leaveStateStringVariable :: AlexInput -> Int -> Alex TokenInfo
leaveStateStringVariable input len = do
    aus <- get
    alexSetStartCode state_string
    lexerTokenInfo (STR_IDENTIFIER $ stateString aus) input len

enterNewComment :: AlexInput -> Int -> Alex TokenInfo
enterNewComment input len = do
    modify (\ aus -> aus { commentDepth = 1, commentStr = "" })
    alexSetStartCode comment
    skip input len

bufferComment :: AlexInput -> Int -> Alex TokenInfo
bufferComment input@(AlexPn a ln c, _, _, s) len = do
    modify (\ aus -> aus { commentStr = commentStr aus ++ (take len s) } )
    skip input len

embedComment :: AlexInput -> Int -> Alex TokenInfo
embedComment input len = do
    modify (\ aus -> aus { commentDepth = commentDepth aus + 1 })
    skip input len

unembedComment :: AlexInput -> Int -> Alex TokenInfo
unembedComment input len = do
    aus <- get
    let cd = commentDepth aus
    put (aus { commentDepth = cd - 1 })
    if (cd == 1)
        then do
            alexSetStartCode 0
            case isAnnotation (commentStr aus) of
                Nothing -> skip input len
                Just ann -> do
                    aus <- get
                    modify (\aus -> aus { commentStr = "" })
                    lexerTokenInfo (ANNOTATION ann) input len
        else do
            skip input len

lineComment :: AlexInput -> Int -> Alex TokenInfo
lineComment input@(AlexPn a ln c, _, _, s) len = do
    let com = drop 2 $ take len s
    case isAnnotation com of
        Nothing -> skip input len
        Just ann -> lexerTokenInfo (ANNOTATION ann) input len

-- Alex Functions --------------------------------------------------------------

data AlexUserState = AlexUserState 
    { filename     :: !String
    , types        :: [String]
    , commentDepth :: Integer
    , stateString  :: String
    , commentStr   :: String
    , lexAnn       :: Bool -- lex tokens in the annotation language or not
    }

alexFilename :: Alex String
alexFilename = liftM filename get

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "" [] 0 "" [] False

instance MonadState AlexUserState Alex where
    get = alexGetUserState
    put = alexSetUserState

instance MonadError SecrecError Alex where
    throwError e = Alex $ \ s -> Left (show e)
    catchError (Alex un) f = Alex $ \ s -> either (catchMe s) Right (un s)
        where 
        catchMe s x = fmap (split (const s) id) $ runAlex "" $ f $ GenericError (UnhelpfulPos "lexer") (text x) Nothing

{-# INLINE split #-}
split :: (a -> b) -> (a -> c) -> a -> (b, c)
split f g a = (f a, g a)

alexEOF :: Alex TokenInfo
alexEOF = do 
    (AlexPn a ln c, _, _, _) <- alexGetInput
    fn <- alexFilename
    return $ TokenInfo TokenEOF "<EOF>" (pos fn ln c a)


-- Processing Functions --------------------------------------------------------

positionToAlexPos :: Position -> AlexPosn
positionToAlexPos (Pos fn l c a) = AlexPn a l c

alexSetPos :: AlexPosn -> Alex ()
alexSetPos p = do
    (_,x,y,z) <- alexGetInput
    alexSetInput (p,x,y,z)

runLexerWith :: Bool -> String -> String -> AlexPosn -> ([TokenInfo] -> Alex a) -> Either String a
runLexerWith isAnn fn str pos parse = runAlex str $ do
    alexSetPos pos
    put (alexInitUserState { filename = fn, lexAnn = isAnn })
    toks <- getTokens
    parse toks

runLexer :: Bool -> String -> String -> Either String [TokenInfo]
runLexer isAnn fn str = runLexerWith isAnn fn str alexStartPos return

injectResult :: Either String a -> Alex a
injectResult (Left err) = throwError (GenericError (UnhelpfulPos "inject") (text err) Nothing)
injectResult (Right a) = return a

-- | Alex lexer
lexer :: (TokenInfo -> Alex a) -> Alex a
lexer cont = alexMonadScan >>= cont

getTokens :: Alex [TokenInfo]
getTokens = do 
    tok <- alexMonadScan
    case tSymb tok of
        TokenEOF -> return [tok]
        _ -> liftM (tok:) getTokens

flushLexer :: Alex ()
flushLexer = return ()


}