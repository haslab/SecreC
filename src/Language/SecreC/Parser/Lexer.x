{

{-# LANGUAGE MultiParamTypeClasses #-}

module Language.SecreC.Parser.Lexer where

import Control.Monad.Except
import Control.Monad.State

import Language.SecreC.Parser.Tokens
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.Parser.IdLexer

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


<0>       "//".*            ;
<0>       \/\*              { enterNewComment }
<comment> \/\*              { embedComment    }
<comment> \*\/              { unembedComment  }

<0>       $white+           ;
                        
-- String literals:   
<0>                     \"                      { enterStateString }
<state_string>          \"                      { saveStateString }
<state_string>          \$                      { enterStateStringVariable }
<state_string>          \\n                     { bufferChar (const '\n') }
<state_string>          \\t                     { bufferChar (const '\t') }
<state_string>          \\r                     { bufferChar (const '\r') }
<state_string>          \\.                     { bufferChar (!!1) }
<state_string>          .                       { bufferChar (!!0) }

-- String identifier:
<state_string_variable> @identifier             { leaveStateStringVariable }

-- Keywords:
<0>                     assert                { lexerTokenInfo ASSERT }
<0>                     bool                  { lexerTokenInfo BOOL }
<0>                     break                 { lexerTokenInfo BREAK }
<0>                     cat                   { lexerTokenInfo CAT }
<0>                     continue              { lexerTokenInfo CONTINUE }
<0>                     declassify            { lexerTokenInfo DECLASSIFY }
<0>                     dim                   { lexerTokenInfo DIMENSIONALITY }
<0>                     do                    { lexerTokenInfo DO }
<0>                     domain                { lexerTokenInfo DOMAIN }
<0>                     else                  { lexerTokenInfo ELSE }
<0>                     false                 { lexerTokenInfo FALSE_B }
<0>                     float                 { lexerTokenInfo FLOAT }
<0>                     float32               { lexerTokenInfo FLOAT32 }
<0>                     float64               { lexerTokenInfo FLOAT64 }
<0>                     for                   { lexerTokenInfo FOR }
<0>                     if                   { lexerTokenInfo IF }
<0>                     import                { lexerTokenInfo IMPORT }
<0>                     int                   { lexerTokenInfo INT }
<0>                     int16                 { lexerTokenInfo INT16 }
<0>                     int32                 { lexerTokenInfo INT32 }
<0>                     int64                 { lexerTokenInfo INT64 }
<0>                     int8                  { lexerTokenInfo INT8 }
<0>                     kind                  { lexerTokenInfo KIND }
<0>                     module                { lexerTokenInfo MODULE }
<0>                     operator              { lexerTokenInfo OPERATOR }
<0>                     print                 { lexerTokenInfo PRINT }
<0>                     public                { lexerTokenInfo PUBLIC }
<0>                     reshape               { lexerTokenInfo RESHAPE }
<0>                     return                { lexerTokenInfo RETURN }
<0>                     shape                 { lexerTokenInfo SHAPE }
<0>                     size                  { lexerTokenInfo SIZE }
<0>                     string                { lexerTokenInfo STRING }
<0>                     strlen                { lexerTokenInfo STRLEN }
<0>                     struct                { lexerTokenInfo STRUCT }
<0>                     template              { lexerTokenInfo TEMPLATE }
<0>                     tostring              { lexerTokenInfo TOSTRING }
<0>                     true                  { lexerTokenInfo TRUE_B }
<0>                     type                  { lexerTokenInfo TYPE }
<0>                     uint                  { lexerTokenInfo UINT }
<0>                     uint16                { lexerTokenInfo UINT16 }
<0>                     uint32                { lexerTokenInfo UINT32 }
<0>                     uint64                { lexerTokenInfo UINT64 }
<0>                     uint8                 { lexerTokenInfo UINT8 }
<0>                     void                  { lexerTokenInfo VOID }
<0>                     while                 { lexerTokenInfo WHILE }
<0>                     xor_uint              { lexerTokenInfo XOR_UINT }
<0>                     xor_uint16            { lexerTokenInfo XOR_UINT16 }
<0>                     xor_uint32            { lexerTokenInfo XOR_UINT32 }
<0>                     xor_uint64            { lexerTokenInfo XOR_UINT64 }
<0>                     xor_uint8             { lexerTokenInfo XOR_UINT8 }

-- built-in functions:
<0>                     __bytes_from_string   { lexerTokenInfo BYTESFROMSTRING }
<0>                     __cref                { lexerTokenInfo CREF }
<0>                     __domainid            { lexerTokenInfo DOMAINID }
<0>                     __ref                 { lexerTokenInfo REF }
<0>                     __string_from_bytes   { lexerTokenInfo STRINGFROMBYTES }
<0>                     __return              { lexerTokenInfo SYSCALL_RETURN }
<0>                     __syscall             { lexerTokenInfo SYSCALL }

<0>                     @identifier             { lexerTokenInfoFunc (return . flip IDENTIFIER Nothing) }
<0>                     @binarylit              { lexerTokenInfoFunc (return . BIN_LITERAL . convert_to_base 2) }
<0>                     @octallit               { lexerTokenInfoFunc (return . OCT_LITERAL . convert_to_base 8) }
<0>                     @hexlit                 { lexerTokenInfoFunc (return . HEX_LITERAL . convert_to_base 16) }
<0>                     @simplefloat            { lexerTokenInfoFunc (return . FLOAT_LITERAL . read) }
<0>                     @scientificfloat        { lexerTokenInfoFunc (return . FLOAT_LITERAL . read) }
<0>                     @decimal                { lexerTokenInfoFunc (return . DEC_LITERAL . convert_to_base 10) }

<0>                     \+=                   { lexerTokenInfo ADD_ASSIGN }
<0>                     &=                   { lexerTokenInfo AND_ASSIGN }
<0>                     \-\-                   { lexerTokenInfo DEC_OP }
<0>                     \/=                   { lexerTokenInfo DIV_ASSIGN }
<0>                     ==                   { lexerTokenInfo EQ_OP }
<0>                     >=                   { lexerTokenInfo GE_OP }
<0>                     \+\+                   { lexerTokenInfo INC_OP }
<0>                     &&                   { lexerTokenInfo LAND_OP }
<0>                     \<=                   { lexerTokenInfo LE_OP }
<0>                     \|\|                   { lexerTokenInfo LOR_OP }
<0>                     >>                   { lexerTokenInfo SHR_OP }
<0>                     \<\<                   { lexerTokenInfo SHL_OP }
<0>                     \%=                   { lexerTokenInfo MOD_ASSIGN }
<0>                     \*=                   { lexerTokenInfo MUL_ASSIGN }
<0>                     !=                   { lexerTokenInfo NE_OP }
<0>                     \|=                   { lexerTokenInfo OR_ASSIGN }
<0>                     \-=                   { lexerTokenInfo SUB_ASSIGN }
<0>                     ::                   { lexerTokenInfo TYPE_QUAL }
<0>                     ^=                   { lexerTokenInfo XOR_ASSIGN }
<0>                     =                 { lexerTokenInfo (CHAR '=') }
<0>                     \?                 { lexerTokenInfo (CHAR '?') }
<0>                     :                 { lexerTokenInfo (CHAR ':') }
<0>                     \.                 { lexerTokenInfo (CHAR '.') }
<0>                     \,                    { lexerTokenInfo (CHAR ',') }
<0>                     \(                    { lexerTokenInfo (CHAR '(') }
<0>                     \)                    { lexerTokenInfo (CHAR ')') }
<0>                     \{                    { lexerTokenInfo (CHAR '{') }
<0>                     \}                    { lexerTokenInfo (CHAR '}') }
<0>                     !                    { lexerTokenInfo (CHAR '!') }
<0>                     \~                     { lexerTokenInfo (CHAR '~') }
<0>                     \[                     { lexerTokenInfo (CHAR '[') }
<0>                     \]                     { lexerTokenInfo (CHAR ']') }
<0>                     \;                     { lexerTokenInfo (CHAR ';') }
<0>                     \|                     { lexerTokenInfo (CHAR '|') }
<0>                     \^                     { lexerTokenInfo (CHAR '^') }
<0>                     &                     { lexerTokenInfo (CHAR '&') }
<0>                     \<                     { lexerTokenInfo (CHAR '<') }
<0>                     \>                     { lexerTokenInfo (CHAR '>') }
<0>                     \+                     { lexerTokenInfo (CHAR '+') }
<0>                     \-                     { lexerTokenInfo (CHAR '-') }
<0>                     \*                     { lexerTokenInfo (CHAR '*') }
<0>                     \/                     { lexerTokenInfo (CHAR '/') }
<0>                     \%                     { lexerTokenInfo (CHAR '%') }

<0>                     $simpleop               { skip }
<0>                     @newline                { skip }
<0>                     $whitespace             { skip }

<0>                     .                       { lexerTokenInfoFunc handleError     }
<comment>               .                       ;


{

-- Token Functions -------------------------------------------------------------

lexerTokenInfo :: Token -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfo t (AlexPn a ln c, _, _, s) l = do
    fn <- alexFilename
    return $ TokenInfo t (take l $ s) (pos fn ln c a)

lexerTokenInfoFunc :: (String -> Alex Token) -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfoFunc f (AlexPn a ln c, _, _, s) l = do 
    r <- f (take (fromIntegral l) s)
    fn <- alexFilename
    return $ TokenInfo r (take (fromIntegral l) s) (pos fn ln c a)

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
    
saveStateString :: AlexInput -> Int -> Alex TokenInfo
saveStateString input len = do
    aus <- get
    skip input len
    modify (\ aus -> aus { stateString = "" } )
    lexerTokenInfo (STR_FRAGMENT $ stateString aus) input len

leaveStateStringVariable :: AlexInput -> Int -> Alex TokenInfo
leaveStateStringVariable input len = do
    aus <- get
    alexSetStartCode state_string
    skip input len
    lexerTokenInfo (STR_IDENTIFIER $ stateString aus) input len

enterNewComment :: AlexInput -> Int -> Alex TokenInfo
enterNewComment input len = do
    modify (\ aus -> aus { commentDepth = 1 } )
    alexSetStartCode comment
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
    when (cd == 1) $ alexSetStartCode 0
    skip input len

-- Alex Functions --------------------------------------------------------------

data AlexUserState = AlexUserState 
    { filename     :: !String
    , types        :: [String]
    , commentDepth :: Integer
    , stateString  :: String
    , tokens       :: [TokenInfo]
    }

alexFilename :: Alex String
alexFilename = liftM filename get

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "" [] 0 "" []

instance MonadState AlexUserState Alex where
    get = alexGetUserState
    put = alexSetUserState

instance MonadError SecrecError Alex where
    throwError e = Alex $ \ s -> Left (show e)
    catchError (Alex un) f = Alex $ \ s -> either (catchMe s) Right (un s)
        where 
        catchMe s = fmap (split (const s) id) . runAlex "" . f . read

{-# INLINE split #-}
split :: (a -> b) -> (a -> c) -> a -> (b, c)
split f g a = (f a, g a)

alexEOF :: Alex TokenInfo
alexEOF = do 
    (AlexPn a ln c, _, _, _) <- alexGetInput
    fn <- alexFilename
    return $ TokenInfo TokenEOF "<EOF>" (pos fn ln c a)


-- Processing Functions --------------------------------------------------------

runIdAlex :: String -> String -> Alex a -> Either String a
runIdAlex fn str parse = runAlex str $ do
    put (alexInitUserState { filename = fn })
    toks <- getAlexTokens
    idtoks <- runIdLexer fn toks
    modify $ \aus -> aus { tokens = idtoks }
    parse

runIdAlexTokens :: String -> String -> Either String [TokenInfo]
runIdAlexTokens fn str = runIdAlex fn str $ liftM tokens get

injectResult :: Either String a -> Alex a
injectResult (Left err) = throwError (read err)
injectResult (Right a) = return a

-- | Alex lexer
--lexer :: (TokenInfo -> Alex a) -> Alex a
--lexer cont = alexMonadScan >>= cont

-- Composite lexer
lexer :: (TokenInfo -> Alex a) -> Alex a
lexer cont = do
    next <- state $ \aus -> let tok:toks = tokens aus in (tok,aus {tokens = toks} )
    cont next

getAlexTokens :: Alex [TokenInfo]
getAlexTokens = do 
    tok <- alexMonadScan
    case tSymb tok of
        TokenEOF -> return [tok]
        _ -> liftM (tok:) getAlexTokens

getTokens :: Alex [TokenInfo]
getTokens = liftM tokens get

flushLexer :: Alex ()
flushLexer = return ()

}