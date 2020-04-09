
import qualified Data.Map as M
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.Parsec.Prim
import qualified Text.ParserCombinators.Parsec.Token as Token
import Control.Monad (void)
import Data.Either (lefts,rights)
import Data.List (findIndex)
import Control.Monad.State
import Control.Concurrent (threadDelay)
import System.Environment (getArgs)
import Control.Applicative (liftA2,liftA3)

data Condition = IsWall { arg :: Direction }  deriving (Show,Eq,Read)

data Direction = LEFT | RIGHT | UP | DOWN | NONE deriving (Show,Eq,Read)

data NObject = OpBrace | ClBrace | EmptyLine | Comment | Else | Other String deriving (Eq,Show)

type FunctionName = String
type VariableName = String

-- x= f(123,y)
data Expr = GetMem1 | Add Expr1 Expr1 | SingleVar VariableName | Val1 Int | FuncCall FunctionName [Expr1]  deriving (Eq,Show) 
data Expr1 = Var VariableName | Val Int deriving (Eq,Show)

data Instruction = Read | 
                   Write |
                   Asgn  { asgnLn :: Int ,
                          vn  :: VariableName,
                          expr :: Expr
                         }           |
                   SetMem { val :: Int} |
                   GetMem |
                   Move { dir :: Direction } | 
                   If { ifc :: Condition,
                        ifi :: Int,
                        ife :: Int } |
                   EndOfFunction { eo :: FunctionName,
                                   retList :: [Int] } | 
                   NOP NObject | 
                   JumpC { jc :: Int } |
                   Jump { j :: Int } |
                   FlipPassable |
                   FlipWritable |
                   Return | --
                   BlockContext { env :: M.Map VariableName Int } |  
                   BlockStart | --
                   BlockEnd | --
                   IfIntermediate { ifinter :: Condition } | --
                   FunctionStart { fs :: FunctionName } | --
                   FunctionDef { fd :: FunctionName , 
                                 args :: Arguments,
                                 returnType :: Type         
                                                    } | --

                   FunctionCall { fc :: FunctionName ,
                                  param :: [Expr1]} --
                 deriving (Eq,Show)

data Type = INT | FUNC deriving (Show,Eq)
type Arguments =[(Type,VariableName)] 
type ForInterpreter = [(Instruction,String)]
type CurrentPosition = Int
type FunctionTable = M.Map Int Int


type Color = (Int,Int,Int)
type ColorTup = (Color,Color)
data Robo = Robo { id :: Int,
                   roboColor :: ColorTup,
                   mem :: Int } deriving (Eq,Show)

languageDef :: LanguageDef u
languageDef = emptyDef { Token.identStart = letter <|> satisfy (=='_')
                       , Token.identLetter = alphaNum
                       , Token.reservedNames = ["int","func","move","up","left","right","down","read","write","main","return","if","else","return","setmem","getmem"]
                       , Token.caseSensitive = False
                       }

lexer :: Token.TokenParser u
lexer = Token.makeTokenParser languageDef

reserved :: String -> Parser ()
reserved  = Token.reserved lexer


natural :: Parser Integer
natural = Token.integer lexer

eol :: Parser ()
eol = void (char '\n') <|> eof

parens :: Parser a -> Parser a
parens = Token.parens lexer

whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer

curlies :: Parser a -> Parser a
curlies p = between (Token.symbol lexer "{") (Token.symbol lexer "}") p

brackets :: Parser a -> Parser a
brackets p = between (Token.symbol lexer "[") (Token.symbol lexer "]") p

try' = Text.ParserCombinators.Parsec.try

parser :: Parser a -> String -> Either ParseError a
parser p x = parse p "" x

instructionParser :: Parser Instruction
instructionParser = try' readWriteParser <|>
                    (try' ifIntermediateParser <|>
                     try' asgnParser <|>
                    try' setMemParser <|>
                    try' moveParser <|>
                    try' flipPassableParser <|>
                    try' flipWritableParser <|>
                    try' returnParser <|>
                    try' funcDefParser <|>
                    try' nopParser <|>
                    try' functionCallParser) 

ifIntermediateParser :: Parser Instruction
ifIntermediateParser = whiteSpace >> reserved "if" >> ((\x-> IfIntermediate x) <$> parens conditionParser)

setMemParser :: Parser Instruction
setMemParser = try' (whiteSpace >> reserved "setmem" >>  whiteSpace >> ((\x -> SetMem { val = read(show(x))::Int} ) <$>  (parens natural)))

-- x = getmem
-- x1 = x
-- x2 = x1 + 1
-- x3 = x1 + x2

asgnParser :: Parser Instruction 
asgnParser = liftA2 (\x y -> Asgn { asgnLn = (-1) ,vn = x, expr = y}) (varnameparser )  (exprParser)
         where 
          varnameparser =  whiteSpace >> many1 alphaNum <* (whiteSpace >> string "=") 

            

exprParser :: Parser Expr
exprParser = try' getmemparser <|>
             try' exprparser <|>
             try' singlevarparser <|>
             try' functioncallparser 

  where
    getmemparser =  (whiteSpace >> ((\x-> GetMem1) <$> string "getmem")) 
    singlevarparser = whiteSpace >> try'( ((\x -> Val1 (read $show x:: Int)) <$> natural) <|> ((\x -> SingleVar x) <$> many1 alphaNum))
    exprparser = liftA2 (\x y -> Add (Var x) (Val (read $ show y ::Int))) varnameparser intparser
    varnameparser = (whiteSpace >> many1 alphaNum) 
    intparser = (whiteSpace >> string "+" >> whiteSpace >> natural)
    functioncallparser = (whiteSpace >> liftA2 (\x y-> FuncCall x y) (many1 alphaNum) (paramListParser)
    paramListParser     = sepBy singlevarparser commaSeperator  
    singlevarparser = ( whiteSpace >> ((\x -> Val (read $show x:: Int)) <$> (whiteSpace >> natural <* whiteSpace))) <|>(((\x -> Var x) <$> (whiteSpace >> (many1 alphaNum <* whiteSpace))))
    
returnParser :: Parser Instruction
returnParser = whiteSpace >> reserved "return" >> return Return

flipPassableParser :: Parser Instruction
flipPassableParser = whiteSpace >> reserved "flippassable" >> parens (string "") >> whiteSpace >> return FlipPassable

flipWritableParser :: Parser Instruction
flipWritableParser = whiteSpace >> reserved "flipwritable" >> parens (string "") >> whiteSpace >> return FlipWritable

functionCallParser :: Parser Instruction
functionCallParser = whiteSpace >> liftA2 (\x y -> FunctionCall x y) functionName  (parens paramListParser)
  where
    functionName = many1 alphaNum 
    paramListParser     = sepBy singlevarparser commaSeperator  
    singlevarparser = ( whiteSpace >> ((\x -> Val (read $show x:: Int)) <$> (whiteSpace >> natural <* whiteSpace))) <|>(((\x -> Var x) <$> (whiteSpace >> (many1 alphaNum <* whiteSpace))))


readWriteParser :: Parser Instruction
readWriteParser = try' (whiteSpace >> reserved "read" >> whiteSpace >> parens (string "") >> whiteSpace >> return Read) <|>
                  try' (whiteSpace >> reserved "write" >> whiteSpace >> parens (string "") >> whiteSpace >> return Write)

nopParser :: Parser Instruction
nopParser = (\x-> NOP x) <$> (try' commentParser <|>
                              try' opBraceParser <|>
                              try' clBraceParser <|>
                              try' elseParser <|>
                              try' blankLineParser)

moveParser :: Parser Instruction
moveParser = whiteSpace >> reserved "move" >> Move <$> parens directionParser

funcDefParser :: Parser Instruction
funcDefParser = whiteSpace >> reserved "def" >> whiteSpace >> functionDefParser  
 where
    functionDefParser = liftA3 (\x y z-> FunctionDef x y z) (many1 alphaNum) (whiteSpace >> parens argListParser) (returnType) 
    argListParser     = sepBy varTypeParser commaSeperator  
    returnType        = whiteSpace >> parens returnTypeParser 

commaSeperator :: Parser ()
commaSeperator = skipMany (char ',')


varTypeParser :: Parser (Type,VariableName)
varTypeParser     = (whiteSpace >> reserved "int" >> many1 alphaNum >>= (\x -> return (INT,x)) ) <|>
                    (whiteSpace >> reserved "func" >> many1 alphaNum >>= (\x -> return (FUNC,x)) )  

returnTypeParser = (reserved "int" >> return INT) <|>
                   (reserved "func" >> return FUNC) 



conditionParser :: Parser Condition
conditionParser = whiteSpace >> reserved "iswall" >> ((\x-> IsWall x) <$> parens directionParser)

blankLineParser :: Parser NObject
blankLineParser = whiteSpace <* eol >> return EmptyLine

opBraceParser :: Parser NObject
opBraceParser = (many (oneOf "\t ") >> char '{' >> whiteSpace) >> return OpBrace

clBraceParser :: Parser NObject
clBraceParser = (many (oneOf "\t ") >> char '}' >> whiteSpace) >> return ClBrace

elseParser :: Parser NObject
elseParser = (many (oneOf "\t ") >> reserved "else" >> whiteSpace) >> return Else

commentParser :: Parser NObject
commentParser = (whiteSpace >> string "--" >> many anyChar) >> return Comment

directionParser :: Parser Direction
directionParser = (reserved "up" >> return UP) <|>
                  (reserved "right" >> return RIGHT) <|>
                  (reserved "left" >> return LEFT) <|>
                  (reserved "down" >> return DOWN) <|>
                  (many alphaNum >> return NONE)
