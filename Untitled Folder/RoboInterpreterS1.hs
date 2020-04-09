import qualified Data.Map as M
import SocketComm
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
import Network (PortNumber)
import Control.Applicative (liftA2)

data Condition = IsWall { arg :: Direction }  deriving (Show,Eq,Read)

data Direction = LEFT | RIGHT | UP | DOWN | NONE deriving (Show,Eq,Read)

data NObject = OpBrace | ClBrace | EmptyLine | Comment | Else | Other String deriving (Eq,Show)

type FunctionName = String

type VariableName = String
data Expr = GetMem1 | Add Expr1 Expr1 | SingleVar VariableName | Val1 Int deriving (Eq,Show) 
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
                   BlockStart { env :: M.Map VariableName Int } |  
                   BlockEnd | --
                   IfIntermediate { ifinter :: Condition } | --
                   FunctionStart { fs :: FunctionName,
                                   env :: M.Map VariableName Int } | --
                   FunctionDef { fd :: FunctionName } | --
                   FunctionCall { fc :: FunctionName } --
                 deriving (Eq,Show)

type ForInterpreter = [(Instruction,String)]
type CurrentPosition = Int
type FunctionTable = M.Map Int Int

data InterpreterState = InterpreterState { insStr :: ForInterpreter,
                                           pointer :: CurrentPosition,
                                           funcTab :: FunctionTable,
                                           robo :: Robo,
                                           comm :: Communicator } deriving (Eq,Show)

type Color = (Int,Int,Int)
type ColorTup = (Color,Color)
data Robo = Robo { id :: Int,
                   roboColor :: ColorTup,
                    mem :: Int 
                   } deriving (Eq,Show)

main :: IO ()
main = do
  args<-getArgs
  if length args == 3
    then do
      let rID = read (args!!0)::Int
      comm <- newCommunicator (read (show (2*(3000+rID)+1))::PortNumber) (read (show (2*(3000+rID)))::PortNumber)
      let filePath = args!!1
      let color = read (args!!2)::ColorTup 
      let initRobo = Robo rID color 0
      -- comm1 <- verifyCommunicator comm
      str1 <- readFile filePath
      let initInterpreterState = (\(x,y,z)->InterpreterState x y z initRobo comm) $ getInterpreterReady str1      
      _<-runStateT runRobo initInterpreterState
      terminateCommunicator comm
      return ()
    else fail "Invalid Args!!!" >> return ()
    
runRobo :: StateT InterpreterState IO ()
runRobo = do
  intprState <- get
  lift $ putStrLn (show intprState)
  newIntpr <- lift $ evalStateT runInterpreter $ toNextPointer intprState
  if pointer newIntpr <= -1 then lift (sendTo (comm intprState) "Halt") >> return ()
    else do
    lift $ sendRequest newIntpr    
    entry <- lift $ getFrom (comm intprState)    
    let code = head entry
    case code of
      '1' -> put newIntpr >> runRobo
      '2' -> put (newIntpr {robo = ((robo newIntpr) { roboColor = read (tail entry) :: ColorTup })}) >> runRobo
      '3' -> lift (putStrLn ("R" ++ show (Main.id $ robo intprState) ++ " quitting..")) >> return ()
      _ -> fail "Unknown Response from Grid!!"
 
runInterpreter :: StateT InterpreterState IO InterpreterState
runInterpreter = do
  intprState <- get 
  case getCurrentInstruction intprState of
    NOP x -> put (toNextPointer intprState) >> runInterpreter
    Jump i -> put (intprState { pointer = i }) >> runInterpreter
    JumpC i -> put (executeJumpC intprState i)  >> runInterpreter
    FlipPassable -> return intprState
    FlipWritable -> return intprState    
    SetMem x     -> put (intprState {robo = updateRoboMem intprState x }) >> runInterpreter
    Asgn ln vn expr ->  put ( intprState { insStr = updatedState }) >> runInterpreter 
                where 
                  updatedState = zip updatedState1 updatedState2  
                  updatedState1 = (take contextidx insList) ++ [ updateFSorBS inst vn evaluatedVal] ++ (drop (contextidx+1) (insList))
                  updatedState2 = (take contextidx (insListStr)) ++ [instStrFormat] ++ (drop (contextidx+1) (insListStr))
                  contextidx   = findContext intprState 
                  evaluatedVal = evaluate expr intprState 
                  inst         = (map fst (insStr intprState)) !! contextidx 
                  instStrFormat = (map snd (insStr intprState)) !! contextidx 
                  insList      =  map fst (insStr intprState)
                  insListStr   =  map snd (insStr intprState)
    EndOfFunction eo r -> if (eo == "main" && r == [])
                          then return (intprState {pointer = -1})
                          else put (executeEOFunc intprState) >> runInterpreter
    Read -> return intprState
    Write -> return intprState
    Move d -> return intprState
    If c i e -> do
      lift $ sendTo (comm intprState) ("I" ++ show (arg c))
      str1 <- lift $ getFrom (comm intprState)
      lift $ putStrLn $ "  " ++ str1
      let condEval = read str1 :: Bool
      case condEval of
        True -> put (intprState { pointer = i }) >> runInterpreter
        False -> put (intprState { pointer = e }) >> runInterpreter
    _ -> fail "Bad Parse"
        

updateRoboMem :: InterpreterState -> Int -> Robo
updateRoboMem (InterpreterState i p f (Robo id rc mem) c) val = Robo id rc val

updateFSorBS :: Instruction ->  String -> Int -> Instruction 
updateFSorBS (FunctionStart x y) vn val = FunctionStart {fs = x, env = M.insert vn val y} 
updateFSorBS (BlockStart x ) vn val = BlockStart { env = M.insert vn val x} 



--evaluateExpr :: InterpreterState -> Instruction -> InterpreterState 
--evaluateExpr iStat (Asgn ln vn expr) = evaluate expr

--evaluate :: Expr -> InevaluateExpr iStat (Asgn ln vn expr) = evaluate expr

evaluate :: Expr -> InterpreterState -> Int  
evaluate (Val1 x) intStat = x
evaluate (SingleVar x) intStat= undefined
evaluate (Add (Var x) (Val y)) intStat= (getValueFromContext intStat x) + y
evaluate (Add (Var x) (Var y)) intStat= (getValueFromContext intStat x) + (getValueFromContext intStat y)

getValueFromContext :: InterpreterState -> String -> Int
getValueFromContext intStat x = undefined 
          

findContextList :: [Instruction] -> Int -> String -> [Instruction]
findContextList xs y vna = f (map fst $ contextHolderList) 
   where 
    contextHolderList = filter  (\ (ins,idx) -> case ins of 
                                                 FunctionStart x y -> True
                                                 BlockStart x      -> True
                                                 _                 -> False) inst
    lengthOfContextList = length$ contextHolderList 
    inst = zip (take y (xs)) [0..]


f t = drop  (length (t) - xlen - 1) t
 where 
  xlen = length (takeWhile (\ x -> case x of
                        FunctionStart x y -> False
                        _                 -> True) (reverse t))
findContext :: InterpreterState -> Int 
findContext xs = snd $ contextHolderList !! (lengthOfContextList-1) 
   where 
    contextHolderList = filter  (\ (ins,idx) -> case ins of 
                                                 FunctionStart x y -> True
                                                 BlockStart x      -> True
                                                 _                 -> False) inst
    lengthOfContextList = length$ contextHolderList 
    asgnIdx = (pointer xs)
    inst = zip (take asgnIdx (map fst (insStr xs))) [0..]








sendRequest :: InterpreterState -> IO ()
sendRequest intprState = case getCurrentInstruction intprState of
                           Move x -> sendTo (comm intprState) ([head $ show x]) 
                           Read -> sendTo (comm intprState) "Read"
                           Write -> sendTo (comm intprState) ("Write " ++ (show $ roboColor (robo intprState)))
                           FlipPassable -> sendTo (comm intprState) "FP"
                           FlipWritable -> sendTo (comm intprState) "FW"
                           
executeJumpC :: InterpreterState -> Int -> InterpreterState
executeJumpC intprState i = retListUpdated { pointer = i }
  where
    eoFuncPointer = M.findWithDefault (-1) i (funcTab intprState)
    retListUpdated = intprState { insStr = listUpdate (insStr intprState)
                                         ((\(ins,s)-> (ins {retList = (retList ins) ++ [pointer intprState +1]},s)) $
                                          (insStr intprState)!!eoFuncPointer)
                                         eoFuncPointer }

executeEOFunc :: InterpreterState -> InterpreterState
executeEOFunc intprState = state1 { insStr = newInsStr }
  where
    currStr = getCurrentString intprState
    currIns = getCurrentInstruction intprState
    state1 = intprState { pointer = last $ retList currIns } 
    newInsStr = listUpdate (insStr state1) (currIns {retList = init $ retList currIns}, currStr) (pointer intprState)
    
getCurrentInstruction :: InterpreterState -> Instruction
getCurrentInstruction intprState = fst $ (insStr intprState)!!(pointer intprState)

getCurrentString :: InterpreterState -> String
getCurrentString intprState = snd $ (insStr intprState)!!(pointer intprState)

toNextPointer :: InterpreterState -> InterpreterState
toNextPointer intprState = intprState { pointer = (pointer intprState) + 1 }

----------------------------------Make Initial Interpreter State--------------------------

getInterpreterReady :: String -> (ForInterpreter, CurrentPosition, FunctionTable)
getInterpreterReady str1 = (forIntpr, (fst intprInit), (snd intprInit))
  where
    intprInit = interpreterInit insListWithoutFinally
    forIntpr = zip (finally insListWithoutFinally) (lines str1)
    insListWithoutFinally = (resolveAsgnStmt $resolveReturn $ ifJumpResolve $ verifyIfs $ verifyIfs $  resolveFunctionCalls $ verifyFunctions $ getSource str1)

interpreterInit :: [Instruction] -> (Int, M.Map Int Int)
interpreterInit xs = ((getStartPoint lineFunc),(M.fromList $ toFuncEOFmap lineFunc))
  where
    lineFunc = filter (\ (i,ins)-> case ins of
                          FunctionStart s _ -> True
                          EndOfFunction s r -> True
                          _ -> False ) (zip [0..] xs)

getStartPoint :: [(Int,Instruction)] -> Int
getStartPoint xs = (\[(i,ins)]-> i) $ filter (\ (i,ins)-> ins == (FunctionStart "main" (M.fromList []))) xs

toFuncEOFmap :: [(Int,Instruction)] -> [(Int,Int)]
toFuncEOFmap xs = if xs == [] then [] else [(\xss-> (fst (xss!!0), fst (xss!!1))) $ (take 2 xs)] ++ toFuncEOFmap (drop 2 xs)

---------------------------------Instruction Conversion/Jump Resolution--------------------------------

finally :: [Instruction] -> [Instruction]
finally xs = map (\x-> case x of
                         FunctionDef z -> NOP (Other $ show $ FunctionDef z)
                         FunctionStart z x -> NOP (Other $ show $ FunctionStart z x)
                         BlockStart y -> NOP $ Other "BlockStart"
                         z -> z ) xs

resolveFunctionCalls :: [Instruction] -> [Instruction]
resolveFunctionCalls xs = foldl (\iList (ins,index)-> listUpdate iList (JumpC (nextIndex (FunctionStart (fc ins) (M.fromList [])) iList)) index) xs functionCallIndices 
  where
    functionCallIndices = filter (\(ins,index)-> case ins of
                                           FunctionCall x -> True
                                           _ -> False) $  zip xs [0..]

resolveAsgnStmt :: [Instruction]-> [Instruction]
resolveAsgnStmt xs = asgnStmtIndices  
  where
    asgnStmtIndices = map (\(ins,index)-> case ins of
                                           Asgn { asgnLn = x , vn =y , expr= e} -> Asgn {asgnLn = index+1 ,vn=y ,expr=e}
                                           n -> n ) $  zip xs [0..]

resolveReturn :: [Instruction] -> [Instruction]
resolveReturn xs = foldl (\iList (ins,index)-> listUpdate iList (Jump (nextEOFuncIndex index iList)) index) xs functionCallIndices 
  where
    functionCallIndices = filter (\(ins,index)-> case ins of
                                           Return -> True
                                           _ -> False) $  zip xs [0..]

findMatching :: Eq a => a -> a -> Int -> [a] -> Int -> Int
findMatching x y 0 xs n = n
findMatching x y i [] n = -1
findMatching x y i xs n | x == head xs = findMatching x y (i-1) (tail xs) (n+1)
                        | y == head xs = findMatching x y (i+1) (tail xs) (n+1)
                        | otherwise = findMatching x y i (tail xs) (n+1)

getSource :: String -> [Instruction]
getSource str = if lefts parsedLines == [] then rights parsedLines else (map (\x->error $ show x) $ lefts parsedLines)
  where
    parsedLines = map (parser instructionParser) (lines str)

listUpdate :: [a] -> a -> Int -> [a]
listUpdate xs x i = take i xs ++  [x] ++ drop (i+1) xs 

nextIndex :: Eq a => a -> [a] -> Int
nextIndex x xs = maybe (error "Syntax Error") Prelude.id (findIndex (==x) xs)


-- listUpdate :: list -> element -> index -> list

verifyFunctions :: [Instruction] -> [Instruction]
verifyFunctions xs = foldl (\iList (ins,index)-> listUpdate (listUpdate iList (FunctionStart (fd ins) (M.fromList []) ) (nextOpIndex index iList)) 
                       (EndOfFunction (fd ins) []) (findMatching (NOP ClBrace) (NOP OpBrace) 1 (drop (1+nextOpIndex index iList) iList)
                        (nextOpIndex index iList))) xs fDefIndices 
  where
    fDefIndices = filter (\(ins,index)-> case ins of
                                           FunctionDef x -> True
                                           _ -> False) $  zip xs [0..]

verifyIfs :: [Instruction] -> [Instruction]
verifyIfs xs = foldl (\iList (ins,index)-> listUpdate (listUpdate iList (BlockStart   {env = (M.fromList [])}   ) (nextOpIndex index iList)) BlockEnd (findMatching (NOP ClBrace) (NOP OpBrace) 1 (drop (1+nextOpIndex index iList) iList) (nextOpIndex index iList))) xs ifInterIndices 
  where
    ifInterIndices = filter (\(ins,index)-> case ins of
                                           IfIntermediate x -> True
                                           --FunctionDef x -> True
                                           _ -> False) $  zip xs [0..]

ifJumpResolve :: [Instruction] -> [Instruction]
ifJumpResolve xs = foldl (\iList (ins,index)-> listUpdate (listUpdate iList (Jump $ blockEndIndex index iList) (findMatching (BlockEnd) (BlockStart {env= (M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList))) (Jump $ blockEndIndex index iList) (findMatching (BlockEnd) (BlockStart {env = (M.fromList [])}) 1 (drop (1+ nextBSIndex (1+(findMatching (BlockEnd) (BlockStart {env= (M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList))) iList) iList) (nextBSIndex (1+(findMatching (BlockEnd) (BlockStart {env =(M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList))) iList))) ifInterToIf ifInterIndices1
  where
    ifInterToIf = foldl (\iList (ins,index)-> listUpdate iList (If (ifinter ins) (nextBSIndex index iList) (nextBSIndex (findMatching BlockEnd (BlockStart {env =(M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList)) iList)) index) xs ifInterIndices1
    ifInterIndices1 = filter (\(ins,index)-> case ins of
                                           IfIntermediate x -> True
                                           _ -> False) $  zip xs [0..]

blockEndIndex ind il = 1+findMatching (BlockEnd) (BlockStart {env= (M.fromList [])}) 1 (drop (1+ nextBSIndex (1+ifend) il) il) (nextBSIndex (1+ifend) il)
  where
    ifend = (findMatching (BlockEnd) (BlockStart  {env= (M.fromList [])}) 1 (drop (1+nextBSIndex ind il) il) (nextBSIndex ind il))

nextEOFuncIndex :: Int -> [Instruction] -> Int
nextEOFuncIndex i xs = i + (head $ fst $ unzip $ getEofs)
  where
    getEofs = filter (\x-> case x of
                             (index,EndOfFunction n rl) -> True
                             (index,_) -> False ) $ zip [1..] (drop (i+1) xs)

nextOpIndex :: Int -> [Instruction] -> Int
nextOpIndex ind il = 1 + ind + nextIndex (NOP OpBrace) (drop (ind+1) il)

nextBSIndex :: Int -> [Instruction] -> Int
nextBSIndex ind il = 1 + ind + nextIndex (BlockStart {env= (M.fromList [])}) (drop (ind+1) il)

nextBEIndex :: Int -> [Instruction] -> Int
nextBEIndex ind il = 1 + ind + nextIndex BlockEnd (drop (ind+1) il)

--------------------Parser------------------

languageDef :: LanguageDef u
languageDef = emptyDef { Token.identStart = letter <|> satisfy (=='_')
                       , Token.identLetter = alphaNum
                       , Token.reservedNames = ["move","up","left","right","down","read","write","main","return","if","else","return","setmem","getmem"]
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
             try' singlevarparser 

  where
    getmemparser =  (whiteSpace >> ((\x-> GetMem1) <$> string "getmem")) 
    singlevarparser = whiteSpace >> try'( ((\x -> Val1 (read $show x:: Int)) <$> natural) <|> ((\x -> SingleVar x) <$> many1 alphaNum))
    exprparser = liftA2 (\x y -> Add (Var x) (Val (read $ show y ::Int))) varnameparser intparser
    varnameparser = (whiteSpace >> many1 alphaNum) 
    intparser = (whiteSpace >> string "+" >> whiteSpace >> natural)
    
returnParser :: Parser Instruction
returnParser = whiteSpace >> reserved "return" >> return Return

flipPassableParser :: Parser Instruction
flipPassableParser = whiteSpace >> reserved "flippassable" >> parens (string "") >> whiteSpace >> return FlipPassable

flipWritableParser :: Parser Instruction
flipWritableParser = whiteSpace >> reserved "flipwritable" >> parens (string "") >> whiteSpace >> return FlipWritable

functionCallParser :: Parser Instruction
functionCallParser = whiteSpace >> ((\x-> FunctionCall x) <$> (many1 alphaNum <* (whiteSpace >> parens (string ""))))

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
funcDefParser = whiteSpace >> reserved "def" >> whiteSpace >> ((\x-> FunctionDef x) <$> (many1 alphaNum <* (whiteSpace >> parens (string ""))))

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
