import qualified Data.Map as M
import Data.List
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
import Control.Applicative (liftA2,liftA3)

data Condition = IsWall { arg :: Direction }  deriving (Show,Eq,Read)

data Direction = LEFT | RIGHT | UP | DOWN | NONE deriving (Show,Eq,Read)

data NObject = OpBrace | ClBrace | EmptyLine | Comment | Else | Other Instruction  deriving (Eq,Show,Read)

data EnvType = ParENV | ENV deriving (Eq,Show)
type FunctionName = String
type VariableName = String
data Expr = GetMem1 | Add Expr1 Expr1 | SingleVar VariableName | Val1 Int | FuncCall FunctionName [Expr1]  deriving (Eq,Show,Read)
data Expr1 = Var VariableName | Val Int | NULL deriving (Eq,Show,Read)
data EnvValue = EInt Int | EPar (FunctionName,[Expr1]) | NIL deriving (Eq,Show,Read)
data JumpType = RETURN | IF deriving (Eq,Show,Read)
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
                                   retList :: [(Int,ForInterpreter)] } | 
                   NOP NObject | 
                   JumpC { jc :: Int ,
                           fn :: FunctionName,
                           param :: [Expr1] } |
                   Jump { j :: Int , 
                         jtype:: JumpType ,
                         returnVal:: Expr1} |
                   FlipPassable |
                   FlipWritable |
                   Return {retval :: Expr1}| --
                   BlockStart { env :: M.Map VariableName Int ,
                                bend :: Int,
                                envpar :: M.Map VariableName (FunctionName,[Expr1]) } | --
                   BlockEnd | --
                   IfIntermediate { ifinter :: Condition } | --
                   FunctionStart { fs :: FunctionName,
                                   env :: M.Map VariableName Int ,
                                   envpar :: M.Map VariableName (FunctionName,[Expr1]) } | --
                   FunctionDef { fd :: FunctionName , 
                                 argum :: Arguments,
                                 returnType :: Type         
                                                    } | --
                   FunctionCall { fc :: FunctionName ,
                                  param :: [Expr1]} --
                 deriving (Eq,Show,Read)
data Type = INT | FUNC | VOID deriving (Eq,Show,Read)
type Arguments = [(Type,VariableName)]
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
      putStrLn (args!!0)
      putStrLn (args!!1)
      --putStrLn (args!!2)
      let rID = read (args!!0)::Int
      comm <- newCommunicator (read (show (2*(3000+rID)+1))::PortNumber) (read (show (2*(3000+rID)))::PortNumber)
      let filePath = args!!1
      let color = read (args!!2)::ColorTup 
      let initRobo = Robo rID color 0
      -- comm1 <- verifyCommunicator comm
      str1 <- readFile filePath
      let initInterpreterState = (\(x,y,z)->InterpreterState x y z initRobo comm) $ getInterpreterReady str1      
      putStrLn (show $ initInterpreterState)
      _ <-runStateT runRobo initInterpreterState
      terminateCommunicator comm
      return ()
    else fail "Invalid Args!!!" >> return ()
    
runRobo :: StateT InterpreterState IO ()
runRobo = do
  lift $ putStrLn ("heyy")
  intprState <- get
  newIntpr <- lift $ evalStateT runInterpreter $ toNextPointer intprState
  lift $ putStrLn ("\n\n\n\nafter eval state" ++ show newIntpr)
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
 --   Jump i jtype rval-> put (intprState { pointer = i }) >> runInterpreter   
    Jump i jtype rval-> eJump  >> runInterpreter  
                  where
              --      eJump = lift $ fail $ show $  executeJump intprState (Jump i jtype rval)  
              --     {-- 
                   eJump = case executeJump intprState (Jump i jtype rval) of 
                              Just newstate  -> put ( newstate {pointer = i}  )
                            --  x -> lift $ fail $ show $ x
                              Nothing -> lift $fail ((show (pointer intprState))++ " :: " ++ "Function with improper number of argument")
                   --}
    JumpC i y z -> eJumpC  >> runInterpreter
                  where 
                   eJumpC = case executeJumpC intprState (JumpC i y z) of 
                              Just x  -> put x
                              Nothing -> lift $fail ((show (pointer intprState))++ " :: " ++ y ++"Function with improper number of argument")
    FlipPassable -> return intprState
    FlipWritable -> return intprState    
    SetMem x     -> put (staten {robo = updateRoboMem intprState x}) >> runInterpreter 
                   where 
                        staten = toNextPointer intprState
    Asgn ln vn expr ->  evalExpRe  >>  runInterpreter 
                   where 
                        evalExpRe = -- lift $ fail $ show $  (evaluate expr intprState)           
                              --case evaluate expr intprState of 
                              -- (evalVal ,istate ) -> lift $ fail $ show $( evalVal,istate)
                             -- {-- 
                           --  case pointer intprState of 
                           --     24 ->  -- lift $ fail $ show $  contextidx --(evaluate expr intprState)           
                               --  ->   
                                     case (evaluate expr intprState) of           
                                      (NIL, st ) -> lift $fail ("ERRROR::"++(show ())++ " :: " ++ "Function with improper expresion")
                                      (evalVal , istate)  -> --lift $ fail $ show $ updatedState --  
                                                             case expr of
                                                              FuncCall _ _ -> put (istate {insStr = updatedState })
                                                              _            -> put (staten { insStr = updatedState  })  
                               --}
                                        where 
                                         --c = findContext st
                                         staten = toNextPointer istate
                                         updatedState = zip updatedState1 updatedState2  
                                         updatedState1 = (take contextidx insList) ++ [ updateFSorBS inst vn evalVal expr] ++ (drop (contextidx+1) (insList))
                                         updatedState2 = (take contextidx (insListStr)) ++ [instStrFormat] ++ (drop (contextidx+1) (insListStr))
                                         contextidx   = findContext istate   
                                         inst         = (map fst (insStr istate)) !! contextidx 
                                         instStrFormat = (map snd (insStr istate)) !! contextidx 
                                         insList      =  map fst (insStr istate)
                                         insListStr   =  map snd (insStr istate)
                               {-- _  ->                   
                                     case (evaluate expr intprState) of           
                                      (NIL, st )          -> lift $fail ("ERRROR::"++(show (st))++ " :: " ++ "Function with improper expresion")
                                      (evalVal , istate)  -> case expr of --lift $ fail $ show $ updatedState --   case expr of
                                                              FuncCall _ _ -> put (istate {insStr = updatedState })
                                                              _            -> put (staten { insStr = updatedState  })  
                                        where 
                                         --c = findContext st
                                         staten = toNextPointer istate
                                         updatedState = zip updatedState1 updatedState2  
                                         updatedState1 = (take contextidx insList) ++ [ updateFSorBS inst vn evalVal expr] ++ (drop (contextidx+1) (insList))
                                         updatedState2 = (take contextidx (insListStr)) ++ [instStrFormat] ++ (drop (contextidx+1) (insListStr))
                                         contextidx   = findContext istate   
                                         inst         = (map fst (insStr istate)) !! contextidx 
                                         instStrFormat = (map snd (insStr istate)) !! contextidx 
                                         insList      =  map fst (insStr istate)
                                         insListStr   =  map snd (insStr istate)
                              --} 

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
        

--executeJump :: InterpreterState -> Instruction -> Maybe InterpreterState 
executeJump intprState (Jump i retType val)  =  
  case retType of
    IF         -> Just intprState  
    RETURN     -> 
                  case val of
                     Val x ->  case instruction of 
                                  Asgn ln vn expr ->  Just (retListUpdated {pointer = currPtr})
                                    where
                                                 cntxtLineNo = findContext (intprState {pointer=ln}) 
                                                 instrRelativePos = cntxtLineNo - (fst $ funcRange)
                                                 newretList = (take instrRelativePos (snd$precontext))++ [(newInstruction,instructionStr)] ++ (drop (instrRelativePos+1) (snd$precontext))
                                                 preInstruction = fst $ ((snd$precontext) !! instrRelativePos)
                                                 newInstruction = updateInstruction preInstruction vn (EInt x) 
                                                 retListUpdated = intprState { insStr = listUpdate (insStr intprState)
                                                   ((\(ins,s)-> (ins {retList = (retList ins) ++ [(retAddress,newretList)]},s)) $
                                                   (insStr intprState)!!(eoFuncPointer))
                                                   (eoFuncPointer) }
                                                 eoFuncPointer = M.findWithDefault (-1) i (funcTab intprState)
                                  _               -> Just intprState  

                     Var x -> case  getValueFromContext intprState x  of
                                   NIL ->  Nothing 
                                   evaluatedVal ->   
                                        case instruction of 
                                           Asgn ln vn expr ->  Just retListUpdated {pointer = currPtr} 
                                               where
                                                 cntxtLineNo = findContext (intprState {pointer=ln}) 
                                                 instrRelativePos = cntxtLineNo - (fst $ funcRange)
                                                 newretList = (take instrRelativePos (snd$precontext))++ [(newInstruction,instructionStr)] ++ (drop (instrRelativePos+1) (snd$precontext))
                                                 preInstruction = fst((snd$precontext) !! instrRelativePos)
                                                 newInstruction = updateInstruction preInstruction vn (evaluatedVal)  
                                                 retListUpdated = intprState { insStr = listUpdate (insStr intprState)
                                                      ((\(ins,s)-> (ins {retList = (retList ins) ++ [(retAddress,newretList)]},s)) $
                                                      (insStr intprState)!! (snd$funcRange))
                                                      (snd$funcRange) }
                                           _               -> Just intprState  
                   
 where
     currPtr = pointer intprState 
     retList1 = retList $ fst ((insStr intprState )!!(snd$funcRange))
     retList2 = retList $ fst ((insStr intprState )!!(eoFuncPointer))
     funcRange = head $filter (\(x,y) -> x <= currPtr && currPtr <= y)  (M.toList (funcTab intprState))
     eoFuncPointer = M.findWithDefault (-1) (fst$funcRange) (funcTab intprState)
     precontext = (last $ retList2)
     retAddress  = fst $ precontext 
     instruction = fst ((insStr intprState)!!(retAddress-1))
     instructionStr =  snd ((insStr intprState)!!(retAddress-1))



updateInstruction :: Instruction ->  String -> EnvValue -> Instruction  --instead of Int type will be EnvValue 
updateInstruction (NOP (Other (FunctionStart x y z ))) vn val =  
  case val of 
    EInt v -> NOP (Other (FunctionStart {fs = x, env = M.insert vn v y , envpar=z })) 
    EPar v -> NOP (Other (FunctionStart {fs = x, env = y , envpar=M.insert vn v z })) 

updateInstruction (NOP (Other (BlockStart x y z))) vn val =  
  case val of 
    EInt v -> NOP (Other (BlockStart { env = M.insert vn v x ,bend = y , envpar= z}))
    EPar v -> NOP (Other (BlockStart { env = x ,bend = y , envpar= M.insert vn v z}))
  

updateRoboMem :: InterpreterState -> Int -> Robo   
updateRoboMem (InterpreterState i p f (Robo id rc mem) c) val = Robo id rc val

{--
extractFromEPar :: EnvValue ->  (VariableName,[Expr1])
extractFromEPar (EPar x) = x

extractFromEInt :: EnvValue -> Int
extractFromEInt (EInt x) = x
--}
updateFSorBS :: Instruction ->  String -> EnvValue -> Expr -> Instruction  
updateFSorBS (NOP (Other (FunctionStart x y z ))) vn val expr =  
  case expr of 
    FuncCall _ _  -> case val of  
                           EInt _ ->   NOP (Other (FunctionStart {fs = x, env = y , envpar=z })) 
                           EPar v -> NOP (Other (FunctionStart {fs = x, env = y , envpar=M.insert vn v z })) 
    _              ->  case  val of 
                        EInt v -> NOP (Other (FunctionStart {fs = x, env = M.insert vn v y , envpar=z })) 
                        EPar v -> NOP (Other (FunctionStart {fs = x, env = y , envpar=M.insert vn v z })) 

updateFSorBS (NOP (Other (BlockStart x y z))) vn val expr = 
 case expr of
  FuncCall _ _ -> case val of 
                        EInt _ ->   NOP (Other (BlockStart {env = x, bend = y , envpar=z })) 
                        EPar v -> NOP (Other (BlockStart {env = x, bend = y , envpar=M.insert vn v z })) 
  _              -> case val of 
                       EInt v -> NOP (Other (BlockStart { env = M.insert vn v x ,bend = y , envpar= z}))
                       EPar v -> NOP (Other (BlockStart { env = x ,bend = y , envpar= M.insert vn v z}))

addEnvVar :: EnvValue -> EnvValue -> EnvValue
addEnvVar (EInt x) (EInt y) = EInt (x+y)
addEnvVar (EInt x)  _       = NIL
addEnvVar _        (EInt x) = NIL

evaluate :: Expr -> InterpreterState -> (EnvValue,InterpreterState) 
evaluate (Val1 x) intStat = (EInt x,intStat)
evaluate (SingleVar x) intStat= (getValueFromContext intStat x,intStat)
evaluate (Add (Var x) (Val y)) intStat= (addEnvVar v1 (EInt y) , intStat)
                               where 
                                 v1 = getValueFromContext intStat x
evaluate (Add (Var x) (Var y)) intStat= (addEnvVar v1 v2,intStat)
                                where 
                                 v1 = getValueFromContext intStat x
                                 v2 = getValueFromContext intStat x

evaluate (FuncCall fname par) intStat = -- getValueFromContext intStat fname 
  case  getValueFromContext intStat fname of 
      EInt x -> (NIL,intStat)  
      EPar ( oriFunName , lstArg ) -> case length $ checkFunctionExist oriFunName instList of
                                        1 -> case (head$checkFunctionExist oriFunName instList) of
                                              ((NOP (Other (FunctionDef nm fdArg rtype))),_) -> 
                                                                                          case (length$fdArg) == (length$currentParamList) of
                                                                                             True -> case executeJumpC intStat jmpinst1 of  
                                                                                                       Nothing -> (NIL,intStat)                
                                                                                                       Just updatedStat -> (EInt 11,updatedStat)
                                                                                             False -> (EPar (oriFunName,currentParamList),intStat{pointer = (instptr + 1)})
                                 where 
                                  currentParamList = lstArg ++ par
                                  jmpinst1 = JumpC { jc = snd$head(checkFunctionStartExist oriFunName instList) , fn = oriFunName  , param= currentParamList }
                                  jln      = snd$head(checkFunctionExist oriFunName instList)
      NIL        -> case length$checkFunctionExist fname instList of 
                      1 -> case head$(checkFunctionExist fname instList) of 
                                ((NOP (Other (FunctionDef nm fdArg rtype))),_) -> 
                                                                     case (length$fdArg) == (length$par) of
                                                                        True -> case executeJumpC intStat jmpinst2 of  
                                                                                  Nothing -> (NIL,intStat)                                    
                                                                                  Just x  -> (EInt 10 , x)
                                                                        False -> (EPar (nm,par),intStat {pointer = instptr + 1 })
                      _ -> (NIL,intStat)
  
  where 
    jmpinst2 = JumpC { jc = snd$head(checkFunctionStartExist fname instList), fn = fname  , param= par }
    instList = zip (fst <$> (insStr intStat)) [0..]
    instptr = pointer intStat 
       
checkFunctionExist :: FunctionName -> [(Instruction,Int)] -> [(Instruction,Int)]
checkFunctionExist oriFunName instList= filter (\x -> case fst$x of {(NOP(Other (FunctionDef fname y z))) -> fname==oriFunName  ; _ -> False}) (instList)


checkFunctionStartExist :: FunctionName -> [(Instruction,Int)] -> [(Instruction,Int)]
checkFunctionStartExist oriFunName instList= filter (\x -> case fst$x of {(NOP(Other (FunctionStart fname y z))) -> fname==oriFunName  ; _ -> False}) (instList)

extractFromMaybe1 :: Maybe Int  -> EnvValue
extractFromMaybe1 (Just x) = EInt x
extractFromMaybe1 Nothing  = NIL

extractFromMaybe2 :: Maybe (FunctionName,[Expr1])  -> EnvValue
extractFromMaybe2 (Just x) = EPar x
extractFromMaybe2 Nothing  = NIL


getValueFromContext :: InterpreterState -> String -> EnvValue 
getValueFromContext intStat var = 
  case length $ context of 
   0 -> NIL
   _ ->  
    case fst (head$context) of 
     NOP (Other (FunctionStart x y z )) -> 
       case isPresentInEnv var (fst$head$context) ENV of 
            True ->   extractFromMaybe1 $ M.lookup var y  
            False ->  extractFromMaybe2 $ M.lookup var z  
     NOP (Other (BlockStart x y z))      -> 
       case isPresentInEnv var (fst$head$context) ENV of 
            True ->  extractFromMaybe1 $ M.lookup var x 
            False -> extractFromMaybe2 $  M.lookup var z  
 where
         context = getAppropriateContext cntxList ptr var
         cntxList = findContextList instList ptr var
         ptr = pointer intStat 
         instList = (map fst (insStr intStat))

getAppropriateContext :: [(Instruction,Int)] -> Int -> String -> [(Instruction,Int)]
getAppropriateContext instWithLn ln var =  
   case checkBlockEnd of 
     True  -> [(instWithLn !! (ylen2-1))]
     False ->  case length$instWithLn of
       1 -> case (boolV || boolPV) of
         True  -> [(instWithLn !! (ylen2-1))]
         False -> []
       _ -> getAppropriateContext (getUpperContext instWithLn) ln var
  where 
    ylen2      = length $ instWithLn
    boolV      = isPresentInEnv var (fst $ (instWithLn !! (ylen2 -1))) ENV 
    boolPV      = isPresentInEnv var (fst $ (instWithLn !! (ylen2 -1))) ParENV 
    lstinst    = instWithLn !! (ylen2 -1)
    checkBlockEnd = case (fst $ lstinst) of 
        (NOP (Other (BlockStart env bend parenv))) -> bend > ln && ( boolV || boolPV)
        _                                    -> False




getUpperContext :: [(Instruction,Int)] -> [(Instruction,Int)]
getUpperContext instWithLn = case ele of 
                               (NOP (Other (FunctionStart x y z )),ln) -> [instWithLn !! (ylen2 -2)]
                               ((If x y z),ln)                      -> takeWhile (\x-> (snd x) < (y-1)) instWithLn 
                               ( NOP Else ,ln)                      -> takeWhile (\x -> (fst x) /= (corrIfInst instWithLn (ln+1)))  instWithLn
           where 
            ylen2          = length(instWithLn)
            ele            = instWithLn !! (ylen2 -2)

corrIfInst instWithLn ln = head$filter (\x1 -> (case x1 of { (If x y z) -> case z==ln of {(True) -> True; (_)->False } ; _ -> False})) inst
                 where
                   inst = (map fst instWithLn)

       
isPresentInEnv :: VariableName -> Instruction -> EnvType -> Bool
isPresentInEnv var x envtype = case (x) of 
                         NOP (Other (FunctionStart x y z )) -> case envtype of 
                                                                ENV ->  M.member var y
                                                                ParENV ->  M.member var z 
                         NOP (Other (BlockStart x y z))    -> case envtype of 
                                                                ENV ->   M.member var x 
                                                                ParENV ->   M.member var z


findContextList :: [Instruction] -> Int -> String -> [(Instruction,Int)]
findContextList xs y vna =  f $ contextHolderList
   where 
    contextHolderList = filter  (\ (ins,idx) -> case ins of 
                                                 NOP (Other (FunctionStart x y z)) -> True
                                                 NOP (Other (BlockStart x y z))      -> True
                                                 If x y z                        -> True
                                                 NOP Else                        -> True
                                                 _                               -> False) inst
    lengthOfContextList = length$ contextHolderList 
    inst = zip (take y (xs)) [0..]


f ls =  reverse  (take ((length pp)+1) (reverse ls))
 where
  pp =  takeWhile  (\ (x,y) -> case x of {(NOP (Other (FunctionStart x y z))) -> False; (_)-> True}) (reverse ls)


findContext :: InterpreterState -> Int 
findContext intprState = snd$cntx                
   where 
    contextHolderList = filter  (\ (ins,idx) -> case ins of 
                                                 NOP (Other (FunctionStart x y z)) -> True
                                                 NOP (Other (BlockStart x y z))   -> True
                                                 _                               -> False) inst
    lst   =  map (\x -> isInstructionInBlock x intprState) contextHolderList 
    cntx  = fst$minimumBy (\(_,a) (_,b) -> compare a b) (filter (\x -> (snd$x) /= -1) lst)
    inst  = zip (map fst (insStr intprState)) [0..]
    asgnIdx = pointer intprState
    


isInstructionInBlock :: (Instruction,Int)-> InterpreterState -> ((Instruction,Int),Int)
isInstructionInBlock instWithLn intprState = 
  case fst $ instWithLn of 
   NOP (Other (BlockStart x bend z)) -> 
     case (bend >= asgnIdx)  && ((snd$instWithLn) <= asgnIdx) of
       True -> (instWithLn,numberOfInstructionIn instList (snd$instWithLn) bend )
       False -> (instWithLn,-1)
   NOP (Other (FunctionStart x y z)) ->  
     case (funcStartLineNumber <= asgnIdx) && (funcEndLineNumber >= asgnIdx) of
       True -> (instWithLn,numberOfInstructionIn instList (snd$instWithLn) funcEndLineNumber)
       False -> (instWithLn,-1)
 where
   funcEndLineNumber =  case (M.lookup (funcStartLineNumber) (funcTab intprState))of { Nothing -> -1 ; Just x -> x}
   funcStartLineNumber = snd $ instWithLn 
   asgnIdx = pointer intprState
   instList = zip (map fst (insStr intprState)) [0..]
   

numberOfInstructionIn :: [(Instruction,Int)] -> Int -> Int -> Int
numberOfInstructionIn instWithLn rangeStart rangeStop = length $ filter (\x ->  (rangeStart < (snd$x))  && ((snd$x) < rangeStop)) instWithLn
                                             
                                           
 

{--
getCurrentContextHolder :: [(Instruction,Int)] -> InterpreterState -> (Instruction,Int)
getCurrentContextHolder cntxList intprStat =  
   case checkBlockEnd of
     True  -> lstInst
     False -> getUpperContext cntxList  
                                         
  where 
    cntxListLen      = length $ cntxList 
    lstInst    = cntxList !! (cntxListLen - 1)
    checkBlockEnd = case (fst $ lstinst) of 
        (NOP (Other (BlockStart env bend ))) -> bend > (pointer intprStat)
        _                                    -> False
--}

sendRequest :: InterpreterState -> IO ()
sendRequest intprState = case getCurrentInstruction intprState of
                           Move x -> sendTo (comm intprState) ([head $ show x]) 
                           Read -> sendTo (comm intprState) "Read"
                           Write -> sendTo (comm intprState) ("Write (" ++ (show $ roboColor (robo intprState)) ++"," ++(show $ mem (robo intprState))++")")
                           FlipPassable -> sendTo (comm intprState) "FP"
                           FlipWritable -> sendTo (comm intprState) "FW"

getParamsValues :: [Expr1] -> Instruction -> InterpreterState -> [(VariableName,EnvValue)]
getParamsValues paramList (NOP (Other (FunctionDef x y z))) intprState =  parameterList  <$> (zip paramList y )
    where 
        parameterList = (\(p,(typ,varname)) -> 
          case p of 
            Val x -> (varname,EInt x)
            Var y ->
                case getValueFromContext intprState y of
                    EInt x -> 
                      case typ of
                        INT -> (varname,EInt x)
                        _   -> (varname,NIL)
                    EPar x -> case typ of
                                 FUNC -> (varname,EPar x)
                                 _   -> (varname,NIL)
                    NIL    -> (varname,NIL)
                            ) 
        
                        

executeJumpC :: InterpreterState -> Instruction -> Maybe InterpreterState
executeJumpC intprState (JumpC i fname par)  =  
  case (length$checkFunctionExist) of
    1 -> case (length (getargument)) == (length $ par) && checkValidParameter of
          True -> Just (intprState { insStr = updateFuncInst , pointer = i })
          False -> Nothing  
    _ -> Nothing --}
 where
    checkFunctionExist = filter (\x -> case fst$x of {(NOP(Other (FunctionDef w y z))) -> fname==w ; _ -> False}) (instList)
    eoFuncPointer = M.findWithDefault (-1) i (funcTab intprState)
    retListUpdated = intprState { insStr = listUpdate (insStr intprState)
                                         ((\(ins,s)-> (ins {retList = (retList ins) ++ [(pointer intprState +1,contextStore)]},s)) $
                                          (insStr intprState)!!eoFuncPointer)
                                         eoFuncPointer }
    contextRange = head$filter (\(s,e) -> s < returnAddr && e > returnAddr)    (M.toList (funcTab intprState))
    contextRangeCalledFunction = head$filter (\(s,e) -> s <= i && i < e)  (M.toList (funcTab intprState))
    contextStore = take ((snd$contextRange)- (fst$contextRange) ) (drop (fst$contextRange) (insStr intprState))
    returnAddr = pointer intprState 
    instList = zip (fst <$> (insStr intprState)) [0..]
    updateFuncInst = map (\(inst,index) -> 
                        case (fst$contextRangeCalledFunction) <= index && index < (snd$contextRangeCalledFunction) of
                         True  -> case (fst$inst) of 
                           -- if instruction is asgn = func(arg..) then in that clear flag = uncalled
                           NOP (Other (FunctionStart x y z)) -> (NOP( Other (FunctionStart { fs = x , env = (M.fromList filterIntFromEnvList) ,envpar = (M.fromList filterFuncFromEnvList)})) ,snd$inst)
                      --(NOP (Other (FunctionStart x (M.fromList filterIntFromEnvList) (M.fromList filterFuncFromEnvList))),snd$inst)
                           NOP (Other ( BlockStart p q r))   -> (NOP ( Other (BlockStart  (M.fromList []) q (M.fromList []))),snd$inst) 
                           m                   -> (m,snd$inst)
                         False ->  inst 
                         ) newupdatelist
    newupdatelist  = (zip (insStr retListUpdated) [0..])
    getargument = case (fst(checkFunctionExist!!0)) of 
                       NOP (Other (FunctionDef x y z)) -> y
    envValueList = getParamsValues par (fst(checkFunctionExist!!0)) intprState -- -> [(VariableName,EnvValue)]
    intparameterList = filter (\(x,y) -> case y of {EInt p -> True;_ -> False} ) envValueList 
    funcparameterList = filter (\(x,y)-> case y of {EPar p -> True;_ -> False} ) envValueList 
    filterIntFromEnvList = map (\(x,y) -> case y of {EInt p -> (x,p) }) intparameterList
    filterFuncFromEnvList = map (\(x,y) -> case y of {EPar p -> (x,p) }) funcparameterList
    checkValidParameter =  and $  map (\(x,y) -> case y of {NIL -> False;_ -> True}) envValueList   

executeEOFunc :: InterpreterState -> InterpreterState
executeEOFunc intprState = state1 { insStr = restorePrevContext }
  where
    currStr = getCurrentString intprState
    currIns = getCurrentInstruction intprState
    prevFunctionContext =  last $ retList currIns  
    state1 = intprState { pointer = fst $ prevFunctionContext } 
    newInsStr = listUpdate (insStr state1) (currIns {retList = init $ retList currIns}, currStr) (pointer intprState)
    returnAddr = fst $ prevFunctionContext 
    contextRange = head$filter (\(s,e) -> s < returnAddr && e > returnAddr)    (M.toList (funcTab intprState))
    restorePrevContext = (take ((fst $ contextRange )) newInsStr) ++ (snd $ prevFunctionContext ) ++ (drop (snd$contextRange) newInsStr)   
    
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
                          FunctionStart s _ z-> True
                          EndOfFunction s r -> True
                          _ -> False ) (zip [0..] xs)

getStartPoint :: [(Int,Instruction)] -> Int
getStartPoint xs = (\[(i,ins)]-> i) $ filter (\ (i,ins)-> ins == (FunctionStart "main" (M.fromList []) (M.fromList []))) xs

toFuncEOFmap :: [(Int,Instruction)] -> [(Int,Int)]
toFuncEOFmap xs = if xs == [] then [] else [(\xss-> (fst (xss!!0), fst (xss!!1))) $ (take 2 xs)] ++ toFuncEOFmap (drop 2 xs)

---------------------------------Instruction Conversion/Jump Resolution--------------------------------

finally :: [Instruction] -> [Instruction]
finally xs = map (\x-> case x of
                         FunctionDef z m n -> NOP (Other $  FunctionDef z m n)
                         FunctionStart z x y -> NOP (Other $  FunctionStart z x y)
                         BlockStart y z x-> NOP ( Other $ BlockStart y z x)
                         z -> z ) xs

resolveFunctionCalls :: [Instruction] -> [Instruction]
resolveFunctionCalls xs = foldl (\iList (ins,index)-> listUpdate iList (JumpC (nextIndex (FunctionStart (fc ins) (M.fromList []) (M.fromList [])) iList) (fc ins) (param ins) ) index) xs functionCallIndices 
  where
    functionCallIndices = filter (\(ins,index)-> case ins of
                                           FunctionCall x y -> True
                                           _ -> False) $  zip xs [0..]

resolveAsgnStmt :: [Instruction]-> [Instruction]
resolveAsgnStmt xs = asgnStmtIndices  
  where
    asgnStmtIndices = map (\(ins,index)-> case ins of
                                           Asgn { asgnLn = x , vn =y , expr= e} -> Asgn {asgnLn = index+1 ,vn=y ,expr=e}
                                           n -> n ) $  zip xs [0..]

resolveReturn :: [Instruction] -> [Instruction]
resolveReturn xs = foldl (\iList (ins,index)-> listUpdate iList (Jump (nextEOFuncIndex index iList) (RETURN) (retval$ ins)) index) xs functionCallIndices 
  where
    functionCallIndices = filter (\(ins,index)-> case ins of
                                           Return _ -> True
                                           _ -> False) $  zip xs [0..]

--findMatching :: Eq a => a -> a -> Int -> [a] -> Int -> Int
findMatching x y 0 xs n = n
findMatching x y i [] n = -1
findMatching x y i xs n | x == head xs = findMatching x y (i-1) (tail xs) (n+1)
                        | compare_y = findMatching x y (i+1) (tail xs) (n+1)
                        | otherwise = findMatching x y i (tail xs) (n+1)
                         where
                           compare_y = case y of 
                                       BlockStart m n v -> case head xs of
                                                         BlockStart m q r -> True
                                                         _              -> False
                                       g            -> g == head xs

getSource :: String -> [Instruction]
getSource str = if lefts parsedLines == [] then rights parsedLines else (map (\x->error $ show x) $ lefts parsedLines)
  where
    parsedLines = map (parser instructionParser) (lines str)

listUpdate :: [a] -> a -> Int -> [a]
listUpdate xs x i = take i xs ++  [x] ++ drop (i+1) xs 

--nextIndex :: Eq a => a -> [a] -> Int
nextIndex x xs = case x of 
                 BlockStart y z w-> maybe (error "Syntax Error x y ") Prelude.id (findIndex (\p-> case p of {BlockStart _  _ _ -> True;_ -> False}) xs)
                 _              -> maybe (error "Syntax Error x y ") Prelude.id (findIndex (==x) xs)


-- listUpdate :: list -> element -> index -> list

verifyFunctions :: [Instruction] -> [Instruction]
verifyFunctions xs = foldl (\iList (ins,index)-> listUpdate (listUpdate iList (FunctionStart (fd ins) (M.fromList []) (M.fromList [])) (nextOpIndex index iList)) 
                       (EndOfFunction (fd ins) []) (findMatching (NOP ClBrace) (NOP OpBrace) 1 (drop (1+nextOpIndex index iList) iList)
                        (nextOpIndex index iList))) xs fDefIndices 
  where
    fDefIndices = filter (\(ins,index)-> case ins of
                                           FunctionDef x y z -> True
                                           _ -> False) $  zip xs [0..]

{--
verifyIfs :: [Instruction] -> [Instruction]
verifyIfs xs = foldl (\iList (ins,index)-> listUpdate (listUpdate iList (BlockStart   {env = (M.fromList [])}   ) (nextOpIndex index iList)) BlockEnd (findMatching (NOP ClBrace) (NOP OpBrace) 1 (drop (1+nextOpIndex index iList) iList) (nextOpIndex index iList))) xs ifInterIndices 
  where
    ifInterIndices = filter (\(ins,index)-> case ins of
                                           IfIntermediate x -> True
                                           --FunctionDef x -> True
                                           _ -> False) $  zip xs [0..]

--}

verifyIfs :: [Instruction] -> [Instruction]
verifyIfs xs = foldl (\iList (ins,index) -> listUpdate (listUpdate iList (BlockStart {env = (M.fromList []),bend = (lnMatchingBlockEnd index iList) ,envpar = (M.fromList [])}) (nextOpIndex index iList)) BlockEnd (lnMatchingBlockEnd index iList) ) xs ifInterIndices 
  where
    --lnMatchingBlockEnd = ( findMatching (NOP ClBrace) (NOP OpBrace) 1 (drop (1+nextOpIndex index iList) iList) (nextOpIndex index iList) )
    ifInterIndices = filter (\(ins,index)-> case ins of
                                           IfIntermediate x -> True
                                           --FunctionDef x -> True
                                           _ -> False) $  zip xs [0..]

lnMatchingBlockEnd index iList = ( findMatching (NOP ClBrace) (NOP OpBrace) 1 (drop (1+nextOpIndex index iList) iList) (nextOpIndex index iList) )


ifJumpResolve :: [Instruction] -> [Instruction]
ifJumpResolve xs = foldl (\iList (ins,index)-> listUpdate (listUpdate iList (Jump (blockEndIndex index iList) (IF) (NULL) ) (findMatching (BlockEnd) (BlockStart {env= (M.fromList []),bend = (lnMatchingBlockEnd index iList),envpar = (M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList))) (Jump (blockEndIndex index iList) (IF) (NULL)) (findMatching (BlockEnd) (BlockStart {env = (M.fromList []),bend = (lnMatchingBlockEnd index iList),envpar = (M.fromList [])}) 1 (drop (1+ nextBSIndex (1+(findMatching (BlockEnd) (BlockStart {env= (M.fromList []),bend=lnMatchingBlockEnd index iList ,envpar = (M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList))) iList) iList) (nextBSIndex (1+(findMatching (BlockEnd) (BlockStart {env =(M.fromList []),bend = (lnMatchingBlockEnd index iList),envpar = (M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList))) iList))) ifInterToIf ifInterIndices1
  where
    ifInterToIf = foldl (\iList (ins,index)-> listUpdate iList (If (ifinter ins) (nextBSIndex index iList) (nextBSIndex (findMatching BlockEnd (BlockStart {env =(M.fromList []),bend = (lnMatchingBlockEnd index iList),envpar = (M.fromList [])}) 1 (drop (1+nextBSIndex index iList) iList) (nextBSIndex index iList)) iList)) index) xs ifInterIndices1
    ifInterIndices1 = filter (\(ins,index)-> case ins of
                                           IfIntermediate x -> True
                                           _ -> False) $  zip xs [0..]


blockEndIndex ind il = 1+findMatching (BlockEnd) (BlockStart {env= (M.fromList []),bend = 0,envpar = (M.fromList [])}) 1 (drop (1+ nextBSIndex (1+ifend) il) il) (nextBSIndex (1+ifend) il)
  where
    ifend = (findMatching (BlockEnd) (BlockStart  {env= (M.fromList []),bend = 0,envpar = (M.fromList [])}) 1 (drop (1+nextBSIndex ind il) il) (nextBSIndex ind il))

nextEOFuncIndex :: Int -> [Instruction] -> Int
nextEOFuncIndex i xs = i + (head $ fst $ unzip $ getEofs)
  where
    getEofs = filter (\x-> case x of
                             (index,EndOfFunction n rl) -> True
                             (index,_) -> False ) $ zip [1..] (drop (i+1) xs)

nextOpIndex :: Int -> [Instruction] -> Int
nextOpIndex ind il = 1 + ind + nextIndex (NOP OpBrace) (drop (ind+1) il)

nextBSIndex :: Int -> [Instruction] -> Int
nextBSIndex ind il = 1 + ind + nextIndex (BlockStart {env= (M.fromList []),bend = 0,envpar = (M.fromList [])}) (drop (ind+1) il)

nextBEIndex :: Int -> [Instruction] -> Int
nextBEIndex ind il = 1 + ind + nextIndex BlockEnd (drop (ind+1) il)

--------------------Parser------------------

languageDef :: LanguageDef u
languageDef = emptyDef { Token.identStart = letter <|> satisfy (=='_')
                       , Token.identLetter = alphaNum
                       , Token.reservedNames = ["void","int","func","move","up","left","right","down","read","write","main","return","if","else","return","setmem","getmem"]
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
             try' functioncallparser <|>
             try' exprparser <|>
             try' singlevarparser 


  where
    getmemparser =  (whiteSpace >> ((\x-> GetMem1) <$> string "getmem")) 
    singlevarparser = whiteSpace >> try'( ((\x -> Val1 (read $show x:: Int)) <$> natural) <|> ((\x -> SingleVar x) <$> many1 alphaNum))
    exprparser = liftA2 (\x y -> Add (Var x) (Val (read $ show y ::Int))) varnameparser intparser
    varnameparser = (whiteSpace >> many1 alphaNum) 
    intparser = (whiteSpace >> string "+" >> whiteSpace >> natural)
    functioncallparser = (whiteSpace >> liftA2 (\x y-> FuncCall x y) (many1 alphaNum) (parens paramListParser))
    paramListParser     = sepBy singlevarparser1 commaSeperator  
    singlevarparser1 = ( whiteSpace >> ((\x -> Val (read $show x:: Int)) <$> (whiteSpace >> natural <* whiteSpace))) <|>(((\x -> Var x) <$> (whiteSpace >> (many1 alphaNum <* whiteSpace))))
    
returnParser :: Parser Instruction
returnParser = whiteSpace >> reserved "return" >> singlevarparser 
  where
    singlevarparser = ( whiteSpace >> ((\x -> Return (Val (read $show x:: Int))) <$> (whiteSpace >> natural <* whiteSpace))) <|>
                      (((\x -> Return (Var x)) <$> (whiteSpace >> (many1 alphaNum <* whiteSpace)))) <|> 
                      (((\x -> Return (NULL)) <$> (whiteSpace >> parens (string "")))) 

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
                   (reserved "func" >> return FUNC)<|>
                   (reserved "void" >> return VOID)

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
