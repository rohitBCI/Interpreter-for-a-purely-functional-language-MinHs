--Rohit Vijayakumar (9145281)

module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Debug.Trace

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           | Expr Exp
           | Closure Environment Exp
           deriving (Show,Eq)

data VCurrentState = CurrentStateExp Exp
                   | CurrentStateVal Value
                   deriving(Show,Eq)

data VStack = BinOpArg1 Exp
            | BinOpArg2 Exp
            | BinOpArg3 Exp Exp
            | AppFunc Exp
            | AppFuncArg Exp
            | EnvStack Environment 
            | AppClosure Environment Exp         
            deriving(Show,Eq)

type Stack = [VStack]

type VEnv = E.Env Value
type BindEnv = E.Env Bind

type Environment = (VEnv,BindEnv)

data MachineState = MSevaluate Stack Environment VCurrentState Integer 
                  | MScalculate Stack Environment VCurrentState Integer
                  deriving(Show,Eq)


--Auxillary Functions
frameToExp :: VStack -> Exp
frameToExp frame  = case frame of
  BinOpArg1 expr -> expr
  BinOpArg2 expr -> expr
  AppFunc expr -> expr

stateToExp :: VCurrentState -> Exp
stateToExp state = case state of
  CurrentStateExp (expr) -> expr
  CurrentStateVal (value) -> case value of
    I n -> Num n
    B True -> Con "True"
    B False -> Con "False"

stateToVal :: VCurrentState -> Value
stateToVal state = case state of
  CurrentStateVal (value) -> case value of
    I n -> I n
    B True -> B True  
    B False -> B False

frameToFunc :: VStack -> Id
frameToFunc (AppFunc(Recfun(Bind var1 typ var2 body))) = var1 

frameToBind :: VStack -> Bind
frameToBind (AppFunc(Recfun(Bind var1 typ var2 body))) = (Bind var1 typ var2 body)

frameToBinding :: VStack -> Id
frameToBinding (AppFunc(Recfun(Bind var1 typ var2 body))) = case var2 of
  [binding] -> binding

frameToId :: [Id] -> Id
frameToId [v] = v

frameToBody :: VStack -> Exp
frameToBody (AppFunc(Recfun(Bind var1 typ var2 body))) = body

maybeToval :: Maybe Value -> Exp
maybeToval v = case v of
  Just val -> case val of
    I n -> Num n
    B True -> Con "True"
    B False -> Con "False"
  Nothing -> error "Variable not in environment"

maybeToExp :: Maybe Bind -> Exp
maybeToExp v = case v of
  Just (Bind var1 typ var2 body) -> body
  Nothing -> error "Variable not in environment"

stackEnvToEnv :: VStack -> Environment
stackEnvToEnv (EnvStack (v,e)) = (v,e)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)


  -- do not change this definition
evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE e

-- do not change this definition
evalE :: Exp -> Value
evalE exp = loop (msInitialState exp)
  where 
    loop ms = --(trace (show newMsState)) $
             if (msInFinalState newMsState)
                then msGetValue newMsState
                else loop newMsState
              where
                 newMsState = msStep ms


msInitialState :: Exp -> MachineState
msInitialState state = MScalculate [] (E.empty, E.empty) (CurrentStateExp state) 0


-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState (MSevaluate stack (vEnv,bindEnv) currentExp iter_count) = case iter_count of
  300000 -> error "Out of bounds"
  _ -> case stack of
      [] -> case currentExp of
            CurrentStateVal value -> case value of
                              B True -> True
                              B False -> True
                              Nil -> True
                              I n -> True
                              Cons n e -> True
            CurrentStateExp expr -> case expr of
               Con str -> case str of
                "True" -> True
                "False" -> True
                "Nil" -> True
      _ -> False
    
msInFinalState (MScalculate stack (vEnv,bindEnv) currentExp iter_count) = case iter_count of
  300000 -> error "Out of bounds"
  _ -> False

-- returns the final value, if machine in final state, Nothing otherwise
msGetValue :: MachineState -> Value
msGetValue (MSevaluate _ _ currentExp iter_count) = case currentExp of
  CurrentStateVal value -> case value of
                     B True -> B True
                     B False -> B False
                     Nil ->  Nil
                     I n -> I n
                     (Cons n e) -> Cons n e


--Calculation mode
msStep :: MachineState -> MachineState
msStep (MScalculate stack (vEnv,bindEnv) currentExp iter_count) = do
  let iteration = iter_count + 1
  case currentExp of

    --Basic values
    CurrentStateExp (Con str) ->  case str of
                      "True" -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B True)) iteration
                      "False" -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B False)) iteration
                      "Nil" ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal Nil) iteration

    CurrentStateExp (Num n) ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I n)) iteration

    
    --List operations
    CurrentStateExp(App (Prim Head) e2) -> case e2 of
      Con "Nil" -> error "list is empty"
      App (App (Con "Cons") (Num n)) e2 -> MSevaluate stack (vEnv,bindEnv) currentExp iteration
                                            where
                                              currentExp = CurrentStateVal (I n)
    CurrentStateExp(App (Prim Tail) e2) -> case e2 of
        Con "Nil" -> error "list is empty"
        App (App (Con "Cons") (Num n)) e2 -> case e2 of
          Con "Nil" -> MSevaluate stack (vEnv,bindEnv) currentExp iteration
                        where
                          currentExp = CurrentStateVal (Cons n Nil)
  
    CurrentStateExp(App (Prim Null) e2) -> case e2 of
      Con "Nil" ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B True)) iteration
      _ ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B False)) iteration

      
    --Binary operations
    CurrentStateExp (App (App (Prim op) (Num num1)) (Num num2))  ->  case op of
      Add -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (num1 + num2))) iteration
      Sub -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (num1 - num2))) iteration
      Mul -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (num1 * num2))) iteration
      Quot -> if num2 == 0
            then error "Division by zero"
            else MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (quot num1 num2))) iteration
      Gt -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 > num2))) iteration
      Ge -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 >= num2))) iteration
      Lt -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 < num2))) iteration
      Le -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 <= num2))) iteration
      Eq -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 == num2))) iteration
      Ne -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 /= num2))) iteration

    CurrentStateExp (App(Prim Neg) (Num num1)) -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (negate num1))) iteration

    CurrentStateExp (App (Prim op) (Num num1)) ->  MScalculate (update:frames) (vEnv,bindEnv) currentExp iteration
                                                      where
                                                        pop = head stack
                                                        arg2 = frameToExp pop
                                                        update = BinOpArg1 (App (Prim op) (Num num1))
                                                        frames = tail stack
                                                        currentExp = CurrentStateExp (arg2)

    CurrentStateExp (App (Prim op) expr2) -> MScalculate (update:frames) (vEnv,bindEnv) currentExp iteration
                                              where
                                                update = BinOpArg1 (Prim op)
                                                frames = stack
                                                currentExp = CurrentStateExp (expr2)

    CurrentStateExp (App(App(Prim op) (Var ch)) (Num n)) -> MScalculate stack (vEnv,bindEnv) currentExp iteration
                                                             where
                                                               lookupEnv = E.lookup vEnv ch
                                                               value = maybeToval lookupEnv
                                                               currentExp = CurrentStateExp (App(App(Prim op) (value)) (Num n))
                                                          
    CurrentStateExp (App expr1 expr2) -> MScalculate (update:frames) (vEnv,bindEnv) currentExp iteration
                                          where
                                            update = BinOpArg2 expr2
                                            frames = stack
                                            currentExp = CurrentStateExp (expr1)
    
    --If then else operation
    CurrentStateExp (If e1 e2 e3) -> case e1 of
      Con str -> case str of
        "True" -> MScalculate stack (vEnv,bindEnv) (CurrentStateExp e2) iteration
        "False" -> MScalculate stack (vEnv,bindEnv) (CurrentStateExp e3) iteration
      _ -> MScalculate (update:frames) (vEnv,bindEnv) (CurrentStateExp e1) iteration
            where
              update = BinOpArg3 e2 e3
              frames = stack
    
    --Function operations
    CurrentStateExp (Recfun (Bind var1 typ var2 body)) -> case (head stack) of 
      EnvStack (c1,c2) -> MScalculate frames (vEnv,bindEnv) currentExp iteration
                            where
                              bundle = Closure (vEnv1,bindEnv1) (Recfun (Bind var1 typ var2 body))
                              vEnv1 = vEnv 
                              bindEnv1 = bindEnv
                              frames = tail stack
                              currentExp = CurrentStateVal bundle

      _ -> MScalculate (update:frames) (vEnv,bindEnv) currentExp iteration
            where
              pop = head stack
              arg2 = frameToExp pop
              update = AppFunc (Recfun (Bind var1 typ var2 body))
              frames = tail stack
              currentExp = CurrentStateExp (arg2)
      
    CurrentStateVal (Closure(c1,c2) expr) -> case (head stack) of
      BinOpArg2 (Num n) -> MScalculate (update:frames) (vEnv,bindEnv) currentExp iteration
                                              where
                                                update = AppClosure (c1,c2) expr
                                                frames = tail stack
                                                currentExp = CurrentStateExp (Num n)
      EnvStack (c1,c2) -> MScalculate (frames) (vEnv,bindEnv) currentExp iteration
                            where
                              frames = tail stack

    --Variable operations
    CurrentStateExp (Var var1) ->  case (E.lookup vEnv var1) of
      Just v -> MScalculate stack (vEnv,bindEnv) currentExp iteration
                  where
                    lookupEnv = E.lookup vEnv (var1)
                    value = maybeToval lookupEnv
                    currentExp = CurrentStateExp (value)

      Nothing -> case (E.lookup bindEnv var1) of
        Just v -> MScalculate stack (vEnv,bindEnv) currentExp iteration
                    where
                      lookupEnv = E.lookup bindEnv (var1)
                      value = maybeToExp lookupEnv
                      currentExp = CurrentStateExp (value)                                                        

    CurrentStateExp (Let[Bind var1 typ var2 body] expr) -> MScalculate stack (vEnv,(E.add bindEnv (var1,(Bind var1 typ var2 body)))) currentExp iteration
                                                            where
                                                              currentExp = CurrentStateExp expr

--Evaluation mode
msStep (MSevaluate stack (vEnv,bindEnv) currentExp iter_count) = do
  let iteration = iter_count + 1
  case (B (length(stack) > 0)) of
    B True -> case (head stack) of
      AppClosure (c1,c2) expr -> case expr of
        Recfun (Bind var1 typ var2 body) -> case var2 of
          [] -> MScalculate (update:frames) ((E.add vEnv (var1,value)),bindEnv) (CurrentStateExp (body)) iteration
                  where
                    oldEnv = (vEnv,bindEnv)
                    pop = head stack
                    update = EnvStack oldEnv
                    frames = tail stack
                    value = stateToVal currentExp
          _ -> MScalculate (update:frames) ((E.add vEnv (bindVal,value)),bindEnv) (CurrentStateExp (body)) iteration
                where
                  oldEnv = (vEnv,bindEnv)
                  pop = head stack
                  update = EnvStack oldEnv
                  frames = tail stack
                  value = stateToVal currentExp
                  bindVal = frameToId var2
                                                                     
      AppFunc expr -> MScalculate (update:frames) ((E.add vEnv (bindVal,value)),(E.add bindEnv(func,binding))) (CurrentStateExp (body)) iteration
                          where
                            oldEnv = (vEnv,bindEnv)
                            pop = head stack
                            update = EnvStack oldEnv
                            frames = tail stack
                            func = frameToFunc pop
                            binding = frameToBind pop
                            bindVal = frameToBinding pop
                            body = frameToBody pop
                            value = stateToVal currentExp      

      EnvStack expr -> case length(tail(stack)) of
        0 -> MSevaluate [] (E.empty,E.empty) currentExp iteration
        _ -> MScalculate frames newenv currentExp iteration
                          where
                            pop = head stack
                            newenv = stackEnvToEnv pop
                            frames = tail stack
      BinOpArg1 arg -> MScalculate frames (vEnv,bindEnv) (CurrentStateExp (App arg tmp)) iteration
                        where
                          frames = tail stack
                          tmp = stateToExp currentExp
      BinOpArg3 e2 e3 -> case currentExp of
        CurrentStateVal (B True) -> MScalculate frames (vEnv,bindEnv) currentExp iteration
                                      where
                                        frames = tail stack
                                        currentExp = CurrentStateExp e2
        CurrentStateVal (B False) -> MScalculate frames (vEnv,bindEnv) currentExp iteration
                                      where
                                        frames = tail stack
                                        currentExp = CurrentStateExp e3

      _ -> MScalculate frames (vEnv,bindEnv) (CurrentStateExp (App arg1 arg2)) iteration
            where
              pop = head stack
              arg1 = frameToExp pop
              arg2 = stateToExp currentExp
              frames = tail stack