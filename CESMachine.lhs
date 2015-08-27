CES stands for Code, Environment, Stack. The machine uses these three data structures for the evaluation of the input code. The first step is compilation: the source code of the program is compiled to an intermediate code in format of the Code data structure. The environment keeps track of the free variables of the code and the stack keeps track of the continuation of the code which will be evaluated next. 

\begin{code}
module CESMachine where
import qualified DeBruijn as S
import qualified IntegerArithmetic as I

data Inst = Int Integer
         |  Bool Bool
         |  Add
         |  Sub
         |  Mul
         |  Div
         |  Nand
         |  Eq
         |  Lt
         |  Access Int
         |  Close Code
         |  Let
         |  EndLet
         |  Apply
         |  Return
         |  If
         |  Fix
         deriving (Show, Eq)

type Code = [Inst]
data Value = BoolVal Bool | IntVal Integer | Clo Code Env | CloFix Code
    deriving Eq

instance Show Value where
  show (BoolVal b) = show b
  show (IntVal i)  = show i
  show (Clo c e)   = "Clo " ++ show c ++ " " ++ show e
  show (CloFix c)  = "Clo " ++ show c

type Env = [Value]
data Slot = Value Value | Code Code | Env Env
    deriving Show

type Stack = [Slot]
type State = (Code, Env, Stack)

compile :: S.Term -> Code
compile t =
    case t of
      S.Var n         -> [Access n]
      S.Tru           -> [Bool True]
      S.Fls           -> [Bool False]
      S.IntConst i    -> [Int i]
      S.Abs _ t       -> [Close (compile(t) ++ [Return])]
      S.App t1 t2     -> (compile t1) ++ compile(t2)  ++ [Apply]

\end{code}

In the evaluation of |if| terms in the form |If t1 t2 t3|, we have to first evaluate |t1| and then decide to evaluate |t2| or |t3|. In other words, |if| should be evaluated in a lazy way. This is important because it requires to deal with |if| terms different from other terms in the compilation phase. To clarify this, note that compiling |If t1 t2 t3| as |compile(t1)++compile(t2)++compile(t3)++[If]| will not produce a lazy code because we first evaluate all three terms |t1|, |t2|, and |t3| and then, choose either |t2| or |t3|. Instead, we put both |t2| and |t3| in a closure to postpone its evaluation. Once |t1| is evaluated, we bring either |t2| or |t3| out of the closure and evaluate it:

\begin{code}
      S.If t1 t2 t3   -> (compile t1) ++
                         [Close (compile(t2) ++ [Return])] ++
                         [Close (compile(t3) ++ [Return])] ++ [If]

      S.Let t1 t2     -> (compile t1) ++ [Let] ++ (compile t2) ++ [EndLet]
      S.Fix t1        -> (compile t1) ++ [Fix]
      S.IntAdd t1 t2  -> (compile t1) ++ (compile t2) ++ [Add]
      S.IntSub t1 t2  -> (compile t1) ++ (compile t2) ++ [Sub]
      S.IntMul t1 t2  -> (compile t1) ++ (compile t2) ++ [Mul]
      S.IntDiv t1 t2  -> (compile t1) ++ (compile t2) ++ [Div]
      S.IntNand t1 t2 -> (compile t1) ++ (compile t2) ++ [Nand]
      S.IntLt t1 t2   -> (compile t1) ++ (compile t2) ++ [Lt]
      S.IntEq t1 t2   -> (compile t1) ++ (compile t2) ++ [Eq]

step :: State -> Maybe State
step state =
    case state of
      ((Int v):c, e, s)                                      ->
        Just (c, e, (Value (IntVal v)):s)

      ((Bool v):c, e, s)                                     ->
        Just (c, e, (Value (BoolVal v)):s)

      ((Access n):c, e, s)                                   ->
         case e !! n of
           CloFix t  ->  Just (t++c, e, s)
           v         ->  Just (c, e, (Value v):s)

      ((Close c'):c, e, s)                                   ->
         Just (c, e, (Value (Clo c' e)):s)
\end{code}

Environment is a local data structure. In other words, environment of subterms should not be used for the whole term so we do not need to push subterm environments to the term environment. This means that environment of a term must be used only for that term. In the following rules, we just get rid of the environment of the subterm (denoted by |e|) in the |Return| rule because the remaining code of the whole term is independent of the contents of |e|:

\begin{code}
      (Apply:c, e, (Value v):(Value (Clo c' e')):s)          ->
         Just (c', v:e', (Code c):(Env e):s)

      (Return:c, e, v:(Code c'):(Env e'):s)                  ->
         Just (c', e', v:s)
\end{code}

Another example of this happens in the |Let| rules, where we do not need the value |v| anymore in the term when we finish evaluating the subterm (i.e. when we reach |EndLet|). So, we get rid of |v| and continue the evaluation:

\begin{code}
      (Let:c, e, (Value v):s)                                ->
         Just (c, v:e, s)

      (EndLet:c, v:e, s)                                     ->
         Just (c, e, s)
         
      (If:c, e, (Value (Clo c3 e3)):(Value (Clo c2 e2)):(Value (BoolVal v)):s)  ->
         if (v == True) then
            Just (c2, e2, (Code c):(Env e):s)
         else
            Just (c3, e3, (Code c):(Env e):s)                 
\end{code}

In the \textit{Fix $\lambda$f.t}, we need to substitute |f| with \textit{Fix $\lambda$ f}, so we need to put \textit{Fix $\lambda$ f.t} in the environment. In the big-step machine, we explained that we cannot put a code in the environment unless we make a wrap it in a closure. But in the CES machine, this simply does not work. In fact, the closure for wrapping the fix term should be different from the one used for abstractions because we need to make sure \emph{Fix} comes before the surrounding application. To address this problem, we define a different closure constructor named \emph{CloFix} for fix terms. So, whenever a \emph{CloFix} value is accessed in the environment, we do not put it in the stack as we do for redular \emph{Clo} terms. Instead, we insert its content term in the front of the current code. This makes it possible to evaluate fix term before the surrounding application:

\begin{code}
      (Fix:c, e, (Value (Clo (Close c':c'') e')) : s)        ->
         Just (c, e, (Value (Clo (c'++c'') ((CloFix (Close ((Close c':c'')):[Fix])):(skipFixEnvs e)))) : s)

      (Add:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s)  ->
         Just (c, e, (Value (IntVal (I.intAdd v1 v2)):s))

      (Sub:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s)  ->
         Just (c, e, (Value (IntVal (I.intSub v1 v2)):s))

      (Mul:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s)  ->
         Just (c, e, (Value (IntVal (I.intMul v1 v2)):s))

      (Div:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s)  ->
         Just (c, e, (Value (IntVal (I.intDiv v1 v2)):s))

      (Nand:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s) ->
         Just (c, e, (Value (IntVal (I.intNand v1 v2)):s))

      (Lt:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s)   ->
         Just (c, e, (Value (BoolVal (I.intLt v1 v2)):s))

      (Eq:c, e, (Value (IntVal v2)):(Value (IntVal v1)):s)   ->
         Just (c, e, (Value (BoolVal (I.intEq v1 v2)):s))

      otherwise -> Nothing

loop :: State -> State
loop state =
    case step state of
      Just state' -> loop state'
      Nothing     -> state

eval :: S.Term -> Value
eval t = case loop (compile t, [], []) of
           (_,_,Value v:_) -> v
\end{code}

Now, consider the following recursive program in the core lambda language. Evaluation of the recursive calls results in creation of four environments (see Figure 1). The inner three environments correspond to the three recursive (fix) calls, each of which has an access to the outer environment variable $y$:

\begin{verbatim}
let y = 0
in
    app( 
        fix (
            abs (f:->(Int,Int). 
                abs (x:Int. 
                    if =(x,y) then 
                        1
                    else 
                        *(x, app (f,-(x,1)))
                    fi
                )
            )
        ), 2
    )
end
\end{verbatim}

\begin{figure}[tp]
	\centering
	\includegraphics[width=0.65\textwidth]{envs.png}
  \caption{Evaluation of the recursive program results in creation of four environments. The inner three environments correspond to the three recursive (fix) calls, each of which has an access to the outer environment variable $y$.} 
\end{figure}

In each of the three recursive calls, the environment should contain only the current value of |x| and the value of the global variable |y| otherwise the access to |y| is incorrectly made. Note that the contents of previous recursive calls are all contained in the current environment so |y| will not be accesses correctly. To fix this, we defined a function named |skipFixEnvs|, which skips all contents of the current environment related to previous recursive calls and returns the rest of contents related to global environment:

\begin{code}
skipFixEnvs :: Env -> Env
skipFixEnvs e = case reverse e of
                  er -> take (skipFixWorker er 0) er

skipFixWorker :: Env -> Int -> Int
skipFixWorker [] i     = i
skipFixWorker (e:es) i = case e of
                           (CloFix _) -> i
                           otherwise  -> skipFixWorker es (i+1)
\end{code}
