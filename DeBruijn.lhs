The DeBruijn notation is a syntax for nameless representation of $\lambda$ terms. It can be seen as a reversal of the usual syntax for the $\lambda$-calculus where the argument in an application is placed next to its corresponding binder in the function instead of after the latter's body. The goal here is to convert the core lambda language terms to De Bruijn terms, which consists of no variable names. 

\begin{code}
module DeBruijn where
import Data.List
import qualified AbstractSyntax as S

type Type = S.Type
type IntConst = Integer
data Term  = Var Int
           | Abs Type Term
           | App Term Term
           | Fix Term
           | Let Term Term
           | Tru
           | Fls
           | If Term Term Term
           | IntConst IntConst
           | IntAdd Term Term
           | IntSub Term Term
           | IntMul Term Term
           | IntDiv Term Term
           | IntNand Term Term
           | IntEq Term Term
           | IntLt Term Term
           deriving Eq

instance Show Term where
  show (Var i)         =  "~" ++ show i
  show (Abs tau t)     =  "abs(" ++ show t ++ ")"
  show (App t1 t2)     =  "app(" ++ show t1  ++ "," ++ show t2 ++ ")"
  show (Fix t)         =  "fix(" ++ show t ++ ")"
  show (Let t1 t2)     =  "let " ++ show t1 ++
                          " in " ++ show t2
  show Tru             =  "true"
  show Fls             =  "false"
  show (If t1 t2 t3)   =  "if " ++ show t1 ++ " then " ++ show t2 ++ " else "
                          ++ show t3 ++ " fi"
  show (IntConst t1)   =  show t1
  show (IntAdd t1 t2)  =  show t1 ++ "+" ++ show t2
  show (IntSub t1 t2)  =  show t1 ++ "-" ++ show t2
  show (IntMul t1 t2)  =  show t1 ++ "*" ++ show t2
  show (IntDiv t1 t2)  =  show t1 ++ "/" ++ show t2
  show (IntNand t1 t2) =  show t1 ++ "|" ++ show t2
  show (IntEq t1 t2)   =  show t1 ++ "=" ++ show t2
  show (IntLt t1 t2)   =  show t1 ++ "<" ++ show t2
  
\end{code}

We define a function named |dbWorker|, which gets the original lambda term and a stack of strings for storing variable names. It then scans the input term recursively and adds variable names that appear in abstraction and let terms to the stack. Once a variable is seen, |dbWorker| returns the index of the variable in the stack replacing it with an integer.

\begin{code}

dbWorker :: S.Term -> [String] -> Maybe Term
dbWorker t s =
    case t of
      S.Tru           ->  Just Tru
      S.Fls           ->  Just Fls
      S.IntConst i    ->  Just (IntConst i)
      S.Var x         ->  do i <- elemIndex x s
                             Just (Var i)

      S.Abs x tau t1  ->  do t1' <- dbWorker t1 (x : s)
                             Just (Abs tau t1')

      S.App t1 t2     ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (App t1' t2')

      S.Fix t         ->  do t' <- dbWorker t s
                             Just (Fix t')

      S.Let x t1 t2   ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 (x : s)
                             Just (Let t1' t2')

      S.If t1 t2 t3   ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             t3' <- dbWorker t3 s
                             Just (If t1' t2' t3')

      S.IntAdd t1 t2  ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntAdd t1' t2')

      S.IntSub t1 t2  ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntSub t1' t2')

      S.IntMul t1 t2  ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntMul t1' t2')

      S.IntDiv t1 t2  ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntDiv t1' t2')

      S.IntNand t1 t2 ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntNand t1' t2')

      S.IntEq t1 t2   ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntEq t1' t2')

      S.IntLt t1 t2   ->  do t1' <- dbWorker t1 s
                             t2' <- dbWorker t2 s
                             Just (IntLt t1' t2')

toDeBruijn :: S.Term -> Term
toDeBruijn t = case dbWorker t [] of
                 Just t    -> t
                 otherwise -> error "Cannot convert to De Bruijn notation!"
\end{code}
