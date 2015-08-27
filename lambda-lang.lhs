\documentclass[11pt]{article}
%% Literate Haskell script intended for lhs2TeX.

%include polycode.fmt
%format `union` = "\cup"
%format alpha = "\alpha"
%format gamma = "\gamma"
%format capGamma = "\Gamma"
%format tau = "\tau"
%format tau1 = "\tau_{1}"
%format tau2 = "\tau_{2}"
%format tau11 = "\tau_{11}"
%format tau12 = "\tau_{12}"
%format t12 = "t_{12}"
%format t1 = "t_{1}"
%format t1' = "t_{1}^{\prime}"
%format t2 = "t_{2}"
%format t2' = "t_{2}^{\prime}"
%format t3 = "t_{3}"
%format nv1 = "nv_{1}"

\usepackage{fullpage}
\usepackage{mathpazo}
\usepackage{graphicx}
\usepackage{color}
\usepackage[centertags]{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{soul}
\usepackage{stmaryrd}

\title{Extended simply-typed call-by-value lambda-calculus with booleans and natural numbers}
\author{Mahdi Zamani}
\date{November 22, 2011}
\begin{document}
\maketitle
\thispagestyle{empty}
In this project, we implemented a small core lambda language, consisting of the lambda calculus with booleans and integers. Moreover, we implemented the nameless representation (DeBruijn notation), natural semantics with nameless representation, the CES
machine, the Continuation-Passing-Style (CPS) transformation, and CE3R machine.
The program takes a command-line argument, which is the name of the source language file. It reads the file entirely and places it into a string. Then, it performs lexical analysis on the string to produce a list of tokens. It then parses the list of tokens to produce a term. If a term was successfully created then the program type-checks it and if there is no any type errors then it evaluates the term. The output consists of three parts: the first part is the result of the parsing, which is a term. The second part is the type of the term and finally, the third part is the normal form of term, which is the result of the evaluation. An appropriate error message will be shown in each part if the program is unable to do the corresponding procedure.
\newpage

\section{Concrete syntax}
\begin{verbatim}
Type --> arr lpar Type comma Type rpar
       | bool
       | nat

Term --> identifier
       | abs lpar identifier colon Type fullstop Term rpar
       | app lpar Term comma Term rpar
       | true
       | false
       | if Term then Term else Term fi
       | 0
       | succ lpar Term rpar
       | pred lpar Term rpar
       | iszero lpar Term rpar
       | lpar Term rpar
       | fix lpar Term rpar
\end{verbatim}

\newpage

\section{Prologue}
\begin{code}
module Main where

import qualified System.Environment
import Data.List
import IO

class LatexShow tau where
  latexShow :: tau -> String
\end{code}

\section{Abstract-syntactic preliminaries}
\subsection{Source types}
\begin{code}
data Type  =  TypeArrow Type Type
           |  TypeBool
           |  TypeNat
           deriving Eq

instance Show Type where
  show  (TypeArrow tau1 tau2)   =  "->(" ++ show tau1 ++ "," ++ show tau2 ++ ")"
  show  TypeBool                =  "Bool"
  show  TypeNat                 =  "Nat"

instance LatexShow Type where
  latexShow  (TypeArrow tau1 tau2)    =  "$\\rightarrow$ (" ++ latexShow tau1
                                         ++ ", " ++ latexShow tau2 ++ ")"
  latexShow  TypeBool                 =  "Bool"
  latexShow  TypeNat                  =  "Nat"
\end{code}
\subsection{Source terms}
\begin{code}
type Var  =  String

data Term  =  Var Var
           |  Abs Var Type Term
           |  App Term Term
           |  Tru
           |  Fls
           |  If Term Term Term
           |  Zero
           |  Succ Term
           |  Pred Term
           |  IsZero Term
           |  Fix Term
           deriving Eq

instance Show Term where
  show (Var x)        =  x
  show (Abs x tau t)  =  "abs(" ++ x ++ ":" ++ show tau ++ "." ++ show t ++ ")"
  show (App t1 t2)    =  "app(" ++ show t1  ++ "," ++ show t2 ++ ")"
  show Tru            =  "true"
  show Fls            =  "false"
  show (If t1 t2 t3)  =  "if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3 ++ " fi"
  show Zero           =  "0"
  show (Succ t)       =  "succ(" ++ show t ++ ")"
  show (Pred t)       =  "pred(" ++ show t ++ ")"
  show (IsZero t)     =  "iszero(" ++ show t ++ ")"
  show (Fix t)        =  "fix(" ++ show t ++ ")"

instance LatexShow Term where
  latexShow  (Var x)            =  x
  latexShow  (Abs x tau t)      =  "$\\lambda$" ++ x ++ ": " ++ latexShow tau
                                   ++ ". " ++ latexShow t
  latexShow  (App t1 t2)        =  "$\\blacktriangleright$ (" ++ latexShow t1  ++ ", " ++ latexShow t2 ++ ")"
  latexShow  Tru                =  "true"
  latexShow  Fls                =  "false"
  latexShow  (If t1 t2 t3)      =  "if " ++ latexShow t1 ++ " then " ++ latexShow t2
                                   ++ " else " ++ latexShow t3 ++ " fi"
  latexShow Zero                =  "0"
  latexShow (Succ t)            =  "succ(" ++ latexShow t ++ ")"
  latexShow (Pred t)            =  "pred(" ++ latexShow t ++ ")"
  latexShow (IsZero t)          =  "iszero(" ++ latexShow t ++ ")"
\end{code}

\newpage
\subsection{Binding and free variables}
\begin{code}
fv :: Term -> [Var]
-- list of free variables of a term
fv Tru            =  []
fv Fls            =  []
fv Zero           =  []
fv (Var x)        =  [x]
fv (Succ t1)      =  fv t1
fv (Pred t1)      =  fv t1
fv (IsZero t1)    =  fv t1
fv (If t1 t2 t3)  =  (fv t1)++(fv t2)++(fv t3)
fv (Abs x _ t1)   =  filter (/=x) (fv t1)
fv (App t1 t2)    =  (fv t1)++(fv t2)
fv (Fix t1)       =  fv t1
\end{code}

\subsection{Substitution}
Substitution: |subst x s t|, or $[x \mapsto s]t$ in Pierce, 
is the result of substituting |s| for |x| in |t|.

\begin{code}
subst :: Var -> Term -> Term -> Term

subst x s Fls = Fls
subst x s Tru = Tru
subst x s Zero = Zero
subst x s (Succ t1) = Succ (subst x s t1)
subst x s (Pred t1) = Pred (subst x s t1)
subst x s (IsZero t1) = IsZero (subst x s t1)  
subst x s (If t1 t2 t3) = If (subst x s t1) (subst x s t2) (subst x s t3) 
subst x s (Var v) = if (v == x) then s else (Var v)

subst x s (Abs y tau term) = if (x == y || elem y (fv s))
                             then Abs y tau term
                             else Abs y tau (subst x s term)

subst x s (App t1 t2) = App (subst x s t1) (subst x s t2)
subst x s (Fix t1) = Fix (subst x s t1)
\end{code}

\newpage
\section{Small-step evaluation relation}
An evaluation strategy is a set of rules for evaluating expressions in a programming language. Here, the evaluation rules described in Chapter 9 of the textbook are used to define three functions: |isValue|, |isNumericValue|, and |eval1|. For every evaluation rule, a separate pattern of one of these functions is defined to reduce the input term to a simpler form. |eval1| is called recursively on some of the compound terms which their evaluations depend on the evaluation of internal terms (like |If t1 t2 t3|):
\begin{code}
isValue :: Term -> Bool
isValue  (Abs _ _ _)  =  True
isValue  Tru          =  True
isValue  Fls          =  True
isValue  Zero         =  True
isValue  (Succ t)     =  isNumericValue t
isValue  _            =  False

isNumericValue :: Term -> Bool
isNumericValue  Zero      =  True
isNumericValue  (Succ t)  =  isNumericValue t
isNumericValue  _         =  False

eval1 :: Term -> Maybe Term
--one-step evaluation relation
eval1  (If Tru t2 t3) = Just t2
eval1  (If Fls t2 t3) = Just t3
eval1  (If t1 t2 t3) =
  case eval1 t1 of
    Just t1' -> Just (If t1' t2 t3)
    Nothing -> Nothing
                                    
eval1 (Succ t1) = 
  case eval1 t1 of
    Just t1' -> Just (Succ t1')
    Nothing -> Nothing

eval1 (Pred Zero) = Just Zero
eval1 (Pred (Succ nv)) 
                      | (isNumericValue nv) = Just (nv)
                      | otherwise = Nothing

eval1 (Pred t1) =
  case eval1 t1 of
    Just t1' -> Just (Pred t1')
    Nothing -> Nothing                                 

eval1 (IsZero Zero) = Just Tru
eval1 (IsZero (Succ nv)) 
                        | (isNumericValue nv) = Just Fls
                        | otherwise = Nothing
eval1 (IsZero t1) =
  case eval1 t1 of
    Just t1' -> Just (IsZero t1')
    Nothing -> Nothing

eval1 (App t1 t2) = 
   case isValue t1 of
     False -> case eval1 t1 of
                Just t1' -> Just (App t1' t2)
                Nothing -> Nothing
     True -> case isValue t2 of
               False -> case eval1 t2 of
                          Just t2' -> Just (App t1 t2')
                          Nothing -> Nothing
               True -> case t1 of
                         (Abs x _ term) -> Just (subst x t2 term)
                         _ -> Nothing
              
eval1 (Fix (Abs x tau t1)) = Just (subst x (Fix (Abs x tau t1)) t1)

eval1 (Fix t1) =
  case eval1 t1 of
    Just t1' -> Just (Fix t1')
    Nothing -> Nothing

eval1 _ = Nothing              

eval :: Term -> Term
--reduction to normal form
eval t =
  case eval1 t of
    Just t' -> eval t'
    Nothing -> t
\end{code}

\newpage
\section{Typing}
Type checking is the processes of identifying errors in a program based on explicitly or implicitly stated type information. The input of the type checker is the output of parsing, i.e. a term. The type-checker applies the typing relations as defined in the textbook and returns the type of the parsed term or a type error. Type-checking can be initiated by calling |typeCheck| function but the actual type-checking is performed by |typing| function, which is defined by several patterns to compute type of different language structures.
\begin{code}
data TypingContext  =  Empty
                    |  Bind TypingContext Var Type
                    deriving Eq
instance Show TypingContext where
  show Empty                  =  "<>"
  show (Bind capGamma x tau)  =  show capGamma ++ "," ++ x ++ ":" ++ show tau

contextLookup :: Var -> TypingContext -> Maybe Type
contextLookup x Empty  =  Nothing
contextLookup x (Bind capGamma y tau)
  | x == y      =  Just tau
  | otherwise   =  contextLookup x capGamma

typing :: TypingContext -> Term -> Maybe Type
--the typing relation
typing capGamma (Var x) = contextLookup x capGamma

typing capGamma (Abs x tau term) = tau2
								 where 
                                      capGamma' = Bind capGamma x tau
                                      tau2 = case typing capGamma' term of
                                               Just tau3 -> Just (TypeArrow tau tau3)
                                               _ -> Nothing
                                      
typing capGamma (App term1 term2) = case typing capGamma term1 of
                                      Just (TypeArrow tau1 tau2) -> case typing capGamma term2 of
                                                                      Just tau -> if (tau == tau1) 
                                                                                  then Just tau2 
                                                                                  else Nothing
                                                                      _ -> Nothing
                                      _ -> Nothing
                                       
typing capGamma (Tru) = Just TypeBool
typing capGamma (Fls) = Just TypeBool

typing capGamma (If t1 t2 t3) = case typing capGamma t1 of
                                  Just TypeBool -> case typing capGamma t2 of 
                                                     Just tau2 -> case typing capGamma t3 of
                                                                    Just tau -> if (tau == tau2) 
                                                                                then Just tau2
                                                                                else Nothing
                                                                    _ -> Nothing
                                                     _ -> Nothing
                                  _ -> Nothing

typing capGamma (Zero) = Just TypeNat

typing capGamma (Succ t1) = typing capGamma t1
typing capGamma (Pred t1) = typing capGamma t1

typing capGamma (IsZero t1) = case typing capGamma t1 of
                                Just TypeNat -> Just TypeBool
                                _ -> Nothing
                                
typing capGamma (Fix t1) = case typing capGamma t1 of
                             Just (TypeArrow tau1 tau2) -> if (tau1 == tau2) 
                                                           then Just tau1 
                                                           else Nothing
                             _ -> Nothing

typeCheck :: Term -> Type
typeCheck t =
  case typing Empty t of
    Just tau -> tau
    _ -> error "type error"
\end{code}

\newpage
\section{Scanning and parsing}
Lexical analysis is the process of converting a sequence of characters into a sequence of tokens. A token is a string of characters, categorized according to the rules as a symbol. A data type called |Token| is implemented that defines various keywords of the language. Parsing is the process of analyzing a text, made of a sequence of tokens to determine its grammatical structure with respect to a given (more or less) formal grammar. Here, a data type called |Term| is implemented that defines the grammar of the language.
\begin{code}
data Token  =  Identifier String
            |  AbsKeyword
            |  AppKeyword
            |  TrueKeyword
            |  FalseKeyword
            |  IfKeyword
            |  ThenKeyword
            |  ElseKeyword
            |  FiKeyword
            |  BoolKeyword
            |  ZeroKeyword
            |  SuccKeyword
            |  PredKeyword
            |  IsZeroKeyword
            |  NatKeyword
            |  LPar
            |  RPar
            |  Comma
            |  Colon
            |  FullStop
            |  RightArrow
            |  FixKeyword
            deriving (Eq, Show)

scan :: String -> [Token]
scan s = map makeKeyword (f s)
  where
    f :: [Char] -> [Token]
    f []               =  []
    f (' ':t)          =  f t
    f ('\t':t)         =  f t
    f ('\n':t)         =  f t
    f ('-':'>':t)      =  RightArrow : f t
    f ('(':t)          =  LPar : f t
    f (')':t)          =  RPar : f t
    f (',':t)          =  Comma : f t
    f (':':t)          =  Colon : f t
    f ('.':t)          =  FullStop : f t
    f (h:t)            =  g [h] t

    g :: [Char] -> [Char] -> [Token]
    g s [] = [Identifier s]
    g s (t:ts) = if (elem t ([' ','\t','\n','-','>','(',')',',',':','.'])) 
    			 then ((Identifier s) : (f (t:ts))) 
    			 else (g (s++[t]) ts) 

    makeKeyword :: Token -> Token
    makeKeyword (Identifier s)
      |  s == "abs"     =  AbsKeyword
      |  s == "app"     =  AppKeyword
      |  s == "true"    =  TrueKeyword
      |  s == "false"   =  FalseKeyword
      |  s == "if"      =  IfKeyword
      |  s == "then"    =  ThenKeyword
      |  s == "else"    =  ElseKeyword
      |  s == "fi"      =  FiKeyword
      |  s == "Bool"    =  BoolKeyword
      |  s == "0"       =  ZeroKeyword
      |  s == "succ"    =  SuccKeyword
      |  s == "pred"    =  PredKeyword
      |  s == "iszero"  =  IsZeroKeyword
      |  s == "Nat"     =  NatKeyword
      |  s == "fix"     =  FixKeyword
      |  otherwise      =  Identifier s
    makeKeyword t = t
       
parseType :: [Token] -> Maybe (Type, [Token])

parseType (RightArrow:LPar:tl) =
  case parseType tl of
    Just (tau1, Comma:tl') ->
      case parseType tl' of
        Just (tau2, RPar:tl'') -> Just (TypeArrow tau1 tau2, tl'')
        _ -> Nothing
    _ -> Nothing

parseType (BoolKeyword:tl) = Just (TypeBool, tl)
parseType (NatKeyword:tl) = Just (TypeNat, tl)
parseType (_:tl) = Nothing

parseTerm :: [Token] -> Maybe (Term, [Token])
parseTerm (Identifier s:tl) = Just (Var s, tl)

parseTerm (AbsKeyword:tl) = if (head tl == LPar) 
                            then case parseTerm (tail tl) of
                                   Just (Var var, remt1) -> 
                                      if (head remt1 == Colon)
                                      then case parseType (tail remt1) of
                                             Just (tau, remt2) -> 
                                                if (head remt2 == FullStop) 
                                                then case parseTerm (tail remt2) of
                                                       Just (term, remt3) -> 
                                                          if (head remt3 == RPar) 
                                                          then Just ((Abs var tau term), tail remt3)
                                                          else Nothing
                                                       Nothing -> Nothing
                                                else Nothing
                                             Nothing -> Nothing
                                      else Nothing
                                   _ -> Nothing
                            else Nothing
                               
parseTerm (AppKeyword:tl) = if (head tl == LPar)
                            then case parseTerm (tail tl) of
                                   Just (term1, remt1) -> 
                                      if (head remt1 == Comma) 
                                      then case parseTerm (tail remt1) of
                                             Just (term2, remt2) -> 
                                                if (head(remt2) == RPar)
                                                then Just ((App term1 term2), tail remt2)
                                                else Nothing
                                             Nothing -> Nothing
                                      else Nothing
                                   Nothing -> Nothing
                            else Nothing

parseTerm (TrueKeyword:tl)  = Just (Tru, tl)
parseTerm (FalseKeyword:tl) = Just (Fls, tl)
parseTerm (ZeroKeyword:tl)  = Just (Zero, tl)
parseTerm (SuccKeyword:tl) = case parseTerm tl of
                               Just tl' -> Just (Succ (fst tl'), snd tl')
                               Nothing -> Nothing

parseTerm (PredKeyword:tl) = case parseTerm tl of
                               Just tl' -> Just (Pred (fst tl'), snd tl')
                               Nothing -> Nothing
                                    
parseTerm (IsZeroKeyword:tl) = case parseTerm tl of
                                 Just tl' -> Just (IsZero (fst tl'), snd tl')
                                 Nothing -> Nothing                      

parseTerm (IfKeyword:tl) = case parseTerm tl of
                             Just (term1, rt1) -> 
                                if (length rt1) > 0 && (head rt1) == ThenKeyword
                                then case parseTerm (tail rt1) of
                                       Just (term2, rt2) -> 
                                          if (length rt2) > 0 && (head rt2) == ElseKeyword
                                          then case parseTerm (tail rt2) of
                                                 Just (term3, rt3) -> 
                                                    if (length rt3) > 0 && (head rt3) == FiKeyword
                                                    then Just ((If term1 term2 term3), tail rt3)
                                                    else Nothing
                                                 Nothing -> Nothing
                                          else Nothing
                                       Nothing -> Nothing
                                else Nothing                
                             Nothing -> Nothing
                                   
parseTerm (LPar:tl) = case parseTerm tl of
                        Just (term1, rt1) -> 
                           if head rt1 == RPar 
                           then Just (term1, tail rt1)
                           else Nothing
                        Nothing -> Nothing
                        
parseTerm (FixKeyword:tl) = case parseTerm tl of
                              Just tl' -> Just (Fix (fst tl'), snd tl')
                              Nothing -> Nothing                        
                              
parseTerm (_:tl) = Nothing
parseTerm [] = Nothing

parse :: [Token] -> Term
parse ts =
  case parseTerm ts of
    Just (t, []) -> t
    Just (t, _) -> error "syntax error: spurious input at end"
    Nothing -> error "syntax error"
\end{code}

\newpage
\section{Epilogue}
\begin{code}
main :: IO ()
main =
    do
      args <- System.Environment.getArgs
      let [sourceFile] = args
      source <- readFile sourceFile
      let tokens = scan source
              
      let term = parse tokens
      putStrLn ("---Term:---")
      putStrLn (show term)
      --putStrLn (latexShow term)
      putStrLn ("---Type:---")
      putStrLn (show (typeCheck term))
      --putStrLn (latexShow (typeCheck term))
      putStrLn ("---Normal form:---")
      putStrLn (show (eval term))
      --putStrLn (latexShow (eval term))
\end{code}

\section{Test Results} 
We run several tests to make sure that the program is giving correct results. Each test is followed by the result obtained from that test:

\begin{verbatim}
------------------------------------------------------------------------------

TEST1: leq 2 3

PCF (unindented):

app ( app ( fix ( abs (leq:->(Nat,->(Nat,Bool)). abs (m:Nat. abs (n:Nat. if 
iszero(m) then true else if iszero(n) then false else app (app (leq, pred(m)), 
pred(n)) fi fi ) ) ) ) , succ (succ (0)) ) , succ (succ (succ (0))) )

PCF (indented):

app (
     app (
          fix (
               abs (leq:->(Nat,->(Nat,Bool)). 
                    abs (m:Nat. 
                         abs (n:Nat. 
                              if iszero(m) then true 
                              else if iszero(n) then false 
                                   else app (app (leq, pred(m)), pred(n))
                                   fi
                              fi
		               )
                    )
               )
          )
          , succ (succ (0))
     )
     , succ (succ (succ (0)))
)

Output:

---Term:---
app(app(fix(abs(leq:->(Nat,->(Nat,Bool)).abs(m:Nat.abs(n:Nat.if iszero(m) then
true else if iszero(n) then false else app(app(leq,pred(m)),pred(n)) fi fi)))),
succ(succ(0))),succ(succ(succ(0))))
---Type:---
Bool
---Normal form:---
true

-------------------------------------------------------------------------------

TEST2: equal 2 3

PCF (unindented):

app ( app ( fix ( abs (equal:->(Nat,->(Nat,Bool)). abs (m:Nat. abs (n:Nat. if 
iszero(m) then iszero(n) else if iszero(n) then false else app (app (equal, pred(m)), 
pred(n)) fi fi ) ) ) ) , succ (succ (0)) ) , succ (succ (succ (0))) )

PCF (indented):

app (
     app (
          fix (
               abs (equal:->(Nat,->(Nat,Bool)). 
                    abs (m:Nat. 
                         abs (n:Nat. 
                              if iszero(m) then iszero(n) 
                              else if iszero(n) then false 
                                   else app (app (equal, pred(m)), pred(n))
                                   fi
                              fi
		                 )
                    )
               )
          )
          , succ (succ (0))
     )
     , succ (succ (succ (0)))
)

Output:

---Term:---
app(app(fix(abs(equal:->(Nat,->(Nat,Bool)).abs(m:Nat.abs(n:Nat.if iszero(m) then
iszero(n) else if iszero(n) then false else app(app(equal,pred(m)),pred(n)) fi
fi)))),succ(succ(0))),succ(succ(succ(0))))
---Type:---
Bool
---Normal form:---
false

-------------------------------------------------------------------------------

TEST3: plus 2 3

PCF (unindented):

app ( app ( fix ( abs (plus:->(Nat,->(Nat,Nat)). abs (m:Nat. abs (n:Nat. if 
iszero(m) then n else succ (app (app (plus, pred(m)), n)) fi ) ) ) ) , succ 
(succ (0)) ) , succ (succ (succ (0))) )

PCF (indented):

app (
     app (
          fix (
               abs (plus:->(Nat,->(Nat,Nat)). 
                    abs (m:Nat. 
                         abs (n:Nat. 
                              if iszero(m) then n 
                              else succ (app (app (plus, pred(m)), n))
                              fi
		                 )
                    )
               )
          )
          , succ (succ (0))
     )
     , succ (succ (succ (0)))
)

Output:

---Term:---
app(app(fix(abs(plus:->(Nat,->(Nat,Nat)).abs(m:Nat.abs(n:Nat.if iszero(m) then n
else succ(app(app(plus,pred(m)),n)) fi)))),succ(succ(0))),succ(succ(succ(0))))
---Type:---
Nat
---Normal form:---
succ(succ(succ(succ(succ(0)))))

-------------------------------------------------------------------------------

TEST4: times 2 3

PCF (unindented):

app ( app ( app ( fix ( abs (times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))). 
abs (m:Nat. abs (n:Nat. abs (plus:->(Nat,->(Nat,Nat)). if iszero(m) then 0 else 
app ( app (plus, n), app ( app ( app (times, pred(m)), n ), plus ) ) fi ) ) ) ) ), 
succ (succ (0)) ), succ (succ (succ (0))) ), fix ( abs (plus:->(Nat,->(Nat,Nat)). 
abs (m:Nat. abs (n:Nat. if iszero(m) then n else succ (app (app (plus, pred(m)), n)) 
fi ) ) ) ) )

PCF (indented):

app (
     app (
          app (
               fix (
                    abs (times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))). 
                         abs (m:Nat. 
                              abs (n:Nat.
                                   abs (plus:->(Nat,->(Nat,Nat)).
                                        if iszero(m) then 0
                                        else app (
                                                  app (plus, n),
     					                          app (
                                                       app (
                                                            app (times, pred(m)), 
                                                            n
                                                       ),
                                                       plus
                                                  )
                                             ) 
                                        fi
                                   )
     		                  )
                         )
                    )
               ),
               succ (succ (0))
          ),
          succ (succ (succ (0)))
     ),
     fix (
          abs (plus:->(Nat,->(Nat,Nat)). 
               abs (m:Nat. 
                    abs (n:Nat. 
                         if iszero(m) then n 
                         else succ (app (app (plus, pred(m)), n))
                         fi
	               )
               )
          )
     )
)

Output:

---Term:---
app(app(app(fix(abs(times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))).abs(m:Nat.
abs(n:Nat.abs(plus:->(Nat,->(Nat,Nat)).if iszero(m) then 0 else app(app(plus,n),
app(app(app(times,pred(m)),n),plus)) fi))))),succ(succ(0))),succ(succ(succ(0))))
,fix(abs(plus:->(Nat,->(Nat,Nat)).abs(m:Nat.abs(n:Nat.if iszero(m) then n else s
ucc(app(app(plus,pred(m)),n)) fi)))))
---Type:---
Nat
---Normal form:---
succ(succ(succ(succ(succ(succ(0))))))

-------------------------------------------------------------------------------

TEST5: exp 2 3

PCF (unindented):

app ( app ( app ( app ( fix ( abs( exp:->(Nat,->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat
,Nat)),Nat))),->(->(Nat,->(Nat,Nat)),Nat)))). abs (a:Nat. abs (x:Nat. abs (times:->(Nat,
->(Nat,->(->(Nat,->(Nat,Nat)),Nat))). abs (plus:->(Nat,->(Nat,Nat)). if iszero(x) then 
succ (0) else app ( app ( app ( times, a ), app ( app ( app ( app ( exp, a ), (pred x) ), 
times ), plus ) ), plus ) fi ) ) ) ) ) ), succ (succ (0)) ), succ (succ (succ (0))) ), 
fix ( abs (times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))). abs (m:Nat. abs (n:Nat. 
abs (plus:->(Nat,->(Nat,Nat)). if iszero(m) then 0 else app ( app (plus, n), app ( app ( 
app (times, pred(m)), n ), plus ) ) fi ) ) ) ) ) ), fix ( abs (plus:->(Nat,->(Nat,Nat)). 
abs (m:Nat. abs (n:Nat. if iszero(m) then n else succ (app (app (plus, pred(m)), n)) fi ) ) ) ) )

Output:

---Term:---
app(app(app(app(fix(abs(exp:->(Nat,->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)
),Nat))),->(->(Nat,->(Nat,Nat)),Nat)))).abs(a:Nat.abs(x:Nat.abs(times:->(Nat,->(
Nat,->(->(Nat,->(Nat,Nat)),Nat))).abs(plus:->(Nat,->(Nat,Nat)).if iszero(x) then
 succ(0) else app(app(app(times,a),app(app(app(app(exp,a),pred(x)),times),plus))
,plus) fi)))))),succ(succ(0))),succ(succ(succ(0)))),fix(abs(times:->(Nat,->(Nat,
->(->(Nat,->(Nat,Nat)),Nat))).abs(m:Nat.abs(n:Nat.abs(plus:->(Nat,->(Nat,Nat)).i
f iszero(m) then 0 else app(app(plus,n),app(app(app(times,pred(m)),n),plus)) fi)
))))),fix(abs(plus:->(Nat,->(Nat,Nat)).abs(m:Nat.abs(n:Nat.if iszero(m) then n e
lse succ(app(app(plus,pred(m)),n)) fi)))))
---Type:---
Nat
---Normal form:---
succ(succ(succ(succ(succ(succ(succ(succ(0))))))))

-------------------------------------------------------------------------------

TEST6: fact 3

PCF (unindented):

app ( app ( app ( fix ( abs (fact:->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),
Nat))),->(->(Nat,->(Nat,Nat)),Nat))). abs (m:Nat. abs (times:->(Nat,->(Nat,->(->(
Nat,->(Nat,Nat)),Nat))). abs (plus:->(Nat,->(Nat,Nat)). if iszero(m) then succ(0) 
else app ( app ( app (times, m), app ( app ( app (fact, pred(m)), times ), plus ) 
), plus ) fi ) ) ) ) ), succ (succ (succ (0))) ), fix ( abs (times:->(Nat,->(Nat,
->(->(Nat,->(Nat,Nat)),Nat))). abs (m:Nat. abs (n:Nat. abs (plus:->(Nat,->(Nat,Nat
)). if iszero(m) then 0 else app ( app (plus, n), app ( app ( app (times, pred(m)),
n ), plus ) ) fi ) ) ) ) ) ), fix ( abs (plus:->(Nat,->(Nat,Nat)). abs (m:Nat. 
abs (n:Nat. if iszero(m) then n else succ (app (app (plus, pred(m)), n)) fi ) ) ) ) )

Output:

---Term:---
app(app(app(fix(abs(fact:->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))),-
>(->(Nat,->(Nat,Nat)),Nat))).abs(m:Nat.abs(times:->(Nat,->(Nat,->(->(Nat,->(Nat,
Nat)),Nat))).abs(plus:->(Nat,->(Nat,Nat)).if iszero(m) then succ(0) else app(app
(app(times,m),app(app(app(fact,pred(m)),times),plus)),plus) fi))))),succ(succ(su
cc(0)))),fix(abs(times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))).abs(m:Nat.abs
(n:Nat.abs(plus:->(Nat,->(Nat,Nat)).if iszero(m) then 0 else app(app(plus,n),app
(app(app(times,pred(m)),n),plus)) fi)))))),fix(abs(plus:->(Nat,->(Nat,Nat)).abs(
m:Nat.abs(n:Nat.if iszero(m) then n else succ(app(app(plus,pred(m)),n)) fi)))))
---Type:---
Nat
---Normal form:---
succ(succ(succ(succ(succ(succ(0))))))

-------------------------------------------------------------------------------

TEST7: fact (fact 3)

PCF (unindented):

app ( app ( app ( app ( abs (fact:->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat,Nat))
,Nat))),->(->(Nat,->(Nat,Nat)),Nat))). abs (x:Nat. abs (times:->(Nat,->(Nat,->(->
(Nat,->(Nat,Nat)),Nat))). abs (plus:->(Nat,->(Nat,Nat)). app( app ( app ( fact, 
app ( app ( app (fact, x), times ), plus ) ), times ), plus ) ) ) ) ), fix ( abs 
(fact:->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))),->(->(Nat,->(Nat,Nat))
,Nat))). abs (m:Nat. abs (times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))). abs 
(plus:->(Nat,->(Nat,Nat)). if iszero(m) then succ(0) else app ( app ( app (times, 
m), app ( app ( app (fact, pred(m)), times ), plus ) ), plus ) fi ) ) ) ) ) ), 
succ (succ (succ (0))) ), fix ( abs (times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),
Nat))). abs (m:Nat. abs (n:Nat. abs (plus:->(Nat,->(Nat,Nat)). if iszero(m) then 
0 else app ( app (plus, n), app ( app ( app (times, pred(m)), n ), plus ) ) fi ) 
) ) ) ) ), fix ( abs (plus:->(Nat,->(Nat,Nat)). abs (m:Nat. abs (n:Nat. if iszero(m) 
then n else succ (app (app (plus, pred(m)), n)) fi ) ) ) ) )

Output:

---Term:---
app(app(app(app(abs(fact:->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),Nat))),-
>(->(Nat,->(Nat,Nat)),Nat))).abs(x:Nat.abs(times:->(Nat,->(Nat,->(->(Nat,->(Nat,
Nat)),Nat))).abs(plus:->(Nat,->(Nat,Nat)).app(app(app(fact,app(app(app(fact,x),t
imes),plus)),times),plus))))),fix(abs(fact:->(Nat,->(->(Nat,->(Nat,->(->(Nat,->(
Nat,Nat)),Nat))),->(->(Nat,->(Nat,Nat)),Nat))).abs(m:Nat.abs(times:->(Nat,->(Nat
,->(->(Nat,->(Nat,Nat)),Nat))).abs(plus:->(Nat,->(Nat,Nat)).if iszero(m) then su
cc(0) else app(app(app(times,m),app(app(app(fact,pred(m)),times),plus)),plus) fi
)))))),succ(succ(succ(0)))),fix(abs(times:->(Nat,->(Nat,->(->(Nat,->(Nat,Nat)),N
at))).abs(m:Nat.abs(n:Nat.abs(plus:->(Nat,->(Nat,Nat)).if iszero(m) then 0 else
app(app(plus,n),app(app(app(times,pred(m)),n),plus)) fi)))))),fix(abs(plus:->(Na
t,->(Nat,Nat)).abs(m:Nat.abs(n:Nat.if iszero(m) then n else succ(app(app(plus,pr
ed(m)),n)) fi)))))
---Type:---
Nat
---Normal form:---
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(
0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)

-------------------------------------------------------------------------------

TEST8: iseven 7

PCF (unindented):

app (fix (abs (ie:->(Nat,Bool). abs (x:Nat. if iszero(x) then true else
if iszero (pred (x)) then false else app (ie, pred (pred (x))) fi fi))),
succ (succ (succ (succ (succ (succ (succ (0))))))))

Output:

---Term:---
app(fix(abs(ie:->(Nat,Bool).abs(x:Nat.if iszero(x) then true else if iszero(pred
(x)) then false else app(ie,pred(pred(x))) fi fi))),succ(succ(succ(succ(succ(suc
c(succ(0))))))))
---Type:---
Bool
---Normal form:---
false

\end{verbatim}
\end{document}
