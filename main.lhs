%% Literate Haskell script intended for lhs2TeX.

\documentclass[10pt]{article}
%include polycode.fmt

%format union = "\cup"
%format `union` = "\cup"
%format Hole = "\square"
%format alpha = "\alpha"
%format gamma = "\gamma"
%format zeta = "\zeta"
%format kappa = "\kappa"
%format kappa'
%format capGamma = "\Gamma"
%format sigma = "\sigma"
%format tau = "\tau"
%format taus = "\tau s"
%format ltaus = "l\tau s"
%format tau1
%format tau1'
%format tau2
%format tau11
%format tau12
%format upsilon = "\upsilon"
%format xi = "\xi"
%format t12
%format t1
%format t1'
%format t2
%format t2'
%format t3
%format nv1

\usepackage{fullpage}
\usepackage{mathpazo}
\usepackage{graphicx}
\usepackage{color}
\usepackage[centertags]{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{stmaryrd}

\title{CS555 Project Exercise 3}
\author{Mahnush Movahedi, Mahdi Zamani, Vlado Ovtcharov}
\date{May 5, 2012}
\begin{document}
\maketitle
\fontfamily{Euclid}\fontsize{4.1mm}{5.3mm}\selectfont
\thispagestyle{empty}
In this exercise, we implemented the nameless representation (DeBruijn notation), natural semantics with nameless representation, the CES machine, the Continuation-Passing-Style (CPS) transformation, and the CE3R machine. Our first attempt for adding types to the CPS is based on [1]. We have also implemented the solution proposed in [2] as the second attempt to CPS tranformation.

\section{De Bruijn notation}
%include DeBruijn.lhs

\section{Natural semantics with nameless terms}
%include NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices.lhs

\section{CES compiler and virtual machine}
%include CESMachine.lhs

\section{CPS transformation}
Our first attempt for adding types to the CPS is based on [1]. We have also implemented the solution proposed in [2] as the second attempt.
\subsection{CPS attempt 1}
%include CPS.lhs
\subsection{CPS attempt 2}
%include Syntax/CPS.lhs

\section{CE3R compiler and virtual machine}
%include CE3RMachine.lhs

\section{Main program}
\begin{code}
module Main (
    main
) where

import TypeCheck
import AbstractSyntax
import System.Environment
import qualified DeBruijn as D
import qualified CESMachine as C
import qualified StructuralOperationalSemantics as S
import qualified NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices as N
import qualified Syntax.CPS as SP
import qualified CPS as P
import qualified Syntax.SyntaxB as B
import qualified Syntax.SyntaxC as X
import qualified CE3RMachine as R

main =
    do
      args <- System.Environment.getArgs
      let [sourceFile] = args
      source <- readFile sourceFile
      putStrLn ("---Input:---")
      putStrLn (source)
      let tokens = scan source
      let term = parse tokens

      putStrLn ("---Term:---")
      putStrLn (show term)

      let tau = typeCheck term
      putStrLn ("---Type:---")
      putStrLn (show tau)

      let deBruijnTerm = D.toDeBruijn term
      putStrLn ("---DeBruijn Notation:---")
      putStrLn (show (deBruijnTerm))

      putStrLn ("---Normal form (Structural semantics):---")
      putStrLn (show (S.eval term))

      putStrLn ("---Normal form (Natural semantics with DeBruijn indices):---")
      putStrLn (show (N.eval deBruijnTerm))

      putStrLn ("---Normal form (CES machine):---")
      putStrLn (show (C.eval deBruijnTerm))

      let cpsTerm1 = P.toCPS' term
      let cpsDeBruijnTerm1 = D.toDeBruijn (App cpsTerm1 (Abs "a" tau (Var "a")))

      putStrLn ("---Normal form (CE3R machine on CPS1):---")
      putStrLn (show (R.eval cpsDeBruijnTerm1))

      let cpsTerm2 = case SP.toCPSe (B.fromSyntaxA term) of
                       Just t    -> t
                       otherwise -> error "CPS error!"
                           
      putStrLn ("---CPS2 Type:---")
      putStrLn (show (SP.checkType (X.stripTags cpsTerm2)))
      
      let cpsDeBruijnTerm2 = D.toDeBruijn (B.toSyntaxA (X.stripTags cpsTerm2))

      putStrLn ("---Normal form (CE3R machine on CPS2):---")
      putStrLn (show (R.eval cpsDeBruijnTerm2))      
\end{code}

\section{Appendix: Test results}
\subsection{Test 1}
\begin{verbatim}
---Input:---
let
  iseven =
    let
      mod = abs (m:Int. abs (n:Int. -(m,*(n,/(m,n)))))
    in
      abs (k:Int. =(0, app(app(mod,k),2)))
    end
in
  app (iseven, 7)
end
---Term:---
let iseven = let mod = abs(m.abs(n."m"-"n"*"m"/"n")) in abs(k.0=app(app("mod", "
k"), 2)) in app("iseven", 7)
---Type:---
Bool
---DeBruijn Notation:---
let let abs(abs(~1-~0*~1/~0)) in abs(0=app(app(~1,~0),2)) in app(~0,7)
---Normal form (Structural semantics):---
False
---Normal form (Natural semantics with DeBruijn indices):---
False
---Normal form (CES machine):---
False
---Normal form (CE3R machine on CPS1):---
False
---CPS2 Type:---
Just ((Bool -> Bool) -> Bool)
---Normal form (CE3R machine on CPS2):---
False
\end{verbatim}

\subsection{Test 2}
\begin{verbatim}
---Input:---
+(+(+(5,3),+(9,10)),+(+(15,13),14))
---Term:---
5+3+9+10+15+13+14
---Type:---
Int
---DeBruijn Notation:---
5+3+9+10+15+13+14
---Normal form (Structural semantics):---
69
---Normal form (Natural semantics with DeBruijn indices):---
69
---Normal form (CES machine):---
69
---Normal form (CE3R machine on CPS1):---
69
---CPS2 Type:---
Just ((Int -> Int) -> Int)
---Normal form (CE3R machine on CPS2):---
69
\end{verbatim}

\subsection{Test 3}
\begin{verbatim}
---Input:---
app (
    abs (x: Int.
        if <(/(12,3),*(2,6)) then
            app( abs(x: Int . if <(x,10) then *(x,3) else *(x,4) fi), *(x,15))
        else 7
        fi
    ), 2
)
---Term:---
app(abs(x.if 12/3<2*6 then app(abs(x.if "x"<10 then "x"*3 else "x"*4 fi), "x"*15
) else 7 fi), 2)
---Type:---
Int
---DeBruijn Notation:---
app(abs(if 12/3<2*6 then app(abs(if ~0<10 then ~0*3 else ~0*4 fi),~0*15) else 7
fi),2)
---Normal form (Structural semantics):---
120
---Normal form (Natural semantics with DeBruijn indices):---
120
---Normal form (CES machine):---
120
---Normal form (CE3R machine on CPS1):---
120
---CPS2 Type:---
Just ((Int -> Int) -> Int)
---Normal form (CE3R machine on CPS2):---
120
\end{verbatim}

\subsection{Test 4}
\begin{verbatim}
---Input:---
+(if <(5,3) then 4 else 6 fi,7)
---Term:---
if 5<3 then 4 else 6 fi+7
---Type:---
Int
---DeBruijn Notation:---
if 5<3 then 4 else 6 fi+7
---Normal form (Structural semantics):---
13
---Normal form (Natural semantics with DeBruijn indices):---
13
---Normal form (CES machine):---
13
---Normal form (CE3R machine on CPS1):---
13
---CPS2 Type:---
Just ((Int -> Int) -> Int)
---Normal form (CE3R machine on CPS2):---
13
\end{verbatim}

\subsection{Test 5}
\begin{verbatim}
---Input:---
app(
   abs(x:Int.
      +(
        app(
            abs(z:Int.
               +(
                 app(
                    abs(x:Int.+(x,z)),
                    5
                 ),
                 app(
                    abs(y:Int.+(y,z)),
                    6
                 )
               )
            ), 7
        ), x
      )
   ),
   8
)
---Term:---
app(abs(x.app(abs(z.app(abs(x."x"+"z"), 5)+app(abs(y."y"+"z"), 6)), 7)+"x"), 8)
---Type:---
Int
---DeBruijn Notation:---
app(abs(app(abs(app(abs(~0+~1),5)+app(abs(~0+~1),6)),7)+~0),8)
---Normal form (Structural semantics):---
33
---Normal form (Natural semantics with DeBruijn indices):---
33
---Normal form (CES machine):---
33
---Normal form (CE3R machine on CPS1):---
33
---CPS2 Type:---
Just ((Int -> Int) -> Int)
---Normal form (CE3R machine on CPS2):---
33
\end{verbatim}

\subsection{Test 6}
\begin{verbatim}
---Input:---
app(
    fix (
        abs (f:->(Int,Int).
            abs (x:Int.
                if =(x,0) then
                    1
                else
                    *(x, app (f,-(x,1)))
                fi
            )
        )
    ), 10
)
---Term:---
app(fix(abs(f.abs(x.if "x"=0 then 1 else "x"*app("f", "x"-1) fi))), 10)
---Type:---
Int
---DeBruijn Notation:---
app(fix(abs(abs(if ~0=0 then 1 else ~0*app(~1,~0-1) fi))),10)
---Normal form (Structural semantics):---
3628800
---Normal form (Natural semantics with DeBruijn indices):---
3628800
---Normal form (CES machine):---
3628800
---Normal form (CE3R machine on CPS1):---
Failed
---CPS2 Type:---
Failed
---Normal form (CE3R machine on CPS2):---
Failed
\end{verbatim}

\subsection{Test 7}
\begin{verbatim}
---Input:---
app (fix (abs (ie:->(Int,Bool). abs (x:Int. if =(0,x) then true else
if =(0, -(x,1)) then false else app (ie, -(x,2)) fi fi))), 7)

---Term:---
app(fix(abs(ie.abs(x.if 0="x" then true else if 0="x"-1 then false else app("ie"
, "x"-2) fi fi))), 7)
---Type:---
Bool
---DeBruijn Notation:---
app(fix(abs(abs(if 0=~0 then true else if 0=~0-1 then false else app(~1,~0-2) fi
 fi))),7)
---Normal form (Structural semantics):---
False
---Normal form (Natural semantics with DeBruijn indices):---
False
---Normal form (CES machine):---
False
---Normal form (CE3R machine on CPS1):---
Failed
---CPS2 Type:---
Failed
---Normal form (CE3R machine on CPS2):---
Failed
\end{verbatim}

\subsection{Test 8}
\begin{verbatim}
---Input:---
let
   iseven = fix (abs (ie:->(Int,Bool). abs (x:Int.
              if =(0,x) then true else
                if =(1,x) then false else
                  app (ie, -(x,2)) fi fi)))
in
  let
    collatz = fix (abs (c:->(Int,Int). abs (x: Int.
                if app (iseven, x) then app (c, /(x,2)) else
                  if =(x,1) then 1 else
                    app (c, +(*(3,x),1)) fi fi)))
  in
    app (collatz, 1000)
  end
end
---Term:---
let iseven = fix(abs(ie.abs(x.if 0="x" then true else if 1="x" then false else a
pp("ie", "x"-2) fi fi))) in let collatz = fix(abs(c.abs(x.if app("iseven", "x")
then app("c", "x"/2) else if "x"=1 then 1 else app("c", 3*"x"+1) fi fi))) in
app("collatz",1000)
---Type:---
Int
---DeBruijn Notation:---
let fix(abs(abs(if 0=~0 then true else if 1=~0 then false else app(~1,~0-2) fi f
i))) in let fix(abs(abs(if app(~2,~0) then app(~1,~0/2) else if ~0=1 then 1 else
 app(~1,3*~0+1) fi fi))) in app(~0,1000)
---Normal form (Structural semantics):---
1
---Normal form (Natural semantics with DeBruijn indices):---
1
---Normal form (CES machine):---
1
---Normal form (CE3R machine on CPS1):---
Failed
---CPS2 Type:---
Failed
---Normal form (CE3R machine on CPS2):---
Failed
\end{verbatim}

\subsection{Test 9}
\begin{verbatim}
---Input:---
app(
  abs (x: Int .
      abs (y: Int .
          +(
             +(x,y),
             app (abs (x: Int . +(x,y)), 3)
          )
      )
  ),
  app (abs (x: Int . x), 5)
)
---Term:---
app(abs(x.abs(y."x"+"y"+app(abs(x."x"+"y"), 3))), app(abs(x."x"), 5))
---DeBruijn Notation:---
app(abs(abs(~1+~0+app(abs(~0+~1),3))),app(abs(~0),5))
---Normal form (Structural semantics):---
abs(y.5+"y"+app(abs(x."x"+"y"), 3))
---Normal form (Natural semantics with DeBruijn indices):---
Function: Clo abs(~1+~0+app(abs(~0+~1),3)) [5]
---Normal form (CES machine):---
Clo [Access 1,Access 0,Add,Close [Access 0,Access 1,Add,Return],Int 3,Apply,Add,
Return] [5]
---Normal form (CE3R machine on CPS1):---
Clo [Close1 [Close1 [~1 0,~2 5,App1],Close2 [Close1 [~1 0,~2 4,App1],Close2 [~1
2,~2 1,~3 0,Add],App1],App1],Close2 [Close1 [Close1 [~1 0,Close2 [Close1 [~1 0,~
2 2,App1],Close2 [Close1 [~1 0,~2 8,App1],Close2 [~1 2,~2 1,~3 0,Add],App1],App1
],App1],Close2 [Close1 [~1 0,Int2 3,App1],Close2 [~1 1,~2 0,~3 2,App2],App1],App
1],Close2 [~1 2,~2 1,~3 0,Add],App1],App1] [Clo [~1 0] [],5,Clo [Close1 [Close1
[~1 0,Close2 [~1 0,~2 1,App1],App1],Close2 [Close1 [~1 0,Int2 5,App1],Close2 [~1
 1,~2 0,~3 2,App2],App1],App1],Close2 [~1 1,~2 0,~3 2,App2],App1] [Clo [~1 0] []
],Clo [~1 0] []]
---CPS2 Type:---
Just (((((Int -> ((((Int -> (((Int -> ((Int -> (((Int -> ((Int -> (Int -> Int))
-> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int
-> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int)))) -> (((Int -> ((In
t -> (Int -> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int))) -> (((In
t -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int)))
) -> (((Int -> ((Int -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (I
nt -> Int)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int
))) -> (Int -> Int)) -> (Int -> Int)))) -> (((Int -> ((Int -> (Int -> Int)) -> (
Int -> Int))) -> (Int -> Int)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int -> I
nt)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int)))) -> (((Int -> ((Int ->
 (Int -> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int))) -> (((Int ->
 ((Int -> (Int -> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int)))) ->
 (((Int -> ((Int -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (Int ->
 Int)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int)))
-> (Int -> Int)) -> (Int -> Int)))) -> (((Int -> ((Int -> (Int -> Int)) -> (Int
-> Int))) -> (Int -> Int)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int -> Int))
 -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int)))) -> (((Int -> ((Int -> (((
Int -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (Int -> Int)
)) -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (Int -> Int)) -> (In
t -> Int)))) -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (Int -> In
t)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> Int))) -> (
Int -> Int)) -> (Int -> Int)))) -> (((Int -> ((Int -> (Int -> Int)) -> (Int -> I
nt))) -> (Int -> Int)) -> (Int -> Int))) -> (((Int -> ((Int -> (Int -> Int)) ->
(Int -> Int))) -> (Int -> Int)) -> (Int -> Int)))
---Normal form (CE3R machine on CPS2):---
Clo [Close1 [~1 0,Close2 [~1 0,Close2 [Close1 [Close1 [~1 0,~2 5,App1],Close2 [C
lose1 [~1 0,~2 4,App1],Close2 [~1 2,~2 1,~3 0,Add],App1],App1],Close2 [Close1 [C
lose1 [~1 0,Close2 [Close1 [~1 0,~2 2,App1],Close2 [Close1 [~1 0,~2 8,App1],Clos
e2 [~1 2,~2 1,~3 0,Add],App1],App1],App1],Close2 [Close1 [~1 0,Int2 3,App1],Clos
e2 [~1 1,~2 0,~3 2,App2],App1],App1],Close2 [~1 2,~2 1,~3 0,Add],App1],App1],App
1],App1],Close2 [Close1 [Close1 [~1 0,Close2 [~1 0,~2 1,App1],App1],Close2 [Clos
e1 [~1 0,Int2 5,App1],Close2 [~1 1,~2 0,~3 2,App2],App1],App1],Close2 [~1 1,~2 0
,~3 2,App2],App1],App1] []
\end{verbatim}

\begin{thebibliography}{1}
\bibitem{griffin} Timothy G. Griffin, {\em A Formulae-as-Types Notion of Control}, 1990: In Conference Record of the Seventeenth Annual ACM Symposium on Principles of Programming Languages, ACM Press.

\bibitem{danvy} Olivier Danvy and Andrzej Filinski, {\em Representing control: a study of the CPS transformation}, 1992.
\end{thebibliography}

\end{document}
