%include lhs2TeX.fmt


\section{Applications}
\label{sec:app}

In this section, we show some large examples using \name.

\subsection{Parametric HOAS}
\label{sec:phoas}

Parametric Higher Order Abstract Syntax (PHOAS) is a higher order approach to represent binders, in which the function space of the meta-language is used to encode the binders of the object language. We show that \name can handle PHOAS by encoding lambda calculus as below:

\begin{code}
data PLambda (a : *) = Var a
   | Num nat
   | Lam (a -> PLambda a)
   | App (PLambda a) (PLambda a);
\end{code}

Next we define the evaluator for our lambda calculus. One advantage of PHOAS is that, environments are implicitly handled by the meta-language, thus the type of the evaluator is simply |plambda value -> value|. The code is presented as below:

\begin{code}
data Value  = VI nat
   | VF (Value -> Value);
let eval : PLambda Value -> Value =
   mu ev : PLambda Value -> Value .
     \ e : PLambda Value . case e of
       Var (v : Value) => v
     | Num (n : nat)   => VI n
     | Lam (f : Value -> PLambda Value) =>
         VF (\ x : Value . ev (f x))
     | App (a : PLambda Value) (b : PLambda Value) =>
        case (ev a) of
          VI (n : nat)            => VI n -- impossible to reach
        | VF (f : Value -> Value) => f (ev b)
in
\end{code}

Now we can evaluate some lambda expression and get the result back:

\begin{code}
let show : Value -> nat =
  \ e : Value . case e of
    VI (n : nat)            => n
  | VF (f : Value -> Value) => 10000 -- impossible to reach
in
let example : PLambda Value =
  App Value
      (Lam Value (\ x : Value . Var Value X))
      (Num Value 42)
in
show (eval example) -- return 42
\end{code}
