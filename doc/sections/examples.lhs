%include lhs2TeX.fmt


\section{Applications}
\label{sec:app}

In this section, we show how some large examples using \name

\subsection{Parametric HOAS}
\label{sec:phoas}

Parametric Higher Order Abstract Syntax (PHOAS) is a higher order approach to represent binders, in which the function space of the meta-language is used to encode the binders of the object language. We show that \name can handle PHOAS by encoding lambda calculus as below:

\begin{code}
data plambda (a : *) = var a
  | num nat
  | lam (a -> (plambda a))
  | app (plambda a) (plambda a)
\end{code}

Next we define the evaluator for our lambda calculus. One advantage of PHOAS is that, environments are implicitly handled by the meta-language, thus the type of the evaluator is simply |plambda value -> value|. The code is presented as below:

\begin{code}
data value  = vi nat
  | vf (value -> value);
let eval : plambda value -> value =
   mu ev : plambda value -> value .
     \ e : plambda value . case e of
       var (v : value) => v
     | num (n : nat) => (vi n)
     | lam (f : value -> plambda value) =>
         vf (\ x : value . ev (f x))
     | app (a : plambda value) (b : plambda value) =>
        case (ev a) of
          vi (n : nat) => vi n -- absurd value
        | vf (f : value -> value) => f (ev b)
in
\end{code}

Now we can evaluate some lambda expression and get the result back:

\begin{code}
let show : value -> nat =
  \ e : value . case e of
    vi (n : nat) => n
  | vf (f : value -> value) => 10000 -- absurd value
in
let example : plambda value =
  app value
      (lam value (\ x : value . var value x))
      (num value 42)
in
show (eval example) -- return 42
\end{code}
