%include lhs2TeX.fmt


\section{Applications}
\label{sec:app}

In this section, we show some large examples using \name.

\subsection{Parametric HOAS}
\label{sec:phoas}

Parametric Higher Order Abstract Syntax (PHOAS) is a higher order approach to represent binders, in which the function space of the meta-language is used to encode the binders of the object language. We show that \name can handle PHOAS by encoding lambda calculus as below:

%format . = "."
%format mu = "\mu"

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

\subsection{Perfect binary trees}
\label{sec:binTree}

A perfect binary tree is a binary tree whose size is exactly a power of two. In Haskell, perfect binary trees are usually represented using nested datatypes. We show that \name is able to encode nested datatypes.

First we define a pair datatype as follows:

\begin{code}
  data PairT (a : *) (b : *) = Pair a b;
\end{code}

Using pairs, perfect binary trees are easily defined as:

\begin{code}
  data B (a : *) = One a
   | Two (B (PairT a a));
\end{code}

Notice that the recursive use of \emph{B} does not hold \emph{a}, but \emph{PairT a a}. This means every time we use a \emph{Two} constructor, the size of the pairs doubles. In case you are curious about the encoding of \emph{B}, here is the one:

\begin{code}
  let B : * -> * =
    mu X : * -> * .
      \ a : * . \ B : * . (a -> B) -> (X (PairT a a) -> B) -> B in
\end{code}

Because of the polymorphic recursive type ($\mu X : \star \rightarrow \star $) being used, it is fairly straightforward to encode nested datatypes.

To easily construct a perfect binary tree from a list, we define a help function:

\begin{code}
  let pairs : (a : *) -> List a -> List (PairT a a) =
    mu pairs' : (a : *) -> List a -> List (PairT a a) .
      \ a : * . \ xs : List a .
        case xs of
          Nil => Nil (PairT a a)
        | Cons (y : a) (ys : List a) =>
            case ys of Nil =>
              Nil (PairT a a)
            | Cons (y' : a) (ys' : List a) =>
                Cons (PairT a a) (Pair a a y y') (pairs' a ys')
  in
  let fromList : (a : *) -> List a -> B a =
    mu from' : (a : *) -> List a -> B a .
      \ a : * . \xs : List a .
        case xs of
          Nil => Two a (from' (PairT a a) (pairs a (Nil a)))
        | Cons (x : a) (xs' : List a) =>
          case xs' of
            Nil => One a x
          | Cons (y : a) (zs : List a) =>
              Two a (from' (PairT a a) (pairs a xs))
  in
\end{code}

Now we can define an interesting function \emph{powerTwo}. Given a natural number $n$, it compute the largest natural number $m$, such that $2^{m} < n$:

\begin{code}
  let twos : (a : *) -> B a -> nat =
    mu twos' : (a : *) -> B a -> nat .
      \ a : * . \x : B a .
        case x of
          One (y : a) => 0
        | Two (c : B (PairT a a)) =>
            1 + twos' (PairT a a) c
  in
  let powerTwo : Nat -> nat =
    \ n : Nat . twos nat (fromList nat (take n (repeat 1)))
  in powerTwo (S (S (S (S Z)))) -- return 2
\end{code}
