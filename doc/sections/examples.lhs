%include polycode.fmt
%include format.fmt

%format mu = "\mathsf{mu}"

\section{\sufcc by Example}
\label{sec:app}

\bruno{Wrong title! This section is not about \name; it is about source languages that can be built on top of name!} \jeremy{this name for the moment}

\bruno{General comment is that, although the material is good, the text is a bit informally written.
Text needs to be polsihed. Also the text is lacking references.}

This sections shows a number of programs written in the surface
language \sufcc, which in built on top of \name. Most of these
examples either require non-trivial extensions of Haskell, or are
non-trivial to encode in dependently typed language like Coq or
Agda. The formalization of the surface language is presented in
Section~\ref{sec:surface}.

\begin{comment}
\subsection{Parametric HOAS}
\label{sec:phoas}

Parametric Higher Order Abstract Syntax (PHOAS) is a higher order
approach to represent binders, in which the function space of the
meta-language is used to encode the binders of the object language. We
show that \name can handle PHOAS by encoding lambda calculus as below:

\begin{figure}[h!]
\begin{spec}
data PLambda (a : *) = Var a
   | Num nat
   | Lam (a -> PLambda a)
   | App (PLambda a) (PLambda a);
\end{spec}
\end{figure}

Next we define the evaluator for our lambda calculus. One advantage of
PHOAS is that, environments are implicitly handled by the
meta-language, thus the type of the evaluator is simply |plambda value
-> value|. The code is presented in Figure~\ref{fig:phoas}.

\begin{figure}[ht]
\begin{spec}
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
\end{spec}
  \caption{Lambda Calculus in PHAOS}
  \label{fig:phoas}
\end{figure}

Now we can evaluate some lambda expression and get the result back as
in Figure~\ref{fig:pex}

\begin{figure}[ht]
\begin{spec}
let show : Value -> nat =
  \ e : Value . case e of
    VI (n : nat)            => n
  | VF (f : Value -> Value) => 10000 -- impossible to reach
in
let example : PLambda Value =
  App Value
      (Lam Value (\ x : Value . Var Value X))
      (Num Value 42)
in show (eval example) -- return 42
\end{spec}
\caption{Example of using PHOAS}
\label{fig:pex}
\end{figure}
\end{comment}

\subsubsection{Datatypes}
Conventional datatypes like natural numbers or polymorphic lists can
be easily defined in \sufcc, \bruno{This is not name; its the source
  language built on top of name!} \jeremy{changed} as in Haskell. For
example, below is the definition of polymorphic lists:

<  data List (a : *) = Nil | Cons a (List a);


Because \sufcc \bruno{You'll have to stop referring to \name in this
  section. You may want to consider giving the source language a
  name.} \jeremy{changed} is explicitly typed, each type parameter
needs to be accompanied with a corresponding kind expression. The use
of the above datatype is best illustrated by the \emph{length}
function:

< letrec length : (a : *) -> List a -> nat =
<   \ a : * . \l : List a . case l of
<      Nil => 0
<   |  Cons (x : a) (xs : List a) => 1 + length a xs
< in
< let test : List nat = Cons nat 1 (Cons nat 2 (Nil nat))
< in length nat test -- return 2

\subsubsection{Higher-kinded Types}
Higher-kinded types are types that take other types and produce a new
type. To support higher-kinded types, languages like Haskell have to
extend their existing core languages to account for kind expressions.
(The existing core language of Haskell, System FC, is an extension of
System $F_{\omega}$~\cite{systemfw}, which naively supports
higher-kinded types.) \bruno{Probably want to mention $F_{\omega}$}
\jeremy{done!}  Given that \sufcc subsumes System $F_{\omega}$, we can
easily construct higher-kinded types. We show this by an example of
encoding the \emph{Functor} class:

< rcrd Functor (f : * -> *) =
<   Func {fmap : (a : *) -> (b : *) -> f a -> f b};

A functor is just a record that has only one field \emph{fmap}. A
Functor instance of the \emph{Maybe} datatype is:

< let maybeInst : Functor Maybe =
<   Func Maybe (\ a : * . \ b : * . \f : a -> b . \ x : Maybe a .
<     case x of
<       Nothing => Nothing b
<    |  Just (z : a) => Just b (f z))

\subsubsection{HOAS}

\emph{Higher-order abstract syntax} is a representation of abstract
syntax where the function space of the meta-language is used to encode
the binders of the object language. Because of the recursive
occurrence of the datatype appears in a negative position (i.e., in
the left side of a function arrow) \bruno{explain where!}
\jeremy{done!}, systems like Coq and Agda would reject such programs using
HOAS due to the restrictiveness of their termination checkers. However
\sufcc is able to express HOAS in a straightforward way. We show an
example of encoding a simple lambda calculus:

< data Exp = Num nat
<   |  Lam (Exp -> Exp)
<   |  App Exp Exp;


Next we define the evaluator for our lambda calculus. As noted
by~\cite{Fegaras1996}, the evaluation function needs an extra function
\emph{reify} to invert the result of evaluation.

< data Value = VI nat | VF (Value -> Value);
< rcrd Eval = Ev { eval' : Exp -> Value, reify' : Value -> Exp };
< let f : Eval = mu f' : Eval .
<   Ev  (\ e : Exp . case e of
<         Num (n : nat) => VI n
<       | Lam (fun : Exp -> Exp) =>
<           VF (\e' : Value . eval' f' (fun (reify' f' e')))
<       | App (a : Exp) (b : Exp) =>
<           case eval' f' a of
<             VI (n : nat) => error
<           | VF (fun : Value -> Value) => fun (eval' f' b))
<       (\v : Value . case v of
<         VI (n : nat) => Num n
<       | VF (fun : Value -> Value) =>
<           Lam (\e' : Exp . (reify' f' (fun (eval' f' e')))))
< in let eval : Exp -> Value = eval' f in


The definition of the evaluator is quite straightforward, although it
is worth noting that the evaluator is a partial function that can
cause run-time errors. Thanks to the flexibility of the $\mu$
primitive, mutual recursion can be encoded by using records!

Evaluation of a lambda expression proceeds as follows:

< let test : Exp = App  (Lam (\ f : Exp . App f (Num 42)))
<                       (Lam (\g : Exp. g))
< in show (eval test) -- return 42

\subsubsection{Fix as a Datatype}
The type-level \emph{Fix} is a good example to demonstrate the
expressiveness of \sufcc. The definition is:

< rcrd Fix (f : * -> *) = In {out : (f (Fix f)) };

The record notation also introduces the selector function: |out : (f :
* -> *) -> Fix f -> f (Fix f)|.  The \emph{Fix} datatype is
interesting in that now we can define recursive datatypes in a
non-recursive way. For instance, a non-recursive definition for
natural numbers is:

< data NatF (self : *) = Zero | Succ self;

And the recursive version is just a synonym:

< let Nat : * = Fix NatF


Note that now we can use the above \emph{Nat} anywhere, including the
left-hand side of a function arrow, which is a potential source of
non-termination. The termination checker of Coq or Agda is so
conservative that it would brutally reject the definition of
\emph{Fix} to avoid the above situation. \bruno{show example?}
\jeremy{done!} However in \sufcc, where type-level computation is
explicitly controlled, we can safely use \emph{Fix} in the program.

Given \emph{fmap}, many recursive shcemes can be defined, for example
we can have \emph{catamorphism}~\cite{Meijer1991} \bruno{reference?}
\jeremy{done!} or generic function fold:

< letrec cata :  (f : * -> *) -> (a : *) ->
<                Functor f -> (f a -> a) -> Fix f -> a =
<   \f : * -> * . \ a : * . \ m : Functor f . \ g : f a -> a. \ t : Fix f .
<     g (fmap f m (Fix f) a (cata f a m g) (out f t))

\subsubsection{Kind Polymophism}
In Haskell, System FC~\cite{fc:pro} \bruno{reference} \jeremy{done!}
was proposed to support kind polymorphism. However it separates
expressions into terms, types and kinds, which complicates both the
implementation and future extensions. \sufcc natively allows datatype
definitions to have polymorphic kinds. Here is an example, taken
from~\cite{fc:pro}, of a datatype that benefits from kind polymophism:
a higher-kinded fixpoint combinator:

< data Mu (k : *) (f : (k -> *) -> k -> *) (a : k) =
<   Roll (f (Mu k f) a);

\emph{Mu} can be used to construct polymorphic recursive types of any kind, for instance:

< data Listf (f : * -> *) (a : *) = Nil | Cons a (f a);
< let List : * -> * = \a : * . Mu * Listf a

\subsubsection{Nested Datatypes}

A nested datatype~\cite{nesteddt} \bruno{reference} \jeremy{done!},
also known as a \emph{non-regular} datatype, is a parametrised
datatype whose definition contains different instances of the type
parameters. Functions over nested datatypes usually involve
polymorphic recursion. We show that \sufcc is capable of defining all
useful functions over a nested datatype. A simple example would be the
type \emph{Pow} of power trees, whose size is exactly a power of two,
declared as follows:

< data PairT (a : *) = P a a;
< data Pow (a : *) = Zero a | Succ (Pow (PairT a));

Notice that the recursive mention of \emph{Pow} does not hold
\emph{a}, but \emph{PairT a}. This means every time we use a
\emph{Succ} constructor, the size of the pairs doubles. In case you
are curious about the encoding of \emph{Pow}, here is the one:

< let Pow : * -> * = mu X : * -> * .
<     \ a : * . (B : *) -> (a -> B) -> (X (PairT a) -> B) -> B

Notice how the higher-kinded type variable |X : * -> *| helps encoding
nested datatypes. Below is a simple function \emph{toList} that
transforms a power tree into a list:

< letrec toList : (a : *) -> Pow a -> List a =
<   \a : * . \t : Pow a . case t of
<      Zero (x : a) => Cons a x (Nil a)
<   |  Succ (c : Pow (PairT a)) =>
<        concatMap (PairT a) a
<          (\ x : PairT a . case x of
<             P (m : a) (n : a) =>
<               Cons a m (Cons a n (Nil a)))
<          (toList (PairT a) c)

\subsubsection{Data Promotion}
\bruno{what is the point that we are trying to make with this example? Title is wrong;
should be about the point, not about the particular example!} \jeremy{This section shows we can do data promotion much more easily than in Haskell}

Haskell needs sophisticated extensions~\cite{fc:pro} in order for
being able to use ordinary datatypes as kinds, and data constructors
as types. With the full power of dependent types, data promotion is
made trivial in \sufcc.

As a last example, we show a representation of a labeled binary tree,
where each node is labeled with its depth in the tree. Below is the
definition:

< data PTree (n : Nat) = Empty
<   | Fork nat (PTree (S n)) (PTree (S n));

Notice how the datatype \emph{Nat} is ``promoted'' to be used in the
kind level. Next we can construct such a binary tree that keeps track
of its depth statically:
< Fork Z 1 (Empty (S Z)) (Empty (S Z))
If we accidentally write the wrong depth, for example:
< Fork Z 1 (Empty (S Z)) (Empty Z)
The above will fail to pass type checking.

\bruno{Two questions: firstly does it work? secondly do we support GADT syntax now?}  \jeremy{changed to a simple binary tree example}

\bruno{More examples? closed type families; dependent types?} \jeremy{had hard time thinking of a simple, non-recursive example for type families}
