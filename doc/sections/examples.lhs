%include lhs2TeX.fmt

%format . = ".\,"
%format mu = "\mu"
%format * = "\star"
%format letrec = "\mathbf{letrec}"
%format rcrd = "\mathbf{rcrd}"


\section{Showcase}
\label{sec:app}

In this section, we showcase applications, which either Haskell needs non-trivial extensions to do that, or dependently typed languages like Coq and Agda are impossible to do, whereas we can easily achieve in \name.

% \subsection{Parametric HOAS}
% \label{sec:phoas}

% Parametric Higher Order Abstract Syntax (PHOAS) is a higher order approach to represent binders, in which the function space of the meta-language is used to encode the binders of the object language. We show that \name can handle PHOAS by encoding lambda calculus as below:

% \begin{figure}[h!]
% \begin{spec}
% data PLambda (a : *) = Var a
%    | Num nat
%    | Lam (a -> PLambda a)
%    | App (PLambda a) (PLambda a);
% \end{spec}
% \end{figure}

% Next we define the evaluator for our lambda calculus. One advantage of PHOAS is that, environments are implicitly handled by the meta-language, thus the type of the evaluator is simply |plambda value -> value|. The code is presented in Figure~\ref{fig:phoas}.

% \begin{figure}[ht]
% \begin{spec}
% data Value  = VI nat
%    | VF (Value -> Value);
% let eval : PLambda Value -> Value =
%    mu ev : PLambda Value -> Value .
%      \ e : PLambda Value . case e of
%        Var (v : Value) => v
%      | Num (n : nat)   => VI n
%      | Lam (f : Value -> PLambda Value) =>
%          VF (\ x : Value . ev (f x))
%      | App (a : PLambda Value) (b : PLambda Value) =>
%         case (ev a) of
%           VI (n : nat)            => VI n -- impossible to reach
%         | VF (f : Value -> Value) => f (ev b)
% in
% \end{spec}
%   \caption{Lambda Calculus in PHAOS}
%   \label{fig:phoas}
% \end{figure}

% Now we can evaluate some lambda expression and get the result back as in Figure~\ref{fig:pex}

% \begin{figure}[ht]
% \begin{spec}
% let show : Value -> nat =
%   \ e : Value . case e of
%     VI (n : nat)            => n
%   | VF (f : Value -> Value) => 10000 -- impossible to reach
% in
% let example : PLambda Value =
%   App Value
%       (Lam Value (\ x : Value . Var Value X))
%       (Num Value 42)
% in show (eval example) -- return 42
% \end{spec}
% \caption{Example of using PHOAS}
% \label{fig:pex}
% \end{figure}

\subsubsection{Conventional datatypes}

Conventional datatypes like natural numbers or polymorphic lists can be easily defined in \name, as in Haskell. For example, below is the definition of polymorphic lists:

\begin{figure}[H]
\begin{spec}
  data List (a : *) = Nil | Cons a (List a);
\end{spec}
\end{figure}

Because \name is explicitly typed, each type parameter needs to be accompanied with corresponding kind expressions. The use of the above datatype is best illustrated by the \emph{length} function:

\begin{figure}[h!]
  \begin{spec}
    letrec length : (a : *) -> List a -> nat =
      \ a : * . \l : List a . case l of
         Nil => 0
      |  Cons (x : a) (xs : List a) => 1 + length a xs
    in
    let test : List nat = Cons nat 1 (Cons nat 2 (Nil nat))
    in length nat test -- return 2
  \end{spec}
\end{figure}

\subsubsection{Higher-kinded types}

Higher-kinded types are types that take other types and produce a new type. To support higher-kinded types, languages like Haskell have to extend their existing core languages to account for kind expressions. In \name, since all syntactical constructs are in the same level, we can easily construct higher-kinded types. We show this by an example of encoding the \emph{Functor} class:

\begin{figure}[h!]
  \begin{spec}
    rcrd Functor (f : * -> *) =
      Func {fmap : (a : *) -> (b : *) -> f a -> f b};
  \end{spec}
\end{figure}

A functor is just a record that has only one field \emph{fmap}. A Functor instance of the \emph{Maybe} datatype is simply:

\begin{figure}[h!]
  \begin{spec}
    let maybeInst : Functor Maybe =
      Func Maybe (\ a : * . \ b : * . \f : a -> b . \ x : Maybe a .
        case x of
          Nothing => Nothing b
       |  Just (z : a) => Just b (f z))
  \end{spec}
\end{figure}

\subsubsection{HOAS}

\emph{Higher-order abstract syntax} is a generalization of representing programs where the function space of the meta-language is used to encode the binders of the object language. Because the recursive mention of the datatype can appear in a negative position, systems like Coq and Agda would reject programs using HOAS due to the restrictiveness of their termination checkers. However \name is able to express HOAS in a straightforward way. We show an example of encoding a simple lambda calculus:

\begin{figure}[h!]
\begin{spec}
  data Exp = Num nat
    |  Lam (Exp -> Exp)
    |  App Exp Exp;
\end{spec}
\end{figure}

Next we define the evaluator for our lambda calculus. As noted by~\cite{Fegaras1996}, the evaluation function needs an extra function \emph{reify} to invert the result of evaluation. The code is presented in Figure~\ref{fig:hoas}.

\begin{figure}[ht]
\begin{spec}
data Value = VI nat | VF (Value -> Value);
rcrd Eval = Ev { eval' : Exp -> Value, reify' : Value -> Exp };
let f : Eval = mu f' : Eval .
  Ev  (\ e : Exp . case e of
        Num (n : nat) => VI n
      | Lam (fun : Exp -> Exp) =>
          VF (\e' : Value . eval' f' (fun (reify' f' e')))
      | App (a : Exp) (b : Exp) =>
          case eval' f' a of
            VI (n : nat) => error
          | VF (fun : Value -> Value) => fun (eval' f' b))
      (\v : Value . case v of
        VI (n : nat) => Num n
      | VF (fun : Value -> Value) =>
          Lam (\e' : Exp . (reify' f' (fun (eval' f' e')))))
in let eval : Exp -> Value = eval' f in
\end{spec}
  \caption{An evaluator for the HOAS-encoded lambda calculus.}
  \label{fig:hoas}
\end{figure}

The definition of the evaluator is quite straightforward, although it is worth noting that the evaluator is a partial function that can cause run-time errors. Thanks to the flexibility of the $\mu$ primitive, mutual recursion can be encoded by using records!

Evaluation of a lambda expression proceeds as follows:

\begin{figure}[H]
  \begin{spec}
  let test : Exp = App  (Lam (\ f : Exp . App f (Num 42)))
                        (Lam (\g : Exp. g))
  in show (eval test) -- return 42
  \end{spec}
\end{figure}

\subsubsection{Fix as a datatype}

The type-level \emph{Fix} is a good example to demonstrate the expressiveness of \name. The definition is simply:

\begin{figure}[H]
  \begin{spec}
    rcrd Fix (f : * -> *) = In {out : (f (Fix f)) };
  \end{spec}
\end{figure}

The record notation also introduces the selector function: |out : (f : * -> *) -> Fix f -> f (Fix f)|. The \emph{Fix} datatype is interesting in that Coq and Agda would reject this definition because the use of the higher-kinded type parameter \emph{f} could be anywhere (e.g., in a negative position). However in \name, where type-level computation is explicitly controlled, we can safely use \emph{Fix} in the program.

Given \emph{fmap}, many recursive shcemes can be defined, for example  we can have \emph{catamorphism} or generic function fold:

\begin{figure}[H]
  \begin{spec}
    letrec cata :  (f : * -> *) -> (a : *) ->
                   Functor f -> (f a -> a) -> Fix f -> a =
      \f : * -> * . \ a : * . \ m : Functor f . \ g : f a -> a. \ t : Fix f .
        g (fmap f m (Fix f) a (cata f a m g) (out f t))
  \end{spec}
\end{figure}


\subsubsection{Kind polymophism for datatypes}

In Haskell, System $F_{c}^{\uparrow}$ was proposed to support kind polymorphism. However it separates expressions into terms, types and kinds, which complicates both the implementation and future extensions. \name natively allows datatype definitions to have polymorphic kinds. Here is an example, taken from~\cite{fc:pro}, of a datatype that benefits from kind polymophism: higher-kinded fixpoint combinator

\begin{figure}[H]
  \begin{spec}
    data Mu (k : *) (f : (k -> *) -> k -> *) (a : k) =
      Roll (f (Mu k f) a);
  \end{spec}
\end{figure}

\emph{Mu} can be used to construct polymorphic recursive types of any kind, for instance:

\begin{figure}[H]
  \begin{spec}
    data Listf (f : * -> *) (a : *) = Nil | Cons a (f a);
    let List : * -> * = \a : * . Mu * Listf a
  \end{spec}
\end{figure}

\subsubsection{Nested datatypes and polymorphic recursion}

A nested datatype, also known as a \emph{non-regular} datatype, is a parametrised datatype whose definition contains different instances of the type parameters. Functions over nested datatypes usually involve polymorphic recursion. We show that \name is capable of defining all useful functions over a nested datatype. A simple example would be the type \emph{Pow} of power trees, whose size is exactly a power of two, declared as follows:

\begin{figure}[H]
\begin{spec}
  data PairT (a : *) = P a a;
  data Pow (a : *) = Zero a | Succ (Pow (PairT a));
\end{spec}
\end{figure}

Notice that the recursive mention of \emph{Pow} does not hold \emph{a}, but \emph{PairT a}. This means every time we use a \emph{Succ} constructor, the size of the pairs doubles. In case you are curious about the encoding of \emph{Pow}, here is the one:

\begin{figure}[H]
\begin{spec}
  let Pow : * -> * = mu X : * -> * .
      \ a : * . (B : *) -> (a -> B) -> (X (PairT a) -> B) -> B
\end{spec}
\end{figure}

Notice how the higher-kinded type variable |X : * -> *| helps encoding nested datatypes. Below is a simple function \emph{toList} that transforms a power tree into a list:

\begin{figure}[H]
  \begin{spec}
    letrec toList : (a : *) -> Pow a -> List a =
      \a : * . \t : Pow a . case t of
         Zero (x : a) => Cons a x (Nil a)
      |  Succ (c : Pow (PairT a)) =>
           concatMap (PairT a) a
             (\ x : PairT a . case x of
                P (m : a) (n : a) =>
                  Cons a m (Cons a n (Nil a)))
             (toList (PairT a) c)
  \end{spec}
\end{figure}



% \subsubsection{Nested datatypes}
% \label{sec:binTree}

% A perfect binary tree is a binary tree whose size is exactly a power of two. In Haskell, perfect binary trees are usually represented using nested datatypes. We show that \name is able to encode nested datatypes.

% First we define a pair datatype as follows:

% \begin{figure}[H]
% \begin{spec}
%   data PairT (a : *) (b : *) = P a b;
% \end{spec}
% \end{figure}

% Using pairs, perfect binary trees are easily defined as below:

% \begin{figure}[h!]
% \begin{spec}
%   data B (a : *) = One a | Two (B (PairT a a));
% \end{spec}
% \end{figure}

% Notice that the recursive use of \emph{B} does not hold \emph{a}, but \emph{PairT a a}. This means every time we use a \emph{Two} constructor, the size of the pairs doubles. In case you are curious about the encoding of \emph{B}, here is the one:

% \begin{figure}[h!]
% \begin{spec}
%   let B : * -> * = mu X : * -> * .
%       \ a : * . (B : *) -> (a -> B) -> (X (PairT a a) -> B) -> B
%   in
% \end{spec}
% \end{figure}

% Because of the polymorphic recursive type ($\mu X : \star \rightarrow \star $) being used, it is fairly straightforward to encode nested datatypes.

% To easily construct a perfect binary tree from a list, we define a help function that transform a list to a perfect binary tree as shown in Figure~\ref{fig:perfectB}.

% \begin{figure}[ht]
% \begin{spec}
%   let pairs : (a : *) -> List a -> List (PairT a a) =
%     mu pairs' : (a : *) -> List a -> List (PairT a a) .
%       \ a : * . \ xs : List a .
%         case xs of
%           Nil => Nil (PairT a a)
%         | Cons (y : a) (ys : List a) =>
%             case ys of Nil =>
%               Nil (PairT a a)
%             | Cons (y' : a) (ys' : List a) =>
%                 Cons (PairT a a) (P a a y y') (pairs' a ys')
%   in
%   let fromList : (a : *) -> List a -> B a =
%     mu from' : (a : *) -> List a -> B a .
%       \ a : * . \xs : List a .
%         case xs of
%           Nil => Two a (from' (PairT a a) (pairs a (Nil a)))
%         | Cons (x : a) (xs' : List a) =>
%           case xs' of
%             Nil => One a x
%           | Cons (y : a) (zs : List a) =>
%               Two a (from' (PairT a a) (pairs a xs))
%   in
% \end{spec}
%   \caption{Construct a perfect binary tree from a list}
%   \label{fig:perfectB}
% \end{figure}

% Now we can define an interesting function \emph{powerTwo}. Given a natural number $n$, it computes the largest natural number $m$, such that $2^{m} < n$:

% \begin{figure}[H]
% \begin{spec}
%   let twos : (a : *) -> B a -> nat =
%     mu twos' : (a : *) -> B a -> nat .
%       \ a : * . \x : B a .
%         case x of
%           One (y : a) => 0
%         | Two (c : B (PairT a a)) =>
%             1 + twos' (PairT a a) c
%   in
%   let powerTwo : Nat -> nat =
%     \ n : Nat . twos nat (fromList nat (take n (repeat 1)))
%   in powerTwo (S (S (S (S Z)))) -- return 2
% \end{spec}
% \end{figure}
