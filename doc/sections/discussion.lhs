%include lhs2TeX.fmt

%format . = ".\,"
%format mu = "\mathsf{mu}"
%format * = "\star"
%format letrec = "\mathbf{letrec}"
%format rcrd = "\mathbf{rcrd}"

\section{Discussion}
\paragraph{More Type-level Computation}


\paragraph{Erasure of \cast Operators}

Explicit type \cast operators $[[castup]]$ and $[[castdown]]$ are part of the core design of the language. They are generalized from $\kw{fold}$ and $\kw{unfold}$ of iso-recursive types. By convention, $[[castup]]$ follows $\kw{fold}$ as a value in the language, which means it cannot be further reduced during the evaluation. Thus, it is likely to have many $[[castup]]$ constructs leaving in terms after evaluation. This will be a performance issue when considering code generation -- too many $[[castup]]$ constructs will dramatically increase the size of the program, which causes runtime overhead and affects the performance of the language.

In fact, we can safely erase \cast operators during code generation, because they do not perform any real transformation of a term other than changing its type.

\paragraph{Encoding of GADTs}

Our translation rules also open opportunity for encoding GADTs. In our
experiment, we have several running examples of encoding GADTs. Below
we show a GATD-encoded representation of well-scoped lambda terms
using de Bruijn notation.

In this notation, a variable is represented as a number -- its de
Bruijn index, where the number $k$ stands for the variable bound by
the $k$'s enclosing $\lambda$. Using the GADT syntax, below is the
definition of lambda terms:

\begin{figure}[H]
  \begin{spec}
    data Fin : Nat -> * =
         fzero : (n : Nat) -> Fin (S n)
      |  fsucc : (n : Nat) -> Fin n -> Fin (S n);
    data Term : Nat -> * =
         Var : (n : Nat) -> Fin n -> Term n
      |  Lam : (n : Nat) -> Term (S n) -> Term n
      |  App : (n : Nat) -> Term n -> Term n -> Term n;
  \end{spec}
\end{figure}

The datatype \emph{Fin n} is used to restrict the the de Brujin index,
so that it lies between $0$ to $n - 1$. The type of a closed term is
simply |Term Z|, for instance, a lambda term $\lambda x.\,\lambda y.\,
x$ is represented as (we use decimal numbers instead of peano natural
numbers):

\begin{figure}[H]
  \begin{spec}
    Lam 0 (Lam 1 (Var 2 (fsucc 1 (fzero 0))))
  \end{spec}
\end{figure}

If we accidentally write the wrong index, the program would fail to
pass type checking.

We do not have space to present a complete
encoding, but instead show the encoding of \emph{Fin}:

\begin{figure}[H]
  \begin{spec}
    let Fin : Nat -> * =
      mu X : Nat -> * . \ a : Nat .
        (B : Nat -> *) ->
        ((n : Nat) -> B (S n)) ->
        ((n : Nat) -> X n -> B (S n)) ->
        B a
  \end{spec}
\end{figure}

The key issue in encoding GATDs lies in type of variable $B$. In
ordinary datatype encoding, $B$ is fixed to have type $\star$, while
in GADTs, its type is the same as the variable $X$ (possibly
higher-kinded). Currently, we have to manually interpret the type
according to the particular use of some GADTs. We are investigating if
there exits a general way to do that.

\paragraph{Using Recursive Functions at the Type Level}
