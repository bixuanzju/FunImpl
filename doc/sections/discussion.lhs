%include polycode.fmt
%include format.fmt

\section{Discussion}
\label{sec:discuss}

\paragraph{More Type-level Computation}


\paragraph{Eliminating Cast Operators}

Explicit type \cast operators $[[castup]]$ and $[[castdown]]$ are
generalized from $[[fold]]$ and $[[unfold]]$ of iso-recursive
types. By convention, $[[castup]]$ follows $[[fold]]$ as a value, so
it cannot be further reduced during the evaluation. This may cause
semantics and performance issues.

To show the semantics issue, suppose there is a non-terminating term
$\mathit{loop}$. It should loop forever when evaluated. But if it is
wrapped by $[[castup]]$ like $[[castup]]~[ [[t]] ]~\mathit{loop}$, the
evaluation stops immediately. So the dynamic semantics of a term-level
expression wrapped by $[[castup]]$ might differ from the original. The
performance issue may occur during code generation. Since $[[castup]]$
will remain after evaluation, too many $[[castup]]$ constructs can
increase the size of the program and cause runtime overhead.

In fact, \cast operators can be safely eliminated after type checking,
because they do not actually transform a term other than changing its
type. There are two choices of when to remove \cast operators, during
evaluation or code generation. The following alternative reduction
rules can eliminate \cast during evaluation:
\ottusedrule{\ottdruleSXXCastUpE{}}
\ottusedrule{\ottdruleSXXCastDownE{}} Moreover, $[[castup]]$ is no
more treated as a value. With such modification, we can obtain
$[[castup]]~[ [[t]] ]~\mathit{loop} [[-->]] \mathit{loop}$. So
$[[castup]]$ will not interfere with the original dynamic semantics of
terms. But noting that $[[castup [t] e]]$ or $[[castdown e]]$ has
different types from $[[e]]$, types of terms are not preserved during
evaluation. This breaks the subject reduction theorem, and
consequently type-safety.

Thus, we stick to the semantics of iso-recursive types for \cast
operators which has type preservation. And we prefer to eliminate
all \cast operators during type erasure to address the potential
performance issue of code generation.

\paragraph{Encoding of GADTs}

Our translation rules also open opportunity for encoding GADTs. In our
experiment, we have several running examples of encoding GADTs. Below
we show a GADT-encoded representation of well-scoped lambda terms
using de Bruijn notation.

In this notation, a variable is represented as a number -- its de
Bruijn index, where the number $k$ stands for the variable bound by
the $k$'s enclosing $\lambda$. Using the GADT syntax, below is the
definition of lambda terms:

< data Fin : Nat -> * =
<      fzero : (n : Nat) -> Fin (S n)
<   |  fsucc : (n : Nat) -> Fin n -> Fin (S n);
<
< data Term : Nat -> * =
<      Var : (n : Nat) -> Fin n -> Term n
<   |  Lam : (n : Nat) -> Term (S n) -> Term n
<   |  App : (n : Nat) -> Term n -> Term n -> Term n;

The datatype \emph{Fin n} is used to restrict the the de Brujin index,
so that it lies between $0$ to $n - 1$. The type of a closed term is
simply |Term Z|, for instance, a lambda term
$\lambda x.\,\lambda y.\, x$ is represented as (for the presentation,
we use decimal numbers instead of Peano numbers):

< Lam 0 (Lam 1 (Var 2 (fsucc 1 (fzero 0))))

If we accidentally write the wrong index, the program would fail to
pass type checking.


We do not have space to present a complete encoding, but instead show
the encoding of \emph{Fin}:

< let Fin : Nat -> * =
<   mu X : Nat -> * . \ a : Nat .
<     (B : Nat -> *) ->
<     ((n : Nat) -> B (S n)) ->
<     ((n : Nat) -> X n -> B (S n)) ->
<     B a

The key issue in encoding GADTs lies in type of variable $B$. In
ordinary datatype encoding, $B$ is fixed to have type $\star$, while
in GADTs, its type is the same as the variable $X$ (possibly
higher-kinded). Currently, we have to manually interpret the type
according to the particular use of some GADTs. We are investigating if
there exits a general way to do that.
