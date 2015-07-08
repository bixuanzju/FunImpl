%include polycode.fmt
%include forall.fmt
%include format.fmt

\section{Overview}

This section informally introduces the main features of \name. In
particular, this section shows how the explicit casts in \name can be
used instead of the typical conversion rule present in calculi such as
the calculus of constructions. The formal details of \name are
presented in Section~\ref{sec:ecore}.

\subsection{The Calculus of Constructions and the Conversion Rule}
\label{sec:coc}

The calculus of constructions (\coc)~\cite{coc} is a
higher-order typed lambda calculus supporting dependent types (among
various other features).  A crucial
feature of \coc is the \emph{conversion rule}
: \ottusedrule{\ottdruleTccXXConv{}}

%For the most part \name is similar to the \emph{Calculus of Constructions}
%(\coc)~\cite{coc}, which is a higher-order typed lambda calculus.
%However unlike \name and \coc is the
%absence of a conversion rule 

The conversion rule allows one to derive $e:[[t2]]$ from the
derivation of $e:[[t1]]$ and the $\beta$-equality of $[[t1]]$ and
$[[t2]]$. This rule is important to \emph{automatically} allow terms
with $\beta$-equivalent types to be considered type-compatible.  The following
example illustrates the use of the conversion rule:
\[
f [[==]] [[\y:(\x:star.x)int.y]]
\]
Here $f$ is an identity function. Notice that the type of $y$
is $[[(\x:star.x)int]]$, which is
an identity function on types $[[\x:star.x]]$ applied to $[[int]]$, 
but not $[[int]]$. Hence $f$ cannot directly take an integer parameter.
Note that the following $\beta$-equivalence holds:
\[ [[(\x:star.x)int =b int]] \]
The conversion rule implicitly allows to convert the type of $y$
in $f$ through $\beta$-equality. Thus, $f$ can be converted to \[ [[\y:int.y]]\]
so that can be applied to an integer.

\paragraph{Decidability of Type-Checking and Strong Normalization}
While the conversion rule in \coc brings a lot of convenience, an
unfortunate consequence is that it couples decidability of
type-checking with strong normalization of the
calculus~\cite{pts:normalize}.  But strong normalization does
not hold with general recursion. And due to the conversion
rule, any non-terminating term would force the type checker to go into
an infinitely loop (by constantly applying the conversion rule without
termination), thus rendering the type system undecidable.

To illuminate the problem of the conversion rule with general
recursion, suppose $d$ is a
``dependent type'' that has type $[[int -> star]]$. With general
recursion, we can assume a term $z$ that has type
$d\,\mathsf{loop}$, where $\mathsf{loop}$ stands for any diverging
computation of type $[[int]]$. If we type
check the following application: \[ [[(\x: d three.x)z]]\]
under the normal typing rules of \coc, the type checker would get
stuck as it tries to do $\beta$-equality on two terms: $d\,3$ and
$d\,\mathsf{loop}$, where the latter is non-terminating.

\subsection{An Alternative to the Conversion Rule: Explicit Casts}
\label{subsec:cast}

In contrast to the implicit
reduction rules of \coc, \name makes it explicit as to when and where
to convert one type to another. Type conversions are explicit by
introducing two language constructs: $[[castdown]]$ (beta reduction)
and $[[castup]]$ (beta expansion). The benefit of this approach is
that decidability of type-checking no longer is coupled with strong
normalization of the calculus.

\paragraph{Beta Reduction} The operator $[[castdown]]$ 
allows a type conversion provided that the resulting
type is a \emph{beta reduction} of the original type of the term. To explain the
use of $[[castdown]]$, assume an identity function $g$ defined by
\[ g \equiv [[\y:int.y]] \]
and a term $[[e1]]$ with the type
\[ [[e1]] : [[(\x:star.x)int]] \]
In contrast to \coc,
we cannot directly apply $g$ to $[[e1]]$ in \name 
since their types are not \emph{syntactically equal}.
Note that the following beta reduction holds:
\[ [[(\x:star.x)int --> int]] \]
Thus, $[[castdown]]$ can be used for the explicit type-level beta reduction:
\[ [[castdown e1]] : [[int]]\]
Then the application $g\,([[castdown e1]])$ can type check.

\paragraph{Beta Expansion} The dual operation of $[[castdown]]$ is
$[[castup]]$, which allows a type conversion provided that the
resulting type is a \emph{beta expansion} of the original type of the
term. To explain the use of $[[castup]]$, let us revisit the example from Section~\ref{sec:coc}.
In \name, we cannot apply $f$ to an integer, say $[[e2]] : [[int]]$. 
Instead we need to use $[[castup]]$  to expand the type of $[[e2]]$:
\[ ([[castup[(\x:star.x)int] e2]]): [[(\x:star.x)int]] \]
Thus, the application $f~([[castup[(\x:star.x)int] e2]])$ can type check.
Intuitively,
$[[castup]]$ is doing a type conversion, as the type of $[[e2]]$ is
$ [[int]] $, and $ [[(\x:star.x)int]] $ is the beta expansion of
$[[int]]$ witnessed by
\[ [[(\x:star.x)int --> int]]\] Notice that for
$[[castup]]$ to work, we need to provide the resulting type as
argument. This is because for the same term, there might be more than one
choices for beta expansions, e.g., $1 + 2$ and $2 + 1$ are both the
beta expansions of $3$. 

\paragraph{One-Step}
A final point to make is that the \cast rules specify \emph{one-step}
reduction or expansion. To
clarify the subtlety, let us consider a variation of the example from
Section~\ref{subsec:cast}. Imagine term $[[e1]]$ has the type
\[ [[(\x : star . \y:star. x) int bool]] \]
which is a type-level |const| function. Now the following
application
\[g\,([[castdown e1]])\]
still results in an ill-typed expression, because $[[castdown e1]]$ has
type $[[(\y : star. int) bool]]$, which is not syntactically equal to
$[[int]]$. Apparently, another $[[castdown]]$ is needed:
\[g\,[[(castdown (castdown e1))]]\]
to further reduce $[[(\y : star. int) bool]]$ to $[[int]]$.

% These fine-tuned \cast rules gain us more control over type-level
% computation. The full technical details about \cast rules are
% presented in Section~\ref{sec:ecore}.

\paragraph{Decidability without Strong Normalization}

With explicit type conversion rules the decidability of type-checking 
no longer depends on the normalization property. 
Thus the type system remains decidable
even in the presence of non-termination at type level.
%As we will see in later sections. The
%ability to write non-terminating terms motivates us to have more
%control over type-level computation. 
% To illustrate, let us consider the following example. Suppose that $d$ is a ``dependent type'' where
% \[d : [[int -> star]]\] so that $d\,3$ or $d\,100$ all yield the same
% type. With general recursion at hand, we can image a term $z$ that has
% type \[d\,\mathsf{loop}\] where $\mathsf{loop}$ stands for any
% diverging computation and of type $[[int]]$. What would happen if we
% try to type check the following application: \[ [[(\x: d three.x)z]]\]
% Under the normal typing rules of \coc, the type checker would get
% stuck as it tries to do $\beta$-equality on two terms: $d\,3$ and
% $d\,\mathsf{loop}$, where the latter is non-terminating.

Consider the same example discussed in
Section~\ref{sec:coc}. The type checker will not get stuck when
type-checking the following application:
\[ [[(\x: d three.x)z]] \]
where the type of $z$ is $d\,\mathsf{loop}$.  This is because in
\name, the type checker only does syntactic comparison between $d\,3$
and $d\,\mathsf{loop}$, instead of $\beta$-equality. It
rejects the above application as ill-typed. Indeed it is impossible to
type-check the application even with the use of $[[castup]]$ and/or
$[[castdown]]$: one would need to write infinite number of
$[[castdown]]$'s to make the type checker loop forever (e.g.,
$([[\x:d three.x]])([[castdown]]([[castdown]] \dots z))$). But it is
impossible to write such program in practice.

% In summary, \name achieves the decidability of type checking by
% explicitly controlling type-level computation, which is independent of
% the normalization property, while supporting general recursion at the
% same time.

\subsection{Recursive Terms and Types}

\name supports general recursion, and allows writing standard
recursive programs at the term level. At the same time, the recursive
construct can also be used to model recursive types at the type-level.
Therefore, \name \emph{unifies} both recursion and recursive types 
by the same $\mu$ primitive.

\paragraph{Recursive Terms}

The $\mu$ primitive $[[mu x:t.e]]$ can be used to define recursive functions.  For
example, the factorial function is written in \name as:

< fact =  mu f : Int -> Int. \ x : Int .
<         if x == 0 then 1 else x time (f (x - 1))

% \bruno{show how to use fact} \jeremy{Linus already has an exmaple of
%   using fact step by step in Section~\ref{subsec:recur}, still need
%   here?} 
Here we treat the $\mu$ operator as a \emph{fixpoint} which can be 
evaluated to its recursive unfolding:
\[ [[mu x:t.e]] [[-->]] e [x \mapsto [[mu x:t.e]] ] \]
Then applying the term above to some integer $n$ like $\mathit{fact}~n$ will work
as a factorial function through the evaluation (see Section \ref{sec:rec:recur}).
Also note that the type $[[t]]$ is not restricted to function types. We can define a
record of mutually recursive functions as the fixed point of a
function on records.

% The dynamic semantics of $\mu$ requires the recursive binder to satisfy (omit type annotations for clarity):  \[ \mu f.\,E = (\lambda f.\,E) (\mu f.\,E) \] which, however, does not terminate in strict languages. Therefore, to loosen the function-type restriction to allow any types, the sensible choice for the evaluation strategy is \emph{call-by-name}.

\paragraph{Recursive Types}
The same $\mu$ primitive is used on type-level to represent recursive types. 
We use the \emph{iso-recursive} approach \cite{eqi:iso} that treats
an iso-recursive type and its one-step as different, but isomorphic types. 
The isomorphism is witnessed by \fold and \unfold operations.
In \name, such isomorphism is witnessed by $[[castup]]$ and
$[[castdown]]$ (see Section \ref{sec:rec:recur}). 
In fact, $[[castup]]$ and $[[castdown]]$ \emph{generalize}
\fold and \unfold, which can convert any types, not just recursive
types.

To demonstrate the use of the
\cast rules with recursive types, we show the formation of the ``hungry'' type~\cite{tapl}:
\[H = \miu{\sigma}{\star}{\mathsf{Int} \rightarrow \sigma}\]
A term $z$
of type $H$ accepts any number of integers and returns a new
function that is hungry for more, as illustrated below:
\begin{align*}
[[castdown z]] &: [[int]][[->]]H  \\
[[castdown(castdown z)]] &: [[int]][[->]][[int]][[->]]H \\
[[castdown]]([[castdown]] \dots z) &: [[int]][[->]][[int]][[->]]\dots[[->]]H
\end{align*}

% Due to the unification of recursive types and recursion, we can use
% the same $\mu$ primitive to write both recursive types and recursion
% with ease.

% \paragraph{Call-by-Name}
% Due to the unification, the \emph{call-by-value} evaluation strategy
% does not fit in our setting. In call-by-value evaluation, recursion
% can be expressed by the recursive binder $\mu$ as $\mu f : T
% \rightarrow T.\, E$ (note that the type of $f$ is restricted to
% function types). Since we don't want to pose restrictions on the
% types, the \emph{call-by-name} evaluation is a sensible choice.
% \bruno{Probably needs to be improved. I'll came back to this later!}

% \subsection{Logical Inconsistency}
% Although the decidability of type-checking is preserved, a consequence
% having general recursion in \name is that the logical consistency is
% lost. In \name every type is inhabited, which is problematic if we
% want to view \name as a logic. Indeed, unlike many other dependently 
% calculi which have been proposed in the past, \name cannot be used 
% directly to do theorem proving.

% Nevertheless the loss of logical consistency is a deliberate design
% decision. Although there are dependently typed languages that support
% general recursion and still preserve logical consistency, this is done
% at the cost of additional complexity in the
% system~\cite{zombie:popl14, Swamy2011, fstar}. In \name we trade the
% loss of logical consistency by a significantly simpler system.

% Since our goal is 
% use \name as a foundational calculus for languages like Haskell,
% logical consistency is not an important property: traditional 
% functional languages like Haskell are logically inconsistent as well. 
% For example, in Haskell, we can write a ``false'' type:

% < type False = forall a. a

% With general recursion, a value with type |False| is given:

% < false  ::  False
% < false  =   false

% whose denotational semantics is |undefined|, which corresponds to
% inconsistency in logic. 

% \paragraph{Type in Type}
% \linus{Duplicated.}
% Since logical consistency is already lost due to general recursion,
% \name also uses the $\star : \star$ axiom~\cite{handbook}. As a
% consequence, having this rule adds expressiveness and simplifies our
% system (e.g., it will be easy to explicitly quantify over kinds). We
% return to this issue in Section~\ref{sec:related}.

\subsection{Encoding Datatypes}
The explicit type conversion rules and the $\mu$ primitive facilitate
the encoding of recursive datatypes and recursive functions over
datatypes. While inductive datatypes can be encoded using either the
Church~\cite{tapl} or the Scott encoding~\cite{encoding:scott}, we
adopt the Scott encoding as it encodes case analysis, making it more
convenient to encode pattern matching. We demonstrate the encoding
method using a simple datatype as a running example: Peano
numbers. The datatype declaration for Peano numbers in Haskell is:

<  data Nat = Z | S Nat

In the Scott encoding, the encoding of the |Nat| datatype reflects how
its two constructors are going to be used. Since |Nat| is a recursive
datatype, we have to use recursive types at some point to reflect its
recursive nature. As it turns out, the typed Scott encoding of |Nat|
is:

< mu X : * . (b : *) -> b -> (X -> b) -> b

The function type |(b -> (X -> b) -> b)| demystifies the recursive
nature of |Nat|: $b$ corresponds to the type of the constructor |Z|,
and |(X -> b)| corresponds to the type of the constructor |S|. The
intuition is that any recursive use of the datatype in the data
constructors is replaced with the variable ($X$ in the case) bound by
$\mu$, and we make the resulting type variable ($B$ in this case)
universally quantified so that elements of the datatype with different
result types can be used in the same program~\cite{gadts}.

The two constructors can be encoded correspondingly via the \cast rules:

< Z = castup[Nat] (\ b : * . \ z : b . \ f : Nat -> b . z)
< S = \ n : Nat .  castup[Nat]
<                  (\ b : * . \ z : b . \ f : Nat -> b . f n)

Intuitively, each constructor selects a different function from the
function parameters ($z$ and $f$ in the above example). This provides
branching in the process flow, based on the constructors. Note that we
use the $[[castup]]$ operation to do type conversion between the
recursive type and its unfolding.

Finally a recursive function that adds two natural numbers is defined
as follows:

< mu f : Nat -> Nat -> Nat . \ n : Nat . \ m : Nat .
<     (castdown n) Nat m (\ n' : Nat . S (f n' m))

The above definition resembles case analysis commonly seen in modern
functional programming languages. Indeed, if we take apart the definition, we will see
why the use of $[[castdown]]$ plays such an important role to make it
all work. First of all, remember |Nat| datatype is encoded as:

< mu X : * . (b : *) -> b -> (X -> b) -> b

then |(castdown n)| reduces the above to

< (b : *) -> b -> (Nat -> b) -> b

which perfectly matches the types of the terms applied to |(castdown
n)|: |Nat| is fed as the result type; $m$ is used for the base case;
and |(\ n' : Nat . S (f n' m))| the recursive step.

% The formal treatment of encoding case analysis is presented in
% Section~\ref{sec:surface}.



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../main"
%%% End:
