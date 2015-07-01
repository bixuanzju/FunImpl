%include polycode.fmt
%include format.fmt

\section{Overview}

This section informally introduces the main features of \name. In
particular, this section shows how the explicit casts in \name can be
used instead of the typical conversion rule present in calculi such as
the calculus of constructions. The formal details of \name are
presented in \S\ref{sec:ecore}. \jeremy{to distinguish code from
  \sufcc and \name, we may want to use different fonts, e.g., {\tt
    typewriter font} for \sufcc}

\subsection{The Calculus of Constructions and the Conversion Rule}
\label{sec:coc}

The calculus of constructions (\coc)~\cite{coc} is a powerful
higher-order typed lambda calculus supporting dependent types (among
various other features).  A crutial
feature of \coc is the so-called \emph{conversion}
rule: \ottusedrule{\ottdruleTccXXConv{}}

%For the most part \name is similar to the \emph{Calculus of Constructions}
%(\coc)~\cite{coc}, which is a higher-order typed lambda calculus.
%However unlike \name and \coc is the
%absence of a conversion rule 

The conversion rule allows one to derive $e:[[t2]]$ from the
derivation of $e:[[t1]]$ and the $\beta$-equality of $[[t1]]$ and
$[[t2]]$. This rule is important to \emph{automatically} allows terms
with equivalent types to be considered type-compatible.  The following
example illustrates the use of the conversion rule:
\[
f \equiv [[\x:(\y:star.y)int.x]]
\]
Here $f$ is a simple identity function. Notice that the type of $x$
(i.e., $[[(\y:star.y)int]]$), which is the argument of $f$, is
interesting: it is an identity function on types, applied to an
integer.  Without the conversion rule, $f$ cannot be applied to, say
$3$ in \coc. However, given that $f$ is actually $\beta$-convertible
to $[[\x:int.x]]$, the conversion rule allows the application of $f$
to $3$ by implicitly converting $[[\x:(\y:star.y)int.x]]$ to
$[[\x:int.x]]$.

\paragraph{Decidability of Type-Checking and Strong Normalization} 
While the conversion rule in \coc brings a lot of convenience, an
unfortunate consequence is that it couples decidability of
type-checking with strong normalization of the
calculus~\cite{coc:decidability}.  However strong normalization does
not hold with general recursion. This is because due to the conversion
rule, any non-terminating term would force the type checker to go into
an infinitely loop (by constantly applying the conversion rule without
termination), thus rendering the type system undecidable.

To illustrate the problem of the conversion rule with general
recursion, let us consider a somewhat contrived example. Suppose that
$d$ is a ``dependent type'' that has type $[[int -> star]]$. With
general recursion at hand, we can image a term $z$ that has type
$d\,\mathsf{loop}$, where $\mathsf{loop}$ stands for any diverging
computation of type $[[int]]$. What would happen if we try to type
check the following application: \[ [[(\x: d three.x)z]]\]
Under the normal typing rules of \coc, the type checker would get
stuck as it tries to do $\beta$-equality on two terms: $d\,3$ and
$d\,\mathsf{loop}$, where the latter is non-terminating.  \bruno{show
  simple example. Explain issue better.} \jeremy{done!}

\subsection{An Alternative to the Conversion Rule: Explicit Casts}

\bruno{Mention somewhere that the \cast rules do \emph{one-step}
  reductions.} \jeremy{done! see last paragraph, also put beta
  reduction before beta expansion} In contrast to the implicit
reduction rules of \coc, \name makes it explicit as to when and where
to convert one type to another. Type conversions are explicit by
introducing two language constructs: $[[castdown]]$ (beta reduction)
and $[[castup]]$ (beta expansion). The benefit of this approach is
that decidability of type-checking no longer is coupled with strong
normalization of the calculus.

\paragraph{Beta Reduction} The first of the two type conversions
$[[castdown]]$, allows a type conversion provided that the resulting
type is a \emph{beta reduction} of the original type of the term. The
use of $[[castdown]]$ is better explained by the following simple
example. Suppose that
\[ g \equiv [[\x:int.x]] \]
and term $z$ has type
\[ [[(\y:star.y)int]] \]
$ g\,z $ is an ill-typed application, whereas $ g\,([[castdown z]]) $
is well-typed. This is witnessed by
$[[(\y:star.y)int]] \rightarrow_{\beta} [[int]]$, which is a beta
reduction of $[[(\y:star.y)int]]$. \bruno{explain why this is a
  reduction} \jeremy{done!}

\paragraph{Beta Expansion} The dual operation of $[[castdown]]$ is
$[[castup]]$, which allows a type conversion provided that the
resulting type is a \emph{beta expansion} of the original type of the
term.  Let us revisit the example from \S\ref{sec:coc}. In \name,
$f\,3$ is an ill-typed application. Instead we must write the
application as
\[ f\,([[castup[(\y:star.y)int] three]]) \]
\bruno{how to put a space before $3$?} \jeremy{fixed!} Intuitively,
$[[castup]]$ is doing a type conversion, as the type of $ 3 $ is
$ [[int]] $, and $ [[(\y:star.y)int]] $ is the beta expansion of
$[[int]]$ (witnessed by
$[[(\y:star.y)int]] \rightarrow_{\beta} [[int]]$). \bruno{explain why
  this is a beta expansion} \jeremy{done!} Notice that for
$[[castup]]$ to work, we need to provide the resulting type as
argument. This is because for the same term, there are more than one
choices for beta expansions (e.g., $1 + 2$ and $2 + 1$ are both the
beta expansions of $3$). \bruno{explain why for beta expansions we
  need to provide the resulting type as argument} \jeremy{done!}

A final point to make is that the \cast rules specify \emph{one-step}
reduction. This enables us to have more control over type-level
computation. The full technical details about \cast rules are presented
in \S\ref{sec:ecore}.

\subsection{Decidability without Strong Normalization}

With explicit type conversion rules the decidability of type-checking 
no longer depends on the normalization property. 
A nice consequence of this is that the type system remains decidable
even in the presence of non-terminating programs at type level.
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

To illustrate, let us consider the same example discussed in
\S\ref{sec:coc}. Now the type checker will not get stuck when
type-checking the following application:
\[ [[(\x: d three.x)z]] \]
where the type of $z$ is $d\,\mathsf{loop}$.  This is because in
\name, the type checker only does syntactic comparison between $d\,3$
and $d\,\mathsf{loop}$, instead of $\beta$-equality. Therefore it
rejects the above application as ill-typed. Indeed it is impossible to
type-check the application even with the use of $[[castup]]$ and/or
$[[castdown]]$: one would need to write infinite number of
$[[castdown]]$'s to make the type checker loop forever (e.g.,
$([[\x:d three.x]])([[castdown]]([[castdown]] \dots z))$). But it is
impossible to write such program in reality.

In summary, \name achieves the decidability of type checking by
explicitly controlling type-level computation.  which is independent
of the normalization property, while supporting general recursion at
the same time.

\subsection{Recursion and Recursive Types}

\bruno{Show how in \name recursion and recursive types are unified.
Discuss that due to this unification the sensible choice for the
evaluation strategy is call-by-name. }

A simple extension to \name is to add a simple recursion construct.
With such an extension, it becomes possible to write standard
recursive programs at the term level. At the same time, the recursive
construct can also be used to model recursive types at the type-level.
Therefore, \name differs from other programming languages in that it
unifies both recursion and recursive types by the same $\mu$
primitive. With a single language construct we get two powerful
features!

\paragraph{Recursion}

The $\mu$ primitive can be used to define recursive functions.  For
example, the factorial function:

< mu f : Int -> Int . if x == 0 then 1 else x time f (x - 1)

The above recursive definition works because of the dynamic semantics of the
$\mu$ primitive: \ottusedrule{\ottdruleSXXMu{}} which is exactly doing
recursive unfolding of itself.

It is worth noting that the type $[[t]]$ in \ruleref{S\_Mu} is not
restricted to function types. This extra freedom allows us to define a
record of mutually recursive functions as the fixed point of a
function on records.

% The dynamic semantics of $\mu$ requires the recursive binder to satisfy (omit type annotations for clarity):  \[ \mu f.\,E = (\lambda f.\,E) (\mu f.\,E) \] which, however, does not terminate in strict languages. Therefore, to loosen the function-type restriction to allow any types, the sensible choice for the evaluation strategy is \emph{call-by-name}.

\subsubsection{Recursive types}
In the literature on type systems, there are two approaches to
recursive types, namely \emph{equi-recursive} and
\emph{iso-recursive}. The \emph{iso-recursive} approach treats a
recursive type and its unfolding as different, but isomorphic. The
isomorphism between a recursive type and its one step unfolding is
witnessed by traditionally \fold and \unfold operations. In \name, the
isomorphism is witnessed by first $[[castup]]$, then
$[[castdown]]$. \bruno{Explain that the casts generalize fold and
  unfold!}  \jeremy{done!} At first sight, the \cast rules share some
similarities with \fold and \unfold, but $[[castup]]$ and
$[[castdown]]$ actually generalize \fold and \unfold: they can convert
any types, not just recursive types. To demonstrate the use of the
\cast rules, let us consider a classic example of a recursive type,
the so-called ``hungry'' type~\cite{tapl}:
$H = \miu{\sigma}{\star}{\mathsf{Int} \rightarrow \sigma}$. A term $z$
of type $H$ can accept any number of integers and return a new
function that is hungry for more, as illustrated below:
\begin{align*}
[[castdown z]] &: [[int]][[->]]H  \\
[[castdown(castdown z)]] &: [[int]][[->]][[int]][[->]]H \\
[[castdown]]([[castdown]] \dots z) &: [[int]][[->]][[int]][[->]]\dots[[->]]H
\end{align*}

% Due to the unification of recursive types and recursion, we can use
% the same $\mu$ primitive to write both recursive types and recursion
% with ease.

\paragraph{Call-by-Name}
Due to the unification, the \emph{call-by-value} evaluation strategy
does not fit in our setting. In call-by-value evaluation, recursion
can be expressed by the recursive binder $\mu$ as $\mu f : T
\rightarrow T.\, E$ (note that the type of $f$ is restricted to
function types). Since we don't want to pose restrictions on the
types, the \emph{call-by-name} evaluation is a sensible choice.
\bruno{Probably needs to be improved. I'll came back to this later!}

\subsection{Logical Inconsistency}

\bruno{Explain that the \name is inconsistent and discuss that this is
  a deliberate design decision, since we want to model languages like
  Haskell, which are logically inconsistent as well.} \bruno{Discuss
  the $* : *$ rule: since we already have inconsistency, having this
  rule adds expressiveness and simplifies the system.} \jeremy{added!}

One consequence of adding general recursion to the type system is that
the logical consistency of the system is broken. This is a deliberate
design decision, since our goal is to model languages like Haskell,
which are logically inconsistent as well.

In light of the fact that we decide to give up consistency, we take
another step further by declaring that the kind $\star$ is of type
$\star$. As it turns out, having this rule adds expressiveness and
simplifies our system. We return to this issue in \S\ref{sec:related}.


\subsection{Encoding Datatypes}

The explicit type conversion rules and the $\mu$ primitive facilitates
the encoding of recursive datatypes and recursive functions over
datatypes. While inductive datatypes can be encoded using either the
Church or the Scott encoding, we adopt the Scott encoding as it
encodes case analysis, making it more convenient to encode pattern
matching. We demonstrate the encoding method using a simple datatype
as a running example: Peano numbers.

The datatype declaration for Peano numbers in Haskell is:

<  data Nat = Z | S Nat

In the Scott encoding, the encoding of the \emph{Nat} datatype
reflects how its two constructors are going to be used. Since
\emph{Nat} is a recursive datatype, we have to use recursive types at
some point to reflect its recursive nature. As it turns out, the typed
Scott encoding of \emph{Nat} is:

< mu X : * . pi B : * . B -> (X -> B) -> B

The function type |B -> (X -> B) -> B| demystifies the recursive
nature of \emph{Nat}: $B$ corresponds to the type of the constructor
\emph{Z}, and |X -> B| corresponds to the type of the constructor
\emph{S}. The intuition is that any recursive use of the datatype in
the data constructors is replaced with the variable ($X$ in the case)
bound by $\mu$, and we make the resulting variable ($B$ in this case)
universally quantified so that elements of the datatype with different
result types can be used in the same program~\cite{gadts}.

Its two constructors can be encoded correspondingly via the \cast rules:

< Z = castup[Nat] (\ B : * . \ z : B . \ f : Nat -> B . z)
< S = \ n : Nat . castup[Nat] (\ B : * . \ z : B . \ f : Nat -> B . f n)

Thanks to the \cast rules, we can make use of the $[[castup]]$
operation to do type conversion between the recursive type and its
unfolding.

The last example defines a recursive function that adds two natural
numbers:

< mu f : Nat -> Nat -> Nat . \ n : Nat . \ m : Nat .
<     (castdown n) Nat m (\ n' : Nat . S (f n' m))

The above definition quite resembles case analysis commonly seen in
modern functional programming languages. (We formalize the encoding of
case analysis in \S\ref{sec:surface}.)



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../main"
%%% End:
