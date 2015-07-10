%include polycode.fmt
%include format.fmt

%format tri="\triangleright"
%format family="\mathbf{family}"


\section{Conclusions and Future Work}

This work proposes a minimal dependently typed language that allows the same
syntax for terms and types, supports type-level computation, and preserves
decidable type checking under the presence of general recursion. It does so by
1) introducing explicit type casts that decouple the decidability of type
checking from strong normalization; 2) providing a single recursion operator
for recursion on terms as well as recursive types; 3) formalizing the core
language, and proving its type-safety and decidability. By demonstrating a
surface language on top of the core which supports advanced  constructions, we
consider our work as a well-suited core  for Haskell-like languages.

\begin{comment}
In \name type-level computation amounts to usual term-level
computation, but in a controlled way. This is in the same spirit as
Haskell, where System $F_C$ uses syntactic type-level equality and
explicit equality coercions to control type-level computation. For
example, a type-level identity function in System $F_C$ is defined
using closed type families:

< type family Id (a :: *):: * where
<    Id a = a

By using explicit coercions, function like |\ x : Id Int . x tri co|
can be typed as |Id Int -> Int|. In a similar way, \name uses
explicit casts to type function |\x : Id Int . castdown x|. This is
in contrast to Coq and Agda, which require no coecions or casts but
the conversion rule.
\end{comment}

In future work, we hope to make  writing type-level computation easier by
adding language constructs to the surface language. Currently intensive type-
level computation can be written in \name,  but is inconvenient to use.
Because in \name  type-level computation is driven by casts, and the number of
casts needs to be specified by user beforehand. Nevertheless, we do not
consider this critical weakness of our system,  since our design goal is
similar with System $F_C$ which sacrifices the convenience of type-level
computation and recovers it by language constructs,  such as closed type
families in Haskell. Thus, we plan to add new surface language constructs in
the same spirit as type families in Haskell and automatically generate casts
through the translation.
% Currently, for simple non-recursive functions, it is easy to deduce
% how many casts needs to be introduced, but for recursive ones, it
% becomes inconvenient.

Another important form of type-level computation supported by Haskell is
GADTs. As we mentioned in the related work, currently the surface language
lacks support for GADTs.  Although the core language has  necessary language
features for the encoding~\cite{gadtsml}. And we have succeeded in encoding
some examples of GADTs in \name, such as finite sets (see $\mathit{Fin}$ in
the appendix). The current translation  rules for datatypes can be extended to
account for GADTs by generalizing the return type to be polymorphic  instead
of $\star$.

But we are still cautious about including GADTs  in the surface
language at the moment. The issues are manifested in two strands: 1)
Injectivity of type constructors; 2) Equality proofs. Currently \name only
supports syntactic equality which may cause issues for pattern matching some special
GADTs.  \linus{How special: non-injective, dependent? Examples?} We hope to
resolve the issues by generalizing explicit casts with non-syntactic equality. 
Though adding non-syntactic type equality to our system would require some extra effort, it
remains as compelling future work.
