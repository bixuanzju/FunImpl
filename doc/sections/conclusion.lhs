%include polycode.fmt
%include format.fmt

%format tri="\triangleright"
%format family="\mathbf{family}"


\section{Conclusions and Future Work}

This work proposes a small dependently typed language that allows the
same syntax for terms and types, supports type-level computation, and
preserves decidable type checking under the presence of general
recursion. It does so by 1) introducing explicit type casts, which
allow decouping decidability of type checking from strong
nomalization; 2) providing a single recursion operator that combines
recursion on terms with recursive types; 3) formalizing the core
language \name, and proving its type-safety and decidability. We
consider our work as a well-suited core for Haskell-like languages.

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

Of course much remains to be done. For one thing, intensive type-level
computation can be written in \name, but is inconvenient to use. This
is because in \name type-level computation is driven by casts, and the
number of casts needs to be specified beforehand.
% Currently, for simple non-recursive functions, it is easy to deduce
% how many casts needs to be introduced, but for recursive ones, it
% becomes inconvenient.
However, we are optimistic in this regard. We plan to add language
constructs to the surface language, in the same spirit as type
families in Haskell, to automatically generate casts. For another, as
we mentioned in the related work, \name lacks support for GADTs. In
our experience, the translation rules for datatypes can be extended to
account for GADTs. (We have succeeded in encoding some examples of
GADTs, including \emph{Fin}.) The issues are manifested in two
strands: 1) Injectivity of type constructors; 2) Equality
proofs. Currently \name only supports syntactic equality. Though
adding non-syntactic type equality to our system would require some
thoughts, it remains as compelling future work.
