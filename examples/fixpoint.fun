---- Begin Comment ----

Fixpoints of functors, also defines a gerneci fold function `cata`

<expr>            pretty print
:t <expr>         show the type
:trans <expr>     show the translation
:e <expr>         evaluation
:q                quit gracefully

Copy and paste the following definition to REPL

---- End Comment ----

rcrd Functor (f : * -> *) = Func {fmap : (a : *) -> (b : *) -> (a -> b) -> f a -> f b}; rcrd Fix (f : * -> *) = In {out : (f (Fix f)) }; letrec cata : (f : * -> *) -> (a : *) -> Functor f -> (f a -> a) -> Fix f -> a = \f : * -> * . \ a : * . \ m : Functor f . \ g : f a -> a. \ t : Fix f . g (fmap f m (Fix f) a (cata f a m g) (out f t)) in cata
