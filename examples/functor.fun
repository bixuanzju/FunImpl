---- Begin Comment ----

The functor record, also define `Manybe` datatype and its functor instance

<expr>            pretty print
:t <expr>         show the type
:trans <expr>     show the translation
:e <expr>         evaluation
:q                quit gracefully

Copy and paste the following definition to REPL

---- End Comment ----

data Maybe (a : *) = Nothing | Just (x:a); rcrd Functor (f : * -> *) = Func {fmap : (a : *) -> (b : *) -> (a -> b) -> f a -> f b}; let maybeInst : Functor Maybe = Func Maybe (\ a : * . \ b : * . \f : a -> b . \ x : Maybe a . case x of Nothing => Nothing b |  Just (z : a) => Just b (f z)) in maybeInst
