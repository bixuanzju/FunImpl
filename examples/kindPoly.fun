---- Begin Comment ----

Higher-kinded fixpoint combinator

<expr>            pretty print
:t <expr>         show the type
:trans <expr>     show the translation
:e <expr>         evaluation
:q                quit gracefully

Copy and paste the following definition to REPL

---- End Comment ----

data Mu (k : *) (f : (k -> *) -> k -> *) (a : k) = Roll (g : (f (Mu k f) a)); data Listf (f : * -> *) (a : *) = Nil | Cons (x : a) (xs : (f a)); let List : * -> * = \a : * . Mu * Listf a in let nil : List nat = Roll * Listf nat (Nil (Mu * Listf) nat) in nil
