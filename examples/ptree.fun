---- Begin Comment ----

A labelled binary tree that keeps track its depth statically

<expr>            pretty print
:t <expr>         show the type
:trans <expr>     show the translation
:e <expr>         evaluation
:q                quit gracefully

Copy and paste the following definition to REPL

---- End Comment ----

data Nat = Z | S (n:Nat); data PTree (n : Nat) = Empty | Fork (z : nat) (x : PTree (S n)) (y : PTree (S n)); Fork Z 1 (Empty (S Z)) (Empty (S Z))
