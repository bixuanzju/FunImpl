---- Begin Comment ----

The `Fin` datatype represents the type of all numbers less than a
given number. This example demonstrates that we can encode and use
some GADTs. Below are some definitions in GADT-style. (Note that
GADT-style declaration is not supported yet.)

data Fin : Nat -> * where
  zero : (n : Nat) -> Fin (S n)
  suc  : (n : Nat) -> Fin n -> Fin (S n)

letrec toNat : (n : Nat) -> Fin n -> nat =
  case f of
    zero => 0
    suc (n : Nat) (m : Fin n) => 1 + toNat n m

<expr>            pretty print
:t <expr>         show the type
:trans <expr>     show the translation
:e <expr>         evaluation
:q                quit gracefully

Copy and paste the following definition to REPL

---- End Comment ----

data Nat = Z | S (n : Nat); let Fin : Nat -> * = mu X : Nat -> * . \ a : Nat . (B : Nat -> *) -> ((n : Nat) -> B (S n)) -> ((n : Nat) -> X n -> B (S n)) -> B a in let zero : (a : Nat) -> Fin (S a) = \ a : Nat . fold 2 [Fin (S a)] (\ B : Nat -> * . \c : (n : Nat) -> B (S n) . \ d : (n : Nat) -> Fin n -> B (S n) . c a) in let suc : (a : Nat) -> Fin a -> Fin (S a) = \ a : Nat . \ m : Fin a . fold 2 [Fin (S a)] (\ B : Nat -> * . \c : (n : Nat) -> B (S n) . \ d : (n : Nat) -> Fin n -> B (S n) . d a m) in letrec toNat : (n : Nat) -> Fin n -> nat = \n : Nat . \f : Fin n . unfold 1 (((unfold 2 (f)) (\x : Nat . nat) (\ a : Nat . fold 1 [(\ x : Nat . nat) (S a)] 0) (\ a : Nat . \ g : Fin a . fold 1 [(\ x : Nat . nat) (S a)] (1 + toNat a g)))) in toNat (S (S Z)) (suc (S Z) (zero Z))
