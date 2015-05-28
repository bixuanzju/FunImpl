module Predef where

import Expr
import Parser
import Syntax
import TypeCheck

initenv :: BEnv
initenv = [ ("nat", nat)
          , ("fix", fix)
          , ("zero", zero)
          , ("suc", suc)
          , ("one", one)
          , ("two", two)
          , ("plus", plus)
          , ("three", three)
          , ("bool", bool)
          , ("true", true)
          , ("false", false)
          ]

initalBEnv :: BEnv
initalBEnv = foldl (\env (n, e) -> (n, repFreeVar env e) : env) [] initenv

initalEnv :: Env
initalEnv = [("vec", vec), ("cons", cons), ("nil", nil)]

parse :: String -> Expr
parse str =
  let Right (Progm [expr]) = parseExpr str
  in expr

cons :: Expr
cons = repFreeVar initalBEnv (parse "pi a : * . pi b : a . pi n : nat . vec a n -> vec a (suc n)")

nil :: Expr
nil = repFreeVar initalBEnv (parse "pi a : * . vec a zero")

vec :: Expr
vec = repFreeVar initalBEnv (parse "* -> nat -> *")

bool :: Expr
bool = parse "mu x . pi a : * . a -> a -> a"

true :: Expr
true = parse "fold[bool] (lam a : * . lam t : a . lam f : a . t)"

false :: Expr
false = parse "fold[bool] (lam a : * . lam t : a . lam f : a . f)"

fix :: Expr
fix =
  parse
    "lam a : * . lam f : a -> a . (lam x : (mu m . m -> a) . f ((unfold x) x)) (fold [mu m . m -> a] (lam x : (mu m . m -> a) .  f ((unfold x) x)))"

nat :: Expr
nat = parse "mu x . pi a : * . a -> (x -> a) -> a"

zero :: Expr
zero = parse "fold[nat] (lam a : * . lam z : a . lam f : (nat -> a) . z)"

suc :: Expr
suc = parse "lam n : nat . fold[nat] (lam a : * . lam z : a . lam f : (nat -> a) . f n)"

one :: Expr
one = App suc zero

two :: Expr
two = App suc one

three :: Expr
three = App suc two

plus :: Expr
plus = parse "fix (nat -> nat -> nat) (lam p : (nat -> nat -> nat) . lam n : nat . lam m : nat . (unfold n) nat m (lam l : nat . suc (p l m)))"

