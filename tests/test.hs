import Test.Tasty
import Test.Tasty.HUnit
import Data.Either (isRight)

import Expr
import Parser
import Syntax
import TypeCheck
-- import Predef
import Translation

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [substTest, codeInPaper]

-- natdt :: String
-- natdt = "data nat = zero | suc nat;"

listdt :: String
listdt = "data List (a : *) = Nil | Cons (x:a) (xs : List a);"

maybedt :: String
maybedt = "data Maybe (a : *) = Nothing | Just (x:a);"

natdt :: String
natdt = "data Nat = Z | S (n:Nat);"

-- pairdt :: String
-- pairdt = "data PairT (a : *) (b : *) = Pair (x:a) (y:b);"

functor :: String
functor = "rcrd Functor (f : * -> *) = Func {fmap : (a : *) -> (b : *) -> (a -> b) -> f a -> f b};"

datatypes :: Expr
datatypes =
  let Right (Progm [e]) = parseExpr $ listdt ++ "letrec length : (a : *) -> List a -> nat = \\ a : * . \\l : List a . case l of Nil => 0 |  Cons (x : a) (xs : List a) => 1 + length a xs in let test : List nat = Cons nat 1 (Cons nat 2 (Nil nat)) in length nat test"
  in e

higherKinded :: Expr
higherKinded =
  let Right (Progm [e]) = parseExpr $ maybedt ++ functor ++ "let maybeInst : Functor Maybe = Func Maybe (\\ a : * . \\ b : * . \\f : a -> b . \\ x : Maybe a . case x of Nothing => Nothing b |  Just (z : a) => Just b (f z)) in maybeInst"
  in e

hoas :: Expr
hoas =
  let Right (Progm [e]) = parseExpr "data Exp = Num (n : nat) |  Lam (f : Exp -> Exp) |  App (a : Exp) (b : Exp); data Value = VI (n : nat) | VF (f : Value -> Value); rcrd Eval = Ev { eval' : Exp -> Value, reify' : Value -> Exp }; letrec ev : Eval = Ev  (\\ e : Exp . case e of Num (n : nat) => VI n | Lam (fun : Exp -> Exp) => VF (\\e' : Value . eval' ev (fun (reify' ev e'))) | App (a : Exp) (b : Exp) => case eval' ev a of VI (n : nat) => error | VF (fun : Value -> Value) => fun (eval' ev b)) (\\v : Value . case v of VI (n : nat) => Num n | VF (fun : Value -> Value) => Lam (\\e' : Exp . (reify' ev (fun (eval' ev e'))))) in let eval : Exp -> Value = eval' ev in let show : Value -> nat = \\v : Value . case v of VI (n : nat) => n | VF (fun : Value -> Value) => error in let test : Exp = App (Lam (\\ f : Exp . App f (Num 42))) (Lam (\\g : Exp. g)) in show (eval test)"
  in e

fixAsDatatype :: Expr
fixAsDatatype =
  let Right (Progm [e]) = parseExpr $ functor ++ "rcrd Fix (f : * -> *) = In {out : (f (Fix f)) }; letrec cata : (f : * -> *) -> (a : *) -> Functor f -> (f a -> a) -> Fix f -> a = \\f : * -> * . \\ a : * . \\ m : Functor f . \\ g : f a -> a. \\ t : Fix f . g (fmap f m (Fix f) a (cata f a m g) (out f t)) in cata"
  in e

kindPoly :: Expr
kindPoly =
  let Right (Progm [e]) = parseExpr "data Mu (k : *) (f : (k -> *) -> k -> *) (a : k) = Roll (g : (f (Mu k f) a)); data Listf (f : * -> *) (a : *) = Nil | Cons (x : a) (xs : (f a)); let List : * -> * = \\a : * . Mu * Listf a in let nil : List nat = Roll * Listf nat (Nil (Mu * Listf) nat) in nil"
  in e

nestedDT :: Expr
nestedDT =
  let Right (Progm [e]) = parseExpr $ listdt ++ "data PairT (a : *) = P (x : a) (x : a); data Pow (a : *) = Zero (n : a) | Succ (t : Pow (PairT a)); letrec foldr : (a : *) -> (b : *) -> (a -> b -> b) -> b -> List a -> b = \\a : * . \\b : * . \\f : a -> b -> b . \\y : b . \\l : List a . case l of Nil => y | Cons (x : a) (xs : List a) => f x (foldr a b f y xs) in letrec append : (a : *) -> List a -> List a -> List a = \\a : * . \\l : List a . \\m : List a . case l of Nil => m | Cons (x : a) (xs : List a) => Cons a x (append a xs m) in let concatMap : (a : *) -> (b : *) -> (a -> List b) -> List a -> List b = \\a : * . \\b : * . \\f : a -> List b . foldr a (List b) (\\x : a . \\y : List b . append b (f x) y) (Nil b) in letrec toList : (a : *) -> Pow a -> List a = \\a : * . \\t : Pow a . case t of Zero (x : a) => Cons a x (Nil a) | Succ (c : Pow (PairT a)) => concatMap (PairT a) a (\\ x : PairT a . case x of P (m : a) (n : a) => Cons a m (Cons a n (Nil a))) (toList (PairT a) c) in let head : List nat -> nat = \\ x : List nat . case x of Nil => error | Cons (x : nat) (xs : List nat) => x in let tail : List nat -> List nat = \\ x : List nat . case x of Nil => Nil nat | Cons (y : nat) (ys : List nat) => ys in let test : Pow nat = Succ nat (Zero (PairT nat) (P nat 42 43)) in head (toList nat test)"
  in e

dataPro :: Expr
dataPro =
  let Right (Progm [e]) = parseExpr $ natdt ++ "data PTree (n : Nat) = Empty | Fork (z : nat) (x : PTree (S n)) (y : PTree (S n)); Fork Z 1 (Empty (S Z)) (Empty (S Z))"
  in e

codeInPaper :: TestTree
codeInPaper =
  testGroup "Examples in the paper"
    [ testCase "Datatypes: typecheck" $
      (trans [] (desugar datatypes) >>= (\(_, e) -> tcheck [] (desugar e))) @?= Right Nat
    , testCase "Datatypes: eval" $
      (trans [] (desugar datatypes) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 2)
    , testCase "Higher-kinded Types: typecheck" $
      isRight (trans [] (desugar higherKinded) >>= (\(_, e) -> tcheck [] (desugar e))) @?= True
    , testCase "HOAS: typecheck" $
      (trans [] (desugar hoas) >>= (\(_, e) -> tcheck [] (desugar e))) @?= Right Nat
    , testCase "HOAS: eval" $
      (trans [] (desugar hoas) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 42)
    , testCase "Fix as a Datatype: typecheck" $
      isRight (trans [] (desugar fixAsDatatype) >>= (\(_, e) -> tcheck [] (desugar e))) @?= True
    , testCase "Kind Polymorphism: typecheck" $
      isRight (trans [] (desugar kindPoly) >>= (\(_, e) -> tcheck [] (desugar e))) @?= True
    , testCase "Nested Datatypes: typecheck" $
      (trans [] (desugar nestedDT) >>= (\(_, e) -> tcheck [] (desugar e))) @?= Right Nat
    , testCase "Nested Datatypes: eval" $
      (trans [] (desugar nestedDT) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 43)
    , testCase "Data Promotion: typecheck" $
      isRight (trans [] (desugar dataPro) >>= (\(_, e) -> tcheck [] (desugar e))) @?= True
    ]

substTest :: TestTree
substTest =
  testGroup "Substitution"
    [testCase "same name" $
      subst "x" (Var "y") (Lam "x" (Kind Star) (Var "x")) @?=
      Lam "x" (Kind Star) (Var "x"), testCase "free vars" $
                                       subst "x" (Var "y") (Lam "y" (Kind Star) (App (Var "y") (Var "x"))) @?=
                                       Lam "y$" (Kind Star) (App (Var "y$") (Var "y"))]
