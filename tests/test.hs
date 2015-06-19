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
tests = testGroup "Tests" [substTest, patternTest, recordTest, recurTest, kindPolyTest]

-- natdt :: String
-- natdt = "data nat = zero | suc nat;"

listdt :: String
listdt = "data list (a : *) = nil | cons a (list a);"

maybedt :: String
maybedt = "data maybe (a : *) = nothing | just a;"

monad :: String
monad = "rec monad (m : * -> *) = mo { return : pi a : * . a -> m a, bind : pi a : *. pi b : *. m a -> (a -> m b) -> m b};"

-- listtest :: Expr
-- listtest = let Right (Progm [e]) = parseExpr $ listdt ++ "\\ x : (list nat) . cons nat 0 x"
--            in e

pattest :: Expr
pattest =
  let Right (Progm [e]) = parseExpr $ listdt ++ "let alist : list nat = cons nat 1 (cons nat 2 (nil nat)) in let head : list nat -> nat = \\ x : list nat . case x of nil => 1000 | cons (x : nat) (xs : list nat) => x in head alist"
  in e

phoas :: Expr
phoas =
  let Right (Progm [e]) = parseExpr "data PLambda (a : *) = Var a | Num nat | Lam (a -> PLambda a) | App (PLambda a) (PLambda a); data Value = VI nat | VF (Value -> Value); letrec eval : PLambda Value -> Value = \\ e : PLambda Value . case e of Var (v : Value) => v | Num (n : nat) => VI n | Lam (f : Value -> PLambda Value) => VF (\\x : Value . eval (f x)) | App (a : PLambda Value) (b : PLambda Value) => case (eval a) of VI (n : nat) => VI n | VF (f : Value -> Value) => f (eval b) in let show : Value -> nat = \\ e : Value . case e of VI (n : nat) => n | VF (f : Value -> Value) => 10000 in let example : PLambda Value = App Value (Lam Value (\\ x : Value . Var Value x)) (Num Value 42) in show (eval example)"
  in e

perfectBinaryTree :: Expr
perfectBinaryTree =
  let Right (Progm [e]) = parseExpr "data Nat = Z | S Nat; data PairT (a : *) (b : *) = Pair a b; data B (a : *) = One a | Two (B (PairT a a)); data List (a : *) = Nil | Cons a (List a); letrec pairs : (a : *) -> List a -> List (PairT a a) = \\ a : * . \\ xs : List a . case xs of Nil => Nil (PairT a a) | Cons (y : a) (ys : List a) => case ys of Nil => Nil (PairT a a) | Cons (y' : a) (ys' : List a) => Cons (PairT a a) (Pair a a y y') (pairs a ys') in letrec fromList : (a : *) -> List a -> B a = \\ a : * . \\xs : List a . case xs of Nil => Two a (fromList (PairT a a) (pairs a (Nil a))) | Cons (x : a) (xs' : List a) => case xs' of Nil => One a x | Cons (y : a) (zs : List a) => Two a (fromList (PairT a a) (pairs a xs)) in letrec take : Nat -> List nat -> List nat = \\ n : Nat . \\ l : List nat . case n of Z => Nil nat | S (m : Nat) => case l of Nil => Nil nat | Cons (x : nat) (xs : List nat) => Cons nat x (take m xs) in letrec repeat : nat -> List nat = \\ x : nat . Cons nat x (repeat x) in letrec twos : (a : *) -> B a -> nat = \\ a : * . \\x : B a . case x of One (y : a) => 0 | Two (c : B (PairT a a)) => 1 + twos (PairT a a) c in let powerTwo : Nat -> nat = \\ n : Nat . twos nat (fromList nat (take n (repeat 1))) in powerTwo (S (S (S (S Z))))"
  in e

kindPoly :: Expr
kindPoly = let Right (Progm [e]) = parseExpr $ listdt ++ "data TApp (k : *) (f : k -> *) (a : k) = MkTApp (f a); MkTApp * (\\ x : * . x) nat (fold 1 [(\\ x : * . x) nat] 3)"
             in e

recordtest :: Expr
recordtest = let Right (Progm [e]) = parseExpr $ listdt ++ "rec person = p { name : nat, addr : list nat}; addr (p 0 (cons nat 0 (nil nat)))"
             in e

recordtest2 :: Expr
recordtest2 = let Right (Progm [e]) = parseExpr $ maybedt ++ monad ++ "let inst : monad maybe = (mo maybe (\\ a : * . \\ x : a . nothing a) (\\ a : *. \\ b : *. \\ x : maybe a . \\ f : a -> maybe b . case x of nothing => nothing b | just (y : a) => f y)) in return maybe inst nat 0"
             in e

recurtest :: Expr
recurtest = let Right (Progm [e]) = parseExpr $ listdt ++ "letrec length : list nat -> nat = \\ l : list nat . case l of nil => 0 | cons (x : nat) (xs : list nat) => (length xs) + 1 in length (cons nat 0 (nil nat))"
             in e

recurTest :: TestTree
recurTest =
  testGroup "Recursive function"
    [testCase "length of lists" $
      (trans [] (desugar recurtest) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 1)]

kindPolyTest :: TestTree
kindPolyTest =
  testGroup "Kind polymorphism"
    [testCase "data TApp (k : *) (f : k -> *) (a : k) = MkTApp (f a)" $
      isRight (trans [] (desugar kindPoly) >>= (\(_, e) -> tcheck [] (desugar e))) @?= True]

recordTest :: TestTree
recordTest =
  testGroup "Record check"
    [ testCase "record" $
      (trans [] (desugar recordtest) >>= (\(t, _) -> return t)) @?= Right (App (Var "list") Nat)
    , testCase "monad" $
      (trans [] (desugar recordtest2) >>= (\(t, _) -> return t)) @?= Right (App (Var "maybe") Nat)
    ]

patternTest :: TestTree
patternTest =
  testGroup "Pattern matching check"
    [ testCase "typecheck: case analysis" $
      (trans [] (desugar pattest) >>= (\(_, e) -> tcheck [] (desugar e))) @?= Right Nat
    , testCase "evaluation: case analysis" $
      (trans [] (desugar pattest) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 1)
    , testCase "typecheck: PHOAS" $
      (trans [] (desugar phoas) >>= (\(_, e) -> tcheck [] (desugar e))) @?= Right Nat
    , testCase "evaluation: PHOAS" $
      (trans [] (desugar phoas) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 42)
    , testCase "evaluation: Perfect binary tree" $
      (trans [] (desugar perfectBinaryTree) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 2)
    ]

substTest :: TestTree
substTest =
  testGroup "Substitution"
    [testCase "same name" $
      subst "x" (Var "y") (Lam "x" (Kind Star) (Var "x")) @?=
      Lam "x" (Kind Star) (Var "x"), testCase "free vars" $
                                       subst "x" (Var "y") (Lam "y" (Kind Star) (App (Var "y") (Var "x"))) @?=
                                       Lam "y$" (Kind Star) (App (Var "y$") (Var "y"))]
