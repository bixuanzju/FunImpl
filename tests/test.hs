import Test.Tasty
import Test.Tasty.HUnit

import Expr
import Parser
import Syntax
import TypeCheck
-- import Predef
import Translation

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [substTest, patternTest, recordTest, recurTest]

-- natdt :: String
-- natdt = "data nat = zero | suc nat;"

listdt :: String
listdt = "data list (a : *) = nil | cons a (list a);"

maybedt :: String
maybedt = "data maybe (a : *) = nothing | just a;"

monad :: String
monad = "rec monad (m : * -> *) = mo { return : pi a : * . a -> m a, bind : pi a : *. pi b : *. m a -> (a -> m b) -> m b};"


listtest :: Expr
listtest = let Right (Progm [e]) = parseExpr $ listdt ++ "\\ x : (list nat) . cons nat 0 x"
           in e

pattest :: Expr
pattest =
  let Right (Progm [e]) = parseExpr $ listdt ++ "let alist : list nat = cons nat 1 (cons nat 2 (nil nat)) in let head : list nat -> nat = \\ x : list nat . case x of nil => 1000 | cons (x : nat) (xs : list nat) => x in head alist"
  in e

phoas :: Expr
phoas =
  let Right (Progm [e]) = parseExpr $ "data PLambda (a : *) = Var a | Num nat | Lam (a -> PLambda a) | App (PLambda a) (PLambda a); data Value = VI nat | VF (Value -> Value); let eval : PLambda Value -> Value = mu ev : PLambda Value -> Value . \\ e : PLambda Value . case e of Var (v : Value) => v | Num (n : nat) => VI n | Lam (f : Value -> PLambda Value) => VF (\\x : Value . ev (f x)) | App (a : PLambda Value) (b : PLambda Value) => case (ev a) of VI (n : nat) => VI n | VF (f : Value -> Value) => f (ev b) in let show : Value -> nat = \\ e : Value . case e of VI (n : nat) => n | VF (f : Value -> Value) => 10000 in let example : PLambda Value = App Value (Lam Value (\\ x : Value . Var Value x)) (Num Value 42) in show (eval example)"
  in e

recordtest :: Expr
recordtest = let Right (Progm [e]) = parseExpr $ listdt ++ "rec person = p { name : nat, addr : list nat}; addr (p 0 (cons nat 0 (nil nat)))"
             in e

recordtest2 :: Expr
recordtest2 = let Right (Progm [e]) = parseExpr $ maybedt ++ monad ++ "let inst : monad maybe = (mo maybe (\\ a : * . \\ x : a . nothing a) (\\ a : *. \\ b : *. \\ x : maybe a . \\ f : a -> maybe b . case x of nothing => nothing b | just (y : a) => f y)) in return maybe inst nat 0"
             in e

recurtest :: Expr
recurtest = let Right (Progm [e]) = parseExpr $ listdt ++ "let length : list nat -> nat = mu len : list nat -> nat . \\ l : list nat . case l of nil => 0 | cons (x : nat) (xs : list nat) => (len xs) + 1 in length (cons nat 0 (nil nat))"
             in e

recurTest :: TestTree
recurTest =
  testGroup "Recursive function"
    [testCase "length of lists" $
      (trans [] (desugar recurtest) >>= (\(_, e) -> eval (desugar e))) @?= Right (Lit 1)]

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
    ]

substTest :: TestTree
substTest =
  testGroup "Substitution"
    [testCase "same name" $
      subst "x" (Var "y") (Lam "x" (Kind Star) (Var "x")) @?=
      Lam "x" (Kind Star) (Var "x"), testCase "free vars" $
                                       subst "x" (Var "y") (Lam "y" (Kind Star) (App (Var "y") (Var "x"))) @?=
                                       Lam "y$" (Kind Star) (App (Var "y$") (Var "y"))]
