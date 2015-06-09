import Test.Tasty
import Test.Tasty.HUnit

import Expr
import Parser
import Syntax
import TypeCheck
import Predef
import Translation

env1 :: Env
env1 = extend "a" (Kind Star) initalEnv

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [substTest, tcheckTest, datatypeTest, patternTest, recordTest, recurTest]

natdt :: String
natdt = "data nat = zero | suc nat;"

listdt :: String
listdt = "data list (a : *) = nil | cons a (list a);"

maybedt :: String
maybedt = "data maybe (a : *) = nothing | just a;"

monad :: String
monad = "rec monad (m : * -> *) = mo { return : pi a : * . a -> m a, bind : pi a : *. pi b : *. m a -> (a -> m b) -> m b};"

nattest1 :: Expr
nattest1 = let Right (Progm [e]) =  parseExpr $ natdt ++ "\\ x : nat . x"
           in e

nattest2 :: Expr
nattest2 = let Right (Progm [e]) =  parseExpr $ natdt ++ "\\ x : nat . suc zero"
           in e

listtest :: Expr
listtest = let Right (Progm [e]) = parseExpr $ natdt ++ listdt ++ "\\ x : (list nat) . cons nat zero x"
           in e

pattest :: Expr
pattest = let Right (Progm [e]) = parseExpr $ natdt ++ listdt ++ "\\ x : list nat . case x of nil => zero | cons (x : nat) (xs : list nat) => suc (suc x)"
              in e
recordtest :: Expr
recordtest = let Right (Progm [e]) = parseExpr $ natdt ++ listdt ++ "rec person = p { name : nat, addr : list nat}; addr (p zero (cons nat zero (nil nat)))"
             in e

recordtest2 :: Expr
recordtest2 = let Right (Progm [e]) = parseExpr $ natdt ++ maybedt ++ monad ++ "let inst : monad maybe = (mo maybe (\\ a : * . \\ x : a . nothing a) (\\ a : *. \\ b : *. \\ x : maybe a . \\ f : a -> maybe b . case x of nothing => nothing b | just (y : a) => f y)) in return maybe inst nat zero"
             in e

recurtest :: Expr
recurtest = let Right (Progm [e]) = parseExpr $ natdt ++ listdt ++ "let length : list nat -> nat = mu len : list nat -> nat . \\ l : list nat . case l of nil => zero | cons (x : nat) (xs : list nat) => suc (len xs) in length (cons nat zero (nil nat))"
             in e

recurTest :: TestTree
recurTest =
  testGroup "Recursive function"
    [testCase "length of lists" $
      (trans [] (desugar recurtest) >>= (\(t, _) -> return t)) @?= Right (Var "nat")]

recordTest :: TestTree
recordTest =
  testGroup "Record check"
    [ testCase "record" $
      (trans [] (desugar recordtest) >>= (\(t, _) -> return t)) @?= Right (App (Var "list") (Var "nat"))
    , testCase "monad" $
      (trans [] (desugar recordtest2) >>= (\(t, _) -> return t)) @?= Right (App (Var "maybe") (Var "nat"))
    ]

datatypeTest :: TestTree
datatypeTest =
  testGroup "Datatype check"
    [ testCase "natural number" $
      tcheck [] nattest1 @?= Right (Pi "x" (Var "nat") (Var "nat"))
    , testCase "successor of zero" $
      tcheck [] nattest2 @?= Right (Pi "x" (Var "nat") (Var "nat"))
    , testCase "list of natural numbers" $
      tcheck [] listtest @?= Right (Pi "x" (App (Var "list") (Var "nat")) (App (Var "list") (Var "nat")))
    ]

patternTest :: TestTree
patternTest =
  testGroup "Pattern matching check"
    [testCase "case analysis" $
      tcheck [] pattest @?= Right (Pi "x" (App (Var "list") (Var "nat")) (Var "nat"))]

tcheckTest :: TestTree
tcheckTest =
  testGroup "Type check"
    [testCase "type depend on term" $
      tcheck env1 (Pi "" (Var "a") (Kind Star)) @?=
      Right (Kind Box), testCase "A simple term with a type that depends on a term" $
                          tcheck env1 (Lam "x" (Var "a") (Var "a")) @?=
                          Right (Pi "x" (Var "a") (Kind Star))]

substTest :: TestTree
substTest =
  testGroup "Substitution"
    [testCase "same name" $
      subst "x" (Var "y") (Lam "x" (Kind Star) (Var "x")) @?=
      Lam "x" (Kind Star) (Var "x"), testCase "free vars" $
                                       subst "x" (Var "y") (Lam "y" (Kind Star) (App (Var "y") (Var "x"))) @?=
                                       Lam "y$" (Kind Star) (App (Var "y$") (Var "y"))]

-- natTest :: TestTree
-- natTest =
--   testGroup "Natural number"
--     [testCase "one plus two" $
--       equate initalBEnv (App (App plus one) two) three @?=
--       True]
