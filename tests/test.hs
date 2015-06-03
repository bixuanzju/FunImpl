import Test.Tasty
import Test.Tasty.HUnit

import Expr
import Parser
import Syntax
import TypeCheck
import Predef

env1 :: Env
env1 = extend "a" (Kind Star) initalEnv

-- env2 :: Env
-- env2 = extend "d" (Pi "" nat (Kind Star)) env1

-- hT :: Expr
-- hT = Mu "m" (Pi "" (Var "a") (Var "m"))

-- hungry :: Expr
-- hungry =
--   Lam "a" (Kind Star) $
--     App (App fix (Pi "" (Var "a") hT))
--       (Lam "f" (Pi "" (Var "a") hT) $
--          Lam "x" (Var "a") $
--            App (F hT) (Var "f"))

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [substTest, tcheckTest, datatypeTest, patternTest]


-- letTest :: TestTree
-- letTest =
--   testGroup "Let check"
--     [ testCase "nested let in" $
--       equate initalBEnv (parse "let a : nat = one in let b : nat = two in plus a b")
--         (parse "plus two one") @?= True
--     ]

nattest1 :: Expr
nattest1 = let Right (Progm [e]) =  parseExpr "data nat = zero | suc nat; lam x : nat . x"
           in e

nattest2 :: Expr
nattest2 = let Right (Progm [e]) =  parseExpr "data nat = zero | suc nat; data list (a : *) = nil | cons a (list a); lam x : nat . suc zero"
           in e

listtest :: Expr
listtest = let Right (Progm [e]) = parseExpr "data nat = zero | suc nat; data list (a : *) = nil | cons a (list a); lam x : (list nat) . cons nat zero x"
           in e

pattest :: Expr
pattest = let Right (Progm [e]) = parseExpr "data nat = zero | suc nat; data list (a : *) = nil | cons a (list a); lam x : list nat . case x of nil => zero | cons (x : nat) (xs : list nat) => suc (suc x)"
              in e

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
    [ testCase "type depend on term" $
      tcheck env1 (Pi "" (Var "a") (Kind Star)) @?=
      Right (Kind Box)
    , testCase "A simple term with a type that depends on a term" $
      tcheck env1 (Lam "x" (Var "a") (Var "a")) @?=
      Right (Pi "x" (Var "a") (Kind Star))
    ,
    -- ,testCase "Apply a dependent type" $
    --  tcheck env2 (App (Var "d") zero) @?=
    --  Right (Kind Star)
    testCase "Fix combinator" $
      tcheck initalEnv fix @?=
      Right (Pi "a" (Kind Star) (Pi "f" (Pi "" (Var "a") (Var "a")) (Var "a")))
    -- , testCase "Hungry function takes two arguments" $
    --   tcheck (extend "x" (Var "a") (extend "a" (Kind Star) initalEnv))
    --     (App (App (U hT) (App (App hungry (Var "a")) (Var "x"))) (Var "x")) @?=
    --   Right hT
    ]

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
