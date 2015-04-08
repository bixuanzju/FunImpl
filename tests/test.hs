import Test.Tasty
import Test.Tasty.HUnit

import Expr
import Parser
import Syntax
import TypeCheck

-- Examples

zero :: Expr
zero = parseExpr "lam a : * . lam s : (a -> a) . lam z : a . z"

one :: Expr
one = parseExpr "lam a : * . lam s : (a -> a) . lam z : a . s z"

two :: Expr
two = parseExpr "lam a : * . lam s : (a -> a) . lam z : a . s (s z)"

three :: Expr
three = parseExpr "lam a : * . lam s : (a -> a) . lam z : a . s (s (s z))"

plus :: Expr
plus = parseExpr "lam m : (pi a : * . pi s : (a -> a) . pi z : a . a) . lam n : (pi a : * . pi s : (a -> a) . pi z : a . a) . lam a : * . lam f : (a -> a) . lam z : a . (m a f) (n a f z)"

natType :: Expr
natType = parseExpr "pi a : * . pi s : (a -> a) . pi z : a . a"

env1 :: Env
env1 = extend "a" (Kind Star) initalEnv

env2 :: Env
env2 = extend "d" (Pi "" natType (Kind Star)) env1

fix :: Expr
fix =
  parseExpr "lam a : * . lam f : (a -> a) . (lam x : (mu m . (m -> a)) . f ((unfold [mu m . (m -> a)] x) x)) (fold [mu m . (m -> a)] (lam x : (mu m . (m -> a)) .  f ((unfold [mu m . (m -> a)] x) x)))"

hT :: Expr
hT = Mu "m" (Pi "" (Var "a") (Var "m"))

hungry :: Expr
hungry =
  Lam "a" (Kind Star) $
  App (App fix (Pi "" (Var "a") hT))
      (Lam "f" (Pi "" (Var "a") hT) $
       Lam "x" (Var "a") $
       App (F hT)
           (Var "f"))

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [natTest, substTest,tcheckTest]


tcheckTest :: TestTree
tcheckTest =
  testGroup "Type check"
            [testCase "type depend on term" $
             tcheck env1
                    (Pi ""
                        (Var "a")
                        (Kind Star)) @?=
             Right (Kind Box)
            ,testCase "A simple term with a type that depends on a term" $
             tcheck env1
                    (Lam "x"
                         (Var "a")
                         (Var "a")) @?=
             Right (Pi "x"
                       (Var "a")
                       (Kind Star))
            ,testCase "Apply a dependent type" $
             tcheck env2 (App (Var "d") zero) @?=
             Right (Kind Star)
            ,testCase "Fix combinator" $
             tcheck initalEnv fix @?=
             Right (Pi "a"
                       (Kind Star)
                       (Pi "f"
                           (Pi ""
                               (Var "a")
                               (Var "a"))
                           (Var "a")))
            ,testCase "Hungry function takes two arguments" $
             tcheck (extend "x"
                            (Var "a")
                            (extend "a" (Kind Star) initalEnv))
                    (App (App (U hT)
                              (App (App hungry (Var "a"))
                                   (Var "x")))
                         (Var "x")) @?=
             Right hT
            ]

substTest :: TestTree
substTest =
  testGroup "Substitution"
            [testCase "same name" $
             subst "x"
                   (Var "y")
                   (Lam "x"
                        (Kind Star)
                        (Var "x")) @?=
             Lam "x"
                 (Kind Star)
                 (Var "x")
            ,testCase "free vars" $
             subst "x"
                   (Var "y")
                   (Lam "y"
                        (Kind Star)
                        (App (Var "y")
                             (Var "x"))) @?=
             Lam "y$"
                 (Kind Star)
                 (App (Var "y$")
                      (Var "y"))]

natTest :: TestTree
natTest =
  testGroup "Natural number"
            [testCase "one plus two" $
             equate (whnf (App (App plus one) two)) three @?=
             True]
