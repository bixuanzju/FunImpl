import Test.Tasty
import Test.Tasty.HUnit

import Expr

-- Examples

zero :: Expr
zero =
  Lam "a"
      (Kind Star)
      (Lam "s"
           (Pi "_"
               (Var "a")
               (Var "a"))
           (Lam "z" (Var "a") (Var "z")))

one :: Expr
one =
  Lam "a"
      (Kind Star)
      (Lam "f"
           (Pi "_"
               (Var "a")
               (Var "a"))
           (Lam "z"
                (Var "a")
                (App (Var "f")
                     (Var "z"))))

two :: Expr
two =
  Lam "a"
      (Kind Star)
      (Lam "f"
           (Pi "_"
               (Var "a")
               (Var "a"))
           (Lam "z"
                (Var "a")
                (App (Var "f")
                     (App (Var "f")
                          (Var "z")))))

three :: Expr
three =
  Lam "a"
      (Kind Star)
      (Lam "f"
           (Pi "_"
               (Var "a")
               (Var "a"))
           (Lam "z"
                (Var "a")
                (App (Var "f")
                     (App (Var "f")
                          (App (Var "f")
                               (Var "z"))))))

natType :: Expr
natType =
  Pi "a"
     (Kind Star)
     (Pi "s"
         (Pi "_"
             (Var "a")
             (Var "a"))
         (Pi "z"
             (Var "a")
             (Var "a")))

plus :: Expr
plus =
  Lam "m"
      natType
      (Lam "n"
           natType
           (Lam "a"
                (Kind Star)
                (Lam "f"
                     (Pi "_"
                         (Var "a")
                         (Var "a"))
                     (Lam "z"
                          (Var "a")
                          (App (App (App (Var "m")
                                         (Var "a"))
                                    (Var "f"))
                               (App (App (App (Var "n")
                                              (Var "a"))
                                         (Var "f"))
                                    (Var "z")))))))


idd :: Expr
idd = Lam "a" (Kind Star) (Lam "x" (Var "a") (Var "x"))

env1 :: Env
env1 = extend "a" (Kind Star) initalEnv

env2 :: Env
env2 = extend "d" (Pi "_" natType (Kind Star)) env1

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [substTest,natTest,tcheckTest]


tcheckTest :: TestTree
tcheckTest =
  testGroup "Type check"
            [testCase "type depend on term" $
             tcheck env1
                    (Pi "_"
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
             Right (Kind Star)]

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
            [testCase "one plus two equal three" $
             betaEq (App (App plus one) two) three @?=
             True]
