module Main where

import Expr
import TypeCheck
import Syntax
import Parser

main :: IO ()
main = undefined


fix :: Expr
fix =
  parseExpr "lam a : * . lam f : (a -> a) . (lam x : (mu m . (m -> a)) . f ((unfold [mu m . (m -> a)] x) x)) (fold [mu m . (m -> a)] (lam x : (mu m . (m -> a)) .  f ((unfold [mu m . (m -> a)] x) x)))"

nat :: Expr
nat = Mu "x" $ Pi "a" (Kind Star) $ Var "a" `arr` (Var "x" `arr` Var "a" `arr` Var "a")

zero =
  App (F nat)
      (Lam "a" (Kind Star) $
       Lam "z" (Var "a") $
       Lam "f"
           (nat `arr`
            Var "a")
           (Var "z"))

suc =
  Lam "n" nat $
  App (F nat)
      (Lam "a" (Kind Star) $
       Lam "z" (Var "a") $
       Lam "f"
           (nat `arr`
            (Var "a")) $
       App (Var "f")
           (Var "n"))

one = App suc zero

two = App suc one

three = App suc two

plus =
  App (App fix
           (nat `arr`
            (nat `arr` nat)))
      (Lam "p"
           (nat `arr`
            (nat `arr` nat)) $
       Lam "n" nat $
       Lam "m" nat $
       App (App (App (App (U nat)
                          (Var "n"))
                     nat)
                (Var "m"))
           (Lam "n1" nat $
            App suc
                (App (App (Var "p")
                          (Var "n1"))
                     (Var "m"))))
