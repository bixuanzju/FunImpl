module Main where

import System.Console.Haskeline

import Expr
import TypeCheck
-- import Syntax
import Parser

main :: IO ()
main = runInputT defaultSettings (loop initalEnv)
  where loop :: Env -> InputT IO ()
        loop env =
          do minput <- getInputLine "pts> "
             case minput of
               Nothing -> return ()
               Just ":q" -> return ()
               Just cmds -> dispatch env cmds
        dispatch :: Env -> String -> InputT IO ()
        dispatch env cmds =
          case words cmds of
            ":add":name:typ ->
              do outputStrLn "Added!"
                 loop (extend name (parseExpr . unwords $ typ) env)
            ":clr":_ ->
              do outputStrLn "Environment cleaned up!"
                 loop initalEnv
            ":env":_ ->
              do outputStrLn (show env)
                 loop env
            ":e":expr ->
              do outputStrLn . show . whnf . parseExpr $ unwords expr
                 loop env
            ":t":expr ->
              case tcheck env . parseExpr $ unwords expr of
                Left err ->
                  do outputStrLn err
                     loop env
                Right typ ->
                  do outputStrLn . show $ typ
                     loop env
            _ ->
              do outputStrLn "Unknown command!"
                 loop env

-- fix :: Expr
-- fix =
--   parseExpr "lam a : * . lam f : (a -> a) . (lam x : (mu m . (m -> a)) . f ((unfold [mu m . (m -> a)] x) x)) (fold [mu m . (m -> a)] (lam x : (mu m . (m -> a)) .  f ((unfold [mu m . (m -> a)] x) x)))"

-- nat :: Expr
-- nat = Mu "x" $ Pi "a" (Kind Star) $ Var "a" `arr` (Var "x" `arr` Var "a" `arr` Var "a")

-- zero =
--   App (F nat)
--       (Lam "a" (Kind Star) $
--        Lam "z" (Var "a") $
--        Lam "f"
--            (nat `arr`
--             Var "a")
--            (Var "z"))

-- suc =
--   Lam "n" nat $
--   App (F nat)
--       (Lam "a" (Kind Star) $
--        Lam "z" (Var "a") $
--        Lam "f"
--            (nat `arr`
--             (Var "a")) $
--        App (Var "f")
--            (Var "n"))

-- one = App suc zero

-- two = App suc one

-- three = App suc two

-- plus =
--   App (App fix
--            (nat `arr`
--             (nat `arr` nat)))
--       (Lam "p"
--            (nat `arr`
--             (nat `arr` nat)) $
--        Lam "n" nat $
--        Lam "m" nat $
--        App (App (App (App (U nat)
--                           (Var "n"))
--                      nat)
--                 (Var "m"))
--            (Lam "n1" nat $
--             App suc
--                 (App (App (Var "p")
--                           (Var "n1"))
--                      (Var "m"))))
