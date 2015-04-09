module Main where

import System.Console.Haskeline

import Expr
import TypeCheck
import Syntax
import Parser
import Predef

main :: IO ()
main = runInputT defaultSettings (loop initalBEnv initalEnv)
  where loop :: BEnv -> Env -> InputT IO ()
        loop benv env =
          do minput <- getInputLine "pts> "
             case minput of
               Nothing -> return ()
               Just ":q" -> return ()
               Just cmds -> dispatch benv env cmds
        dispatch :: BEnv -> Env -> String -> InputT IO ()
        dispatch benv env cmds =
          case words cmds of
            ":add":name:typ ->
              do outputStrLn "Added!"
                 let Progm [expr] = parseExpr . unwords $ typ
                 loop benv (extend name (repFreeVar benv expr) env)
            ":let":name:e ->
              do outputStrLn "Added new term!"
                 let Progm [expr] = parseExpr . unwords $ e
                 let newEnv = (name, repFreeVar benv expr):benv
                 loop newEnv env
            ":clr":_ ->
              do outputStrLn "Environment cleaned up!"
                 loop initalBEnv initalEnv
            ":env":_ ->
              do outputStrLn $ "Typing environment: " ++ show env
                 outputStrLn $ "Binding environment: " ++ show (map fst benv)
                 loop benv env
            ":e":expr ->
              do let Progm xs = parseExpr . unwords $ expr
                 if length xs == 1 then outputStrLn . show . whnf benv . head $ xs
                   else outputStrLn "Parser error: need one expressions!"
                 loop benv env
            ":eq":exprs ->
              do let Progm xs = parseExpr . unwords $ exprs
                 if length xs == 2 then outputStrLn . show $ equate benv (head xs) (xs !! 1)
                   else outputStrLn "Parser error: need two expressions!"
                 loop benv env
            ":t":expr ->
              let Progm xs = parseExpr . unwords $ expr
              in if length xs == 1
                 then case tcheck env . repFreeVar benv .  head $ xs of
                       Left err ->
                         do outputStrLn err
                            loop benv env
                       Right typ ->
                         do outputStrLn . show $ typ
                            loop benv env
                 else outputStrLn "Parser error: need one expressions!"
            _ -> loop benv env

-- fix :: Expr
-- fix =
--   let (Progm [expr]) = parseExpr
--                          "lam a : * . lam f : (a -> a) . (lam x : (mu m . (m -> a)) . f ((unfold [mu m . (m -> a)] x) x)) (fold [mu m . (m -> a)] (lam x : (mu m . (m -> a)) .  f ((unfold [mu m . (m -> a)] x) x)))"
--   in expr

-- nat :: Expr
-- nat = Mu "x" $ Pi "a" (Kind Star) $ Var "a" `arr` (Var "x" `arr` Var "a" `arr` Var "a")

-- zero :: Expr
-- zero =
--   App (F nat)
--     (Lam "a" (Kind Star) $
--        Lam "z" (Var "a") $
--          Lam "f" (nat `arr`
--                   Var "a") (Var "z"))

-- suc :: Expr
-- suc =
--   Lam "n" nat $
--     App (F nat)
--       (Lam "a" (Kind Star) $
--          Lam "z" (Var "a") $
--            Lam "f" (nat `arr`
--                     Var "a") $
--              App (Var "f") (Var "n"))

-- one :: Expr
-- one = App suc zero

-- two :: Expr
-- two = App suc one

-- three :: Expr
-- three = App suc two

-- plus :: Expr
-- plus =
--   App
--     (App fix (nat `arr`
--               (nat `arr` nat)))
--     (Lam "p" (nat `arr`
--               (nat `arr` nat)) $
--        Lam "n" nat $
--          Lam "m" nat $
--            App (App (App (App (U nat) (Var "n")) nat) (Var "m"))
--              (Lam "n1" nat $
--                 App suc (App (App (Var "p") (Var "n1")) (Var "m"))))

