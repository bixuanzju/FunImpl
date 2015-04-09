module Main where

import System.Console.Haskeline

import Expr
import TypeCheck
import Syntax
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
                 let Progm [expr] = parseExpr . unwords $ typ
                 loop (extend name expr env)
            ":clr":_ ->
              do outputStrLn "Environment cleaned up!"
                 loop initalEnv
            ":env":_ ->
              do outputStrLn (show env)
                 loop env
            ":e":expr ->
              do let Progm [e] = parseExpr . unwords $ expr
                 outputStrLn . show . whnf $ e
                 loop env
            ":eq":exprs ->
              do let Progm xs = parseExpr . unwords $ exprs
                 if length xs == 2 then outputStrLn . show $ equate (whnf (head xs)) (whnf (xs !! 1))
                   else outputStrLn "Parser error: need two expressions!"
                 loop env
            ":t":expr ->
              let Progm [e] = parseExpr . unwords $ expr
              in case tcheck env e of
                  Left err ->
                    do outputStrLn err
                       loop env
                  Right typ ->
                    do outputStrLn . show $ typ
                       loop env
            _ -> loop env
