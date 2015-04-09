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
            _ -> loop env
