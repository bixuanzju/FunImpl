module Main where

import System.Console.Haskeline

import Expr
import TypeCheck
import Syntax
import Parser
import Predef

main :: IO ()
main = runInputT defaultSettings (loop initalBEnv initalEnv)
  where
    loop :: BEnv -> Env -> InputT IO ()
    loop benv env =
      do
        minput <- getInputLine "pts> "
        case minput of
          Nothing   -> return ()
          Just ""   -> loop benv env
          Just ":q" -> return ()
          Just cmds -> dispatch benv env cmds
    dispatch :: BEnv -> Env -> String -> InputT IO ()
    dispatch benv env cmds =
      let e@(cmd:progm) = words cmds
      in case cmd of
        ":clr" -> do
          outputStrLn "Environment cleaned up!"
          loop initalBEnv initalEnv
        ":env" -> do
          outputStrLn $ "Typing environment: " ++ show env
          outputStrLn $ "Binding environment: " ++ show (map fst benv)
          loop benv env
        ":add" ->
          if length progm >= 2
            then let (name:typ) = progm
                 in processCMD typ $
                   \xs -> if length xs == 1
                            then do
                              outputStrLn "Added!"
                              loop benv (extend name (repFreeVar env (head xs)) env)
                            else do
                              outputStrLn "Command parser error - need one expression!"
                              loop benv env
            else do
              outputStrLn "Command parse error - :add name type"
              loop benv env
        ":let" ->
          if length progm >= 2
            then let (name:expr) = progm
                 in processCMD expr $
                   \xs -> if length xs == 1
                            then do
                              outputStrLn "Added new term!"
                              loop ((name, repFreeVar benv (head xs)) : benv) env
                            else do
                              outputStrLn "Command parser error - need one expression!"
                              loop benv env
            else do
              outputStrLn "Command parse error - :let name expr"
              loop benv env
        ":e" -> processCMD progm $
          \xs -> do
            if length xs == 1
              then outputStrLn . show . whnf benv . head $ xs
              else outputStrLn "Command parser error - need one expression!"
            loop benv env
        ":eq" -> processCMD progm $
          \xs -> do
            if length xs == 2
              then outputStrLn . show $ equate benv (head xs) (xs !! 1)
              else outputStrLn "Command parser error - need two expressions!"
            loop benv env
        ":t" -> processCMD progm $
          \xs -> do
            if length xs == 1
              then case tcheck env . repFreeVar benv . head $ xs of
                Left err  -> outputStrLn err
                Right typ -> outputStrLn . show $ typ
              else outputStrLn "Command parser error - need one expression!"
            loop benv env
        _ -> processCMD e $
          \xs -> do
            outputStrLn . show $ xs
            loop benv env
      where
        processCMD expr func =
          case parseExpr . unwords $ expr of
            Left err -> do
              outputStrLn err
              loop benv env
            Right (Progm xs) -> func xs
