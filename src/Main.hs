module Main where

import System.Console.Haskeline

import Expr
import TypeCheck
import Translation
import Syntax
import Parser
-- import Predef

-- Note: 1. datatypes first, then record
--       2. first `desugar` to get rid of record, second desugar to get rid of let expression
main :: IO ()
main = runInputT defaultSettings (loop [] [])
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
          loop [] [] -- initalBEnv initalEnv
        ":env" -> do
          outputStrLn $ "Typing environment: " ++ show env
          outputStrLn $ "Binding environment: " ++ show (map fst benv)
          loop benv env
        ":add" -> delegate progm "Command parse error - :add name type" $
          \name xs -> do
            outputStrLn "Added!"
            loop benv (extend name (head xs) env)
        ":let" -> delegate progm "Command parse error - :let name expr" $
          \name xs -> do
            outputStrLn "Added new term!"
            loop ((name, head xs) : benv) env
        ":e" -> processCMD progm $
          \xs -> do
            if length xs == 1
              then case trans env (desugar . head $ xs) >>= \(_, transE) -> eval (desugar transE) of
                Left err -> outputStrLn err
                Right e' -> outputStrLn ("\n--- Evaluation result ---\n\n" ++ show e' ++ "\n")
              else outputStrLn "Command parser error - need one expression!"
            loop benv env
        -- ":eq" -> processCMD progm $
        --   \xs -> do
        --     if length xs == 2
        --       then outputStrLn . show $ equate benv (head xs) (xs !! 1)
        --       else outputStrLn "Command parser error - need two expressions!"
        --     loop benv env
        ":t" -> processCMD progm $
          \xs -> do
            if length xs == 1
              then case trans env (desugar . head $ xs) >>= \(_, transE) -> tcheck env (desugar transE) of
                Left err  -> outputStrLn err
                Right typ -> outputStrLn ("\n--- Typing result ---\n\n" ++ show typ ++ "\n")
              else outputStrLn "Command parser error - need one expression!"
            loop benv env
        -- ":teq" -> processCMD progm $
        --   \xs -> do
        --     if length xs == 2
        --       then case tcheck env . repFreeVar benv . head $ xs of
        --         Left err  -> outputStrLn err
        --         Right typ -> outputStrLn . show $ equate benv typ (xs !! 1)
        --       else outputStrLn "Command parser error - need two expressions!"
        --     loop benv env
        ":trans" ->
          processCMD progm $
            \xs -> do
              if length xs == 1
                then case trans env . desugar . head $ xs of
                  Left err          -> outputStrLn err
                  Right (_, transE) -> outputStrLn ("\n--- Translation result ---\n\n" ++ show transE ++ "\n")
                else outputStrLn "Command parser error - need one expression!"
              loop benv env
        _ -> processCMD e $
          \xs -> do
            outputStrLn ("\n--- Pretty printing ---\n\n" ++ concatMap show xs ++ "\n")
            loop benv env
      where
        processCMD expr func =
          case parseExpr . unwords $ expr of
            Left err -> do
              outputStrLn err
              loop benv env
            Right (Progm xs) -> func xs

        delegate progm errMsg func =
          if length progm >= 2
            then let (name:typ) = progm
                 in processCMD typ $
                   \xs -> if length xs == 1
                            then func name xs
                            else do
                              outputStrLn "Command parser error - need one expression!"
                              loop benv env
            else do
              outputStrLn errMsg
              loop benv env
