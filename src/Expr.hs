module Expr where

import Data.List ((\\), union)
import Control.Monad (when)

type Sym = String

data Expr = Var Sym
          | App Expr Expr
          | Lam Sym Type Expr
          deriving (Eq, Read, Show)

data Type = Base
          | Arrow Type Type
          deriving (Eq, Read, Show)


whnf :: Expr -> Expr
whnf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s _ e) (a:as) = spine (subst s a e) as
        spine f as = foldl App f as

subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
  where sub e@(Var i) =
          if i == v
             then x
             else e
        sub (App f a) =
          App (sub f)
              (sub a)
        sub (Lam i t e)
          | v == i = Lam i t e
          | i `elem` fvx =
              let i' = cloneSym e i
                  e' = substVar i i' e
              in Lam i' t (sub e')
          | otherwise = Lam i t (sub e)
        fvx = freeVars x
        cloneSym e i = loop i
          where loop i' =
                  if i' `elem` vars
                     then loop (i ++ "$")
                     else i'
                vars = fvx ++ freeVars e

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' = subst s (Var s')

freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i _ e) = freeVars e \\ [i]

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s _ e) (Lam s' _ e') = alphaEq e (substVar s' s e')
alphaEq _ _ = False

nf :: Expr -> Expr
nf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s t e) [] = Lam s t (nf e)
        spine (Lam s _ e) (a:as) = spine (subst s a e) as
        spine f as = app f as
        app f as = foldl App f (map nf as)


betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

newtype Env = Env [(Sym, Type)] deriving (Show)

initalEnv :: Env
initalEnv = Env []

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s,t):r)

type ErrorMsg = String

type TC a = Either ErrorMsg a

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
  case lookup s r of
   Just t -> return t
   Nothing -> Left $ "Cannot find variable " ++ s

tcheck :: Env -> Expr -> TC Type
tcheck env (Var s) = findVar env s
tcheck env (App f a) = do
  tf <- tcheck env f
  case tf of
   Arrow at rt -> do
     ta <- tcheck env a
     when (ta /= at) $ Left "Bad function argument type"
     return rt
   _ -> Left "Non-function in application"
tcheck env (Lam s t e) = do
  let env' = extend s t env
  te <- tcheck env' e
  return $ Arrow t te

typeCheck :: Expr -> Type
typeCheck e = case tcheck initalEnv e of
               Left msg -> error ("Type error:\n" ++ msg)
               Right t -> t

test1 :: Expr
test1 = Lam "x" Base (Var "x")
