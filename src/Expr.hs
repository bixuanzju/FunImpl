module Expr where

import Data.List ((\\), union)
import Control.Monad (unless, when, liftM)

type Sym = String

data Expr = Var Sym
          | App Expr Expr
          | Lam Sym Type Expr
          | Pi Sym Type Type
          | Mu Sym Type
          | F Type
          | U Type
          | Kind Kinds
          deriving (Eq, Read, Show)

type Type = Expr

data Kinds = Star | Box deriving (Eq, Read, Show)

subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
  where sub e@(Var i) =
          if i == v then x else e
        sub (App f a) = App (sub f) (sub a)
        sub (Lam i t e) = abstr Lam i t e
        sub (Pi i t e) = abstr Pi i t e
        sub (Mu i t)
          | v == i = Mu i t
          | i `elem` fvx = let i' = cloneSym t i
                               t' = substVar i i' t
                           in Mu i' (sub t')
          | otherwise = Mu i (sub t)
        sub (F t) = F (sub t)
        sub (U t) = U (sub t)
        sub (Kind k) = Kind k
        abstr con i t e
          | v == i = con i (sub t) e -- type is also expression, need substitution
          | i `elem` fvx =
            let i' = cloneSym e i
                e' = substVar i i' e
            in con i' (sub t) (sub e')
          | otherwise = con i (sub t) (sub e)
        cloneSym e = loop
          where loop i' =
                  if i' `elem` vars
                     then loop (i' ++ "$")
                     else i'
                vars = fvx ++ freeVars e
        fvx = freeVars x

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' = subst s (Var s')

freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i _ e) = freeVars e \\ [i]
freeVars (Pi i k t) = freeVars k `union` (freeVars t \\ [i])
freeVars (Mu i t) = freeVars t \\ [i]
freeVars (F t) = freeVars t
freeVars (U t) = freeVars t
freeVars (Kind _) = []

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Pi s t e) (Pi s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Mu i t) (Mu i' t') = alphaEq t (substVar i' i t')
alphaEq (F t) (F t') = alphaEq t t'
alphaEq (U t) (U t') = alphaEq t t'
alphaEq (Kind k) (Kind k') = k == k'
alphaEq _ _ = False

-- nf :: Expr -> Expr
-- nf ee = spine ee []
--   where spine (App f a) as = spine f (a:as)
--         spine (Lam s t e) [] = Lam s (nf t) (nf e)
--         spine (Lam s _ e) (a:as) = spine (subst s a e) as
--         spine (Pi s k t) as = app (Pi s (nf k) (nf t)) as
--         spine (Mu i t) as = app (Mu i (nf t)) as
--         spine (U _) (App (F _) e:as) = app (nf e) as
--         spine (U t) (a:as) = spine (U t) (nf a:as)
--         spine (F t) (a:as) = spine (F t) (nf a:as)
--         spine f as = app f as
--         app f as = foldl App f (map nf as)

-- TODO: Need thoughts
whnf :: Expr -> Expr
whnf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s _ e) (a:as) = spine (subst s a e) as
        spine (U _) (App (F _) e:as) = spine e as
        -- spine (U t) as = spine e as
        -- spine (F t) as = spine e as
        spine f as = foldl App f as

-- betaEq :: Expr -> Expr -> Bool
-- betaEq e1 e2 = alphaEq (nf e1) (nf e2)

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
tcheck env (Var s) = findVar env s       -- (Var)
tcheck env (App f a) =                   -- (App)
  do tf <- tcheck env f
     case tf of
       Pi x at rt ->
         do ta <- tcheck env a
            unless (alphaEq ta at) $     -- up to alpha equivalence
              Left "Bad function argument type"
            return $ subst x a rt
       _ -> Left "Non-function in application"
tcheck env (Lam s t e) =                 -- (Lam)
  do let env' = extend s t env
     te <- tcheck env' e
     let lt = Pi s t te
     tcheck env lt
     return lt
tcheck _ (Kind Star) = return $ Kind Box -- (Ax)
tcheck _ (Kind Box) = Left "Found a Box"
tcheck env (Pi x a b) =                  -- (Pi)
  do s <- tcheck env a                   -- evaluate after type check
     let env' = extend x a env
     t <- tcheck env' b
     when ((s,t) `notElem` allowedKinds) $ Left "Bad abstraction"
     return t
tcheck env (Mu i t) =                    -- (Mu) TODO: Is star enough?
  do let env' = extend i (Kind Star) env
     s <- tcheck env' t
     when (s /= Kind Star) $ Left "Bad recursive type"
     return s
tcheck env (F mu@(Mu i t)) =             -- (Fold)
  do tcheck env mu
     let rt = subst i mu t
     return (rt `arr` mu)
tcheck env (U mu@(Mu i t)) =             -- (Unfold)
  do tcheck env mu
     let rt = subst i mu t
     return (mu `arr` rt)

allowedKinds :: [(Type, Type)]
allowedKinds =
  [(Kind Star,Kind Star)
  ,(Kind Star,Kind Box)
  ,(Kind Box,Kind Star)
  ,(Kind Box,Kind Box)]

-- tcheckT :: Env -> Expr -> TC Type
-- tcheckT env e = liftM nf (tcheck env e)

typeCheck :: Expr -> Type
typeCheck e =
  case tcheck initalEnv e of
    Left msg -> error ("Type error:\n" ++ msg)
    Right t -> t


arr :: Expr -> Expr -> Expr
arr = Pi ""

-- fixT :: Expr
-- fixT = Mu "m" (Var "m" `arr` Var "a")

-- fix :: Expr
-- fix =
--   Lam "a" (Kind Star) $
--   Lam "f"
--       (Var "a" `arr`
--        Var "a") $
--   App (Lam "x" fixT $
--        App (Var "f")
--            (App (App (U fixT)
--                      (Var "x"))
--                 (Var "x")))
--       (App (F fixT)
--            (Lam "x" fixT $
--             App (Var "f")
--                 (App (App (U fixT)
--                           (Var "x"))
--                      (Var "x"))))


-- fix' :: Expr
-- fix' =
--   Lam "a" (Kind Star) $
--   Lam "f"
--       (Var "a" `arr`
--        Var "a") $
--   App (Lam "x" fixT $
--        App (Var "f")
--            (Lam "y" fixT $
--             App (App (U fixT)
--                      (App (App (U fixT)
--                                (Var "x"))
--                           (Var "x")))
--                 (Var "y")))
--       (App (F fixT)
--            (Lam "x" fixT $
--             App (Var "f")
--                 (Lam "y" fixT $
--                  App (App (U fixT)
--                           (App (App (U fixT)
--                                     (Var "x"))
--                                (Var "x")))
--                      (Var "y"))))


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
