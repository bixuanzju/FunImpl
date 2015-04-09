module Expr where

import Data.List ((\\), union)
import Syntax

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
        sub (Beta t) = Beta (sub t)
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
freeVars (Beta t) = freeVars t
freeVars (Kind _) = []

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Pi s t e) (Pi s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Mu i t) (Mu i' t') = alphaEq t (substVar i' i t')
alphaEq (F t) (F t') = alphaEq t t'
alphaEq (U t) (U t') = alphaEq t t'
alphaEq (Beta t) (Beta t') = alphaEq t t'
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
        -- spine (F t) (a:as) = spine (F t) (whnf a:as)
        -- spine (U t) (a:as) = spine (U t) (whnf a:as)
        spine f as = foldl App f as

-- | Definitional equality because we use weak head normal form
equate :: Expr -> Expr -> Bool
equate e1 e2 =
  let e1' = whnf e1
      e2' = whnf e2
  in case (e1',e2') of
       (App a1 b1,App a2 b2) ->
         equate a1 a2 &&
         equate b1 b2
       (Lam n _ a,Lam n1 _ a1) ->
         equate a (substVar n1 n a1)
       (Pi n _ a,Pi n1 _ a1) ->
         equate a (substVar n1 n a1)
       (Mu n t,Mu n1 t1) ->
         equate t (substVar n1 n t1)
       (F t,F t1) -> equate t t1
       (U t,U t1) -> equate t t1
       (Beta t,Beta t1) -> equate t t1
       (Var n1,Var n2) -> n1 == n2
       (_,_) -> False
