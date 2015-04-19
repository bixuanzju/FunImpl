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
        sub (Mu i t) = -- evil code in order to reuse `abstr`
          case abstr Lam i t t of
           Lam i' t' _ -> Mu i' t'
        sub (F t) = F (sub t)
        sub (U e) = U (sub e)
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
freeVars (U e) = freeVars e
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

desugar :: Expr -> Expr
desugar (Var n) = Var n
desugar (App e1 e2) = App (desugar e1) (desugar e2)
desugar (Lam n t e) = Lam n (desugar t) (desugar e)
desugar (Pi n t e) = Pi n (desugar t) (desugar e)
desugar (Mu n t) = Mu n (desugar t)
desugar (F t) = F (desugar t)
desugar (U t) = U (desugar t)
desugar (Beta e) = Beta (desugar e)
desugar e@(Kind _) = e
desugar (Let n t e1 e2) = App (Lam n t (desugar e2)) (desugar e1)

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

type BEnv = [(Sym, Expr)]

whnf :: BEnv -> Expr -> Expr
whnf benv ee = spine ee []
  where
    spine (App f a) as = spine f (a : as)
    spine (Lam s _ e) (a:as) = spine (subst s a e) as
    spine (U (App (F _) e)) as = spine e as
    spine (U e) as = spine (U (whnf benv e)) as
    spine (Var n) as =          -- fill in pre-defined terms
      case lookup n benv of
        Nothing -> foldl App (Var n) as
        Just e  -> spine e as
    spine f as = foldl App f as

-- | Definitional equality because we use weak head normal form
equate :: BEnv -> Expr -> Expr -> Bool
equate benv e1 e2 =
  let e1' = whnf benv . desugar $ e1
      e2' = whnf benv . desugar $ e2
  in case (e1',e2') of
       (App a1 b1,App a2 b2) ->
         equate benv a1 a2 &&
         equate benv b1 b2
       (Lam n _ a,Lam n1 _ a1) ->
         equate benv a (substVar n1 n a1)
       (Pi n _ a,Pi n1 _ a1) ->
         equate benv a (substVar n1 n a1)
       (Mu n t,Mu n1 t1) ->
         equate benv t (substVar n1 n t1)
       (F t,F t1) -> equate benv t t1
       (U t,U t1) -> equate benv t t1
       (Beta t,Beta t1) -> equate benv t t1
       (Var n1,Var n2) -> n1 == n2
       (_,_) -> False
