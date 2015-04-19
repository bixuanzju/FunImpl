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
        sub (F t e) = F (sub t) (sub e)
        sub (U e) = U (sub e)
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
freeVars (F t e) = freeVars t `union` freeVars e
freeVars (U e) = freeVars e
freeVars (Kind _) = []

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Pi s t e) (Pi s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Mu i t) (Mu i' t') = alphaEq t (substVar i' i t')
alphaEq (F t e) (F t' e') = alphaEq t t' && alphaEq e e'
alphaEq (U t) (U t') = alphaEq t t'
alphaEq (Kind k) (Kind k') = k == k'
alphaEq _ _ = False

-- TODO: Generalize
desugar :: Expr -> Expr
desugar (Var n) = Var n
desugar (App e1 e2) = App (desugar e1) (desugar e2)
desugar (Lam n t e) = Lam n (desugar t) (desugar e)
desugar (Pi n t e) = Pi n (desugar t) (desugar e)
desugar (Mu n t) = Mu n (desugar t)
desugar (F t e) = F (desugar t) (desugar e)
desugar (U t) = U (desugar t)
desugar e@(Kind _) = e
desugar (Let n t e1 e2) = App (Lam n t (desugar e2)) (desugar e1)

type BEnv = [(Sym, Expr)]

-- whnf :: BEnv -> Expr -> Expr
-- whnf benv ee = spine ee []
--   where
--     spine (App f a) as = spine f (a : as)             -- (R-AppL)
--     spine (Lam s _ e) (a:as) = spine (subst s a e) as -- (R-AppLam)
--     spine (U (F _ e)) as = spine e as                 -- (R-Unfold-Fold)
--     spine (U e) as = spine (U (whnf benv e)) as       -- (R-unfold)
--     spine m@(Mu i e) as = spine (subst i m e) as      -- (R-Mu)
--     spine (Beta e) as = spine e as                    -- (R-Beta)
--     spine (Var n) as =                                -- fill in pre-defined terms
--       case lookup n benv of
--         Nothing -> foldl App (Var n) as
--         Just e  -> spine e as
--     spine f as = foldl App f as

reduct :: Expr -> Expr
reduct (App (Lam s _ e1) e2) = subst s e2 e1      -- (R-AppLAm)
reduct (App e1 e2) = App (reduct e1) e2     -- (R-AppL)
reduct (U (F _ e)) = e                            -- (R-Unfold-Fold)
reduct (U e) = U (reduct e)                 -- (R-unfold)
reduct m@(Mu x t) = subst x m t                   -- (R-Mu)

eval :: Expr -> Expr
eval = loop
  where
    loop e
      | isVal e = e
      | otherwise = loop (reduct e)

-- -- | Definitional equality because we use weak head normal form
-- equate :: BEnv -> Expr -> Expr -> Bool
-- equate benv e1 e2 =
--   let e1' = eval benv . desugar $ e1
--       e2' = eval benv . desugar $ e2
--   in case (e1',e2') of
--        (App a1 b1,App a2 b2) ->
--          equate benv a1 a2 &&
--          equate benv b1 b2
--        (Lam n _ a,Lam n1 _ a1) ->
--          equate benv a (substVar n1 n a1)
--        (Pi n _ a,Pi n1 _ a1) ->
--          equate benv a (substVar n1 n a1)
--        (Mu n t,Mu n1 t1) ->
--          equate benv t (substVar n1 n t1)
--        (F t a,F t1 a1) -> equate benv t t1 && equate benv a a1
--        (U t,U t1) -> equate benv t t1
--        (Beta t,Beta t1) -> equate benv t t1
--        (Var n1,Var n2) -> n1 == n2
--        (_,_) -> False
