module Expr where

import Data.List ((\\), union)
import Control.Monad.Except (throwError)
-- import Data.Maybe (fromMaybe)

import Syntax
import Utils
-- import Parser

-- | Substitution function
subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
  where sub e@(Var i) = if i == v then x else e
        sub (App f a) = App (sub f) (sub a)
        sub (Lam i t e) = abstr Lam i t e
        sub (Pi i t e) = abstr Pi i t e
        sub (Mu i t1 t2) = abstr Mu i t1 t2
        sub (F n t e) = F n (sub t) (sub e)
        sub (U n e) = U n (sub e)
        sub (Kind k) = Kind k
        -- surface language
        sub Error = Error
        sub Nat = Nat
        sub (Lit n) = Lit n
        sub (Add e1 e2) = Add (sub e1) (sub e2)
        sub (Case e alts) = Case (sub e) (map subAlt alts)
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
        subAlt :: Alt -> Alt
        subAlt (Alt p e) = Alt p (sub e)

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' = subst s (Var s')


-- | free variable set
freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])
freeVars (Pi i k t) = freeVars k `union` (freeVars t \\ [i])
freeVars (Mu i t1 t2) = freeVars t1 `union` (freeVars t2 \\ [i])
freeVars (F _ t e) = freeVars t `union` freeVars e
freeVars (U _ e) = freeVars e
freeVars (Kind _) = []
-- suface langage
freeVars (Case e _) = freeVars e
freeVars Nat = []
freeVars Error = []
freeVars (Lit _) = []
freeVars (Add e1 e2) = freeVars e1 `union` freeVars e2


-- | alpha equality
alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Pi s t e) (Pi s' t' e') = alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (Mu i t1 t2) (Mu i' t1' t2') = alphaEq t2 (substVar i' i t2') && alphaEq t1 t1'
alphaEq (F n t e) (F n' t' e') = n == n' && alphaEq t t' && alphaEq e e'
alphaEq (U n t) (U n' t') = alphaEq t t' && n == n'
alphaEq (Kind k) (Kind k') = k == k'
-- surface language
alphaEq Nat Nat = True
alphaEq (Lit n) (Lit m) = n == m
alphaEq (Add e1 e2) (Add e1' e2') = alphaEq e1 e1' && alphaEq e2 e2'
alphaEq Error _ = True
alphaEq _ Error = True
alphaEq _ _ = False

-- repFreeVar :: BEnv -> Expr -> Expr
-- repFreeVar env = repl
--   where
--     repl :: Expr -> Expr
--     repl (App f a) = App (repl f) (repl a)
--     repl (Lam n t e) = Lam n (repl t) (repl e)
--     repl (Pi n t e) = Pi n (repl t) (repl e)
--     repl (Mu n t1 t2) = Mu n (repl t1) (repl t2)
--     repl (F t e) = F (repl t) (repl e)
--     repl (U t) = U (repl t)
--     repl (Kind s) = Kind s
--     repl (Var n) = fromMaybe (Var n) (lookup n env)

-- TODO: Generalize
desugar :: Expr -> Expr
desugar (Var n) = Var n
desugar (App e1 e2) = App (desugar e1) (desugar e2)
desugar (Lam n t e) = Lam n (desugar t) (desugar e)
desugar (Pi n t e) = Pi n (desugar t) (desugar e)
desugar (Mu n t1 t2) = Mu n (desugar t1) (desugar t2)
desugar (F n t e) = F n (desugar t) (desugar e)
desugar (U n t) = U n (desugar t)
desugar e@(Kind _) = e
desugar (Let n _ e1 e2) = subst n (desugar e1) (desugar e2)
desugar (Letrec n t e1 e2) =
  let n' = n ++ "^"
  in desugar (Let n t (Mu n' t (desugar (substVar n n' e1))) (desugar e2))
desugar (Rec (RB n params field) e) =
  let selNames = map fst . selector $ field
      taus = map snd . selector $ field
      ru = foldl App (Var n) (map (Var . fst) params)
      selTypes = map (\t -> foldr (\(u, k) tau -> Pi u k tau) (Pi "" ru t) params) taus
      xs = genVarsAndTypes 'x' taus
      selExprs = zip selNames
                   (zip selTypes
                      (map
                         (\i ->
                            genLambdas params
                              (Lam "L" ru
                                 (Case (Var "L")
                                    [ Alt (PConstr (Constructor (recordName field) []) xs)
                                        (Var (map fst xs !! i))
                                    ])))
                         [0 :: Int .. length taus - 1]))
      lastExpr = Data (DB n params [Constructor (recordName field) taus])
                   (desugar (foldr (\(name, (kt, ke)) body -> Let name kt ke body) e selExprs))
  in lastExpr
desugar (Data bind e) = Data bind (desugar e)
desugar (Case e alts) = Case (desugar e) (map deAlt alts)
  where
    deAlt :: Alt -> Alt
    deAlt (Alt p body) = Alt p (desugar body)
desugar e = e


type BEnv = [(Sym, Expr)]


reduct :: Expr -> Either String Expr
reduct (App (Lam s _ e1) e2) = Right $ subst s e2 e1      -- (R-AppLAm)
reduct (App e1 e2) = reduct e1 >>= \e -> Right (App e e2) -- (R-AppL)
reduct (U _ (F _ _ e)) = Right e                              -- (R-Unfold-Fold)
reduct (U n e) = reduct e >>= Right . U n                     -- (R-unfold)
reduct m@(Mu x _ t2) = Right $ subst x m t2               -- (R-Mu)

-- surface language
reduct (Add (Lit n) (Lit m)) = Right (Lit (n + m))
reduct (Add (Lit n) m) = reduct m >>= \m' -> Right $ Add (Lit n) m'
reduct (Add n m) = reduct n >>= \n' -> Right (Add n' m)
reduct Nat = return Nat
reduct Error = throwError "Runtime error!"
reduct e = Left $ "Not reducible: " ++ show e


-- | multiple reduction
reductN :: Int -> Expr -> Either String Expr
reductN 0 e = return e
reductN n e = reduct e >>= \e' -> reductN (n-1) e'


-- | evaluator
eval :: Expr -> Either String Expr
eval = loop
  where
    loop e
      | isVal e = Right e
      | otherwise = case reduct e of
         Right e' -> loop e'
         Left err -> Left err

-- | Definitional equality
-- equate :: BEnv -> Expr -> Expr -> Bool
-- equate benv e1 e2 =
--   let Right e1' = eval . repFreeVar benv $ e1
--       Right e2' = eval . repFreeVar benv $ e2
--   in alphaEq e1' e2'
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
