module Translation where

import Control.Monad (unless, when, mapAndUnzipM)
import Control.Monad.Except (throwError)
-- import Debug.Trace

import Syntax
import Expr
import TypeCheck

trans :: Env -> Expr -> TC (Type, Expr)
trans _ (Kind Star) = return (Kind Box, Kind Star)
trans env (Var s) = findVar env s >>= \t -> return (t, Var s)
trans env (App f a) = do
  (tf, f') <- trans env f
  case tf of
    Pi x at rt -> do
      (ta, a') <- trans env a
      unless (alphaEq ta at) $ throwError "Bad function argument type"
      return (subst x a rt, App f' a')
    _ -> throwError "Non-function in application"
trans env (Lam s t e) = do
  let env' = extend s t env
  (te, e') <- trans env' e
  let lt = Pi s t te
  tcheck env lt
  return (lt, Lam s t e')
trans env (Pi x a b) = do
  (s, a') <- trans env a
  let env' = extend x a env
  (t, b') <- trans env' b
  when ((s,t) `notElem` allowedKinds) $ throwError "Bad abstraction"
  return (t, Pi x a' b')
trans env (Mu i t e) = do
  let env' = extend i t env
  (t', e') <- trans env' e
  tcheck env t'
  unless (alphaEq t t') $ throwError "Bad recursive type"
  return (t, Mu i t e')
trans env (F t1 e) = do
  (t2, e') <- trans env e
  tcheck env t1
  t2' <- reduct t1
  unless (alphaEq t2 t2') $ throwError "Bad fold expression"
  return (t1, F t1 e')
trans env (U e) = do
  (t1, e') <- trans env e
  t2 <- reduct t1
  tcheck env t2
  return (t2, U e')
trans env (Case e alts) = do
  (dv, e') <- trans env e
  actualTypes <- fmap reverse (getActualTypes dv)

  (altTypeList, e2List) <- mapAndUnzipM (transPattern dv actualTypes) alts
  unless (all (== head altTypeList) (tail altTypeList)) $ throwError "Bad pattern expressions"

  let (Pi "" _ t) = head altTypeList
  let genExpr = foldl App (App (U e') t) e2List

  return (t, genExpr)

  where
    transPattern :: Type -> [Type] -> Alt -> TC (Type, Expr)
    transPattern dv tys (ConstrAlt (PConstr constr params) body) = do
      let k = constrName constr
      kt <- tcheck env (Var k)

      let tcApp = foldl App (Var "dummy$") (tys ++ map (Var . fst) params)
      typ <- tcheck (("dummy$", kt) : params ++ env) tcApp
      unless (alphaEq typ dv) $ throwError "Bad patterns"

      (bodyType, body') <- trans (params ++ env) body

      return (arr dv bodyType, genLambdas params body')

trans env (Data db@(DB tc tca constrs) e) = do
  env' <- tcdatatypes env db
  let nenv = env' ++ env
  (t, e') <- trans nenv e

  let tct = chainType (Kind Star) . map snd $ tca
  let du = foldl App (Var tc) (map (Var . fst) tca)
  let dcArgs = map constrParams constrs
  let dcArgChains = map (chainType (Var "B")) dcArgs
  let dcArgsAndSubst = map
                         (chainType (Var "B") . map
                                                  (\tau -> if tau == du
                                                             then Var "X"
                                                             else tau))
                         dcArgs
  let transD = (tc, (tct, genLambdas tca
                            (Mu "X" (Kind Star)
                               (Pi "B" (Kind Star) (chainType (Var "B") dcArgsAndSubst)))))

  let tduList = map (chainType du . constrParams) constrs
  let dctList = map (\tdu -> foldr (\(u, k) tau -> Pi u k tau) tdu tca) tduList

  let transKs = zip (map constrName constrs)
                  (zip dctList
                     (map
                        (\(i, taus) ->
                           let xs = genVars 'x' taus
                               cs = genVars 'c' dcArgChains
                           in genLambdas tca
                                (genLambdas xs
                                   (F du
                                      (Lam "B" (Kind Star)
                                         (genLambdas cs
                                            (foldl App (Var ('c' : show i)) (map (Var . fst) xs)))))))
                        (zip [0 :: Int ..] dcArgs)))
  return (t, foldr (\(n, (kt, ke)) body -> Let n kt ke body) e' (transD : transKs))

  where
    genVars :: Char -> [Type] -> [(Sym, Type)]
    genVars c ts = map (\(n, t) -> (c : show n, t)) (zip [0 :: Int ..] ts)


trans _ _ = throwError "Trans: Impossible happened"

genLambdas :: [(Sym, Type)] -> Expr -> Expr
genLambdas params body = foldr (\(x, t) l -> Lam x t l) body params


-- test = "data nat = zero | suc nat; data list (a : *) = nil | cons a (list a); (lam x : list nat . case x of nil => zero | cons (x : nat) (xs : list nat) => (suc x)) (cons nat zero (nil nat))"
