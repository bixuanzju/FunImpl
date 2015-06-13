module Translation where

import Control.Monad (unless, when, mapAndUnzipM)
import Control.Monad.Except (throwError)
-- import Parser
-- import Debug.Trace

import Expr
import Syntax
import TypeCheck
import Utils

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
  (_, Pi _ t' _) <- trans env lt
  return (lt, Lam s t' e')
trans env (Pi x a b) = do
  (s, a') <- trans env a
  let env' = extend x a env
  (t, b') <- trans env' b
  when ((s,t) `notElem` allowedKinds) $ throwError "Bad abstraction"
  return (t, Pi x a' b')
trans env (Mu i t e) = do
  let env' = extend i t env
  (te, e') <- trans env' e
  unless (alphaEq t te) $ throwError "Bad recursive type"
  (_, t') <- trans env t
  return (t, Mu i t' e')
trans env (F t1 e) = do
  (t2, e') <- trans env e
  (_, t1') <- trans env t1
  t2' <- reduct t1
  unless (alphaEq t2 t2') $ throwError "Bad fold expression"
  return (t1, F t1' e')
trans env (U e) = do
  (t1, e') <- trans env e
  t2 <- reduct t1
  trans env t2
  return (t2, U e')

-- TODO: Lack 1) exhaustive test 2) overlap test
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
    transPattern dv tys (Alt (PConstr constr params) body) = do
      let k = constrName constr
      (kt, _) <- trans env (Var k)

      -- check patterns, quite hacky
      let tcApp = foldl App (Var "dummy$") (tys ++ map (Var . fst) params)
      (typ, _) <- trans (("dummy$", kt) : params ++ env) tcApp
      unless (alphaEq typ dv) $ throwError "Bad patterns"

      (bodyType, body') <- trans (params ++ env) body

      return (arr dv bodyType, genLambdas params body')

trans env (Data db@(DB tc tca constrs) e) = do
  env' <- tcdatatypes env db
  let nenv = env' ++ env
  (t, e') <- trans nenv e

  let tct = chainType (Kind Star) . map snd $ tca
  let du = foldl App (Var tc) (map (Var . fst) tca)
  let tcArgs = map constrParams constrs
  let tcArgChains = map (chainType (Var "B")) tcArgs
  let tcArgsAndSubst = map
                         (chainType (Var "B") . map
                                                  (\tau -> if tau == du
                                                             then Var "X"
                                                             else tau))
                         tcArgs
  let transTC = (tc, (tct, genLambdas tca
                             (Mu "X" (Kind Star)
                                (Pi "B" (Kind Star) (chainType (Var "B") tcArgsAndSubst)))))

  let tduList = map (chainType du . constrParams) constrs
  let dctList = map (\tdu -> foldr (\(u, k) tau -> Pi u k tau) tdu tca) tduList

  let transDC = zip (map constrName constrs)
                  (zip dctList
                     (map
                        (\(i, taus) ->
                           let xs = genVarsAndTypes 'x' taus
                               cs = genVarsAndTypes 'c' tcArgChains
                           in genLambdas tca
                                (genLambdas xs
                                   (F du
                                      (Lam "B" (Kind Star)
                                         (genLambdas cs
                                            (foldl App (Var ('c' : show i)) (map (Var . fst) xs)))))))
                        (zip [0 :: Int ..] tcArgs)))
  return (t, foldr (\(n, (kt, ke)) body -> Let n kt ke body) e' (transTC : transDC))

trans _ Nat = return (Kind Star, Nat)
trans _ n@(Lit _) = return (Nat, n)
trans env (Add e1 e2) = do
  (t1, e1') <- trans env e1
  (t2, e2') <- trans env e2
  unless (t1 == Nat && t2 == Nat) $ throwError "Addition is only allowed for numbers!"
  return (Nat, Add e1' e2')

trans _ _ = throwError "Trans: Impossible happened"

-- recordTest2 = let Right (Progm [e]) = parseExpr "rec monad (m : * -> *) = mo { return : pi a : * . m a, bind : pi a : *. pi b : *. m a -> (a -> m b) -> m b}; lam x : * . x"
--              in e

-- test = let Right (Progm [e]) = parseExpr "data Bool = True | False; data Nat = Zero | Suc Nat; \\ y : (\\ x : Bool . case x of True => Nat | False => Bool) True . unfold y"
--        in e


-- test2 = let Right (Progm [e]) = parseExpr "data Bool = True | False; data Nat = Zero | Suc Nat; data List (a : *) = Nil | Cons a (List a); Cons"
--        in e

-- tt :: Expr -> Expr
-- tt e = case trans [] e of
--   Left _ -> error "error"
--   Right (_, e') -> e'

-- test3 = let Right (Progm [e]) = parseExpr "data List (a : *) = Nil | Cons a (List a); Cons"
--         in e


-- test2 = let Right (Progm [e]) = parseExpr "data Bool = True | False; data Nat = Zero | Suc Nat; \\ y : ((\\ (x : Bool). (((unfold(x) ⋆) Nat) Bool))) True . unfold y"
--        in e
