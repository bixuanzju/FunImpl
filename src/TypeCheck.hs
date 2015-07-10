module TypeCheck where

import Control.Monad (unless)
import Control.Monad.Except (throwError)
-- import Parser
-- import Debug.Trace

import Syntax
import Expr
import Utils

type Env = [(Sym, Type)]

extend :: Sym -> Type -> Env -> Env
extend s t r =(s,t):r

type ErrorMsg = String

type TC a = Either ErrorMsg a

findVar :: Env -> Sym -> TC Type
findVar r s =
  case lookup s r of
   Just t -> return t
   Nothing -> throwError $ "Cannot find variable " ++ s

-- | Type checker for the core language
tcheck :: Env -> Expr -> TC Type
tcheck _ (Kind Star) = return $ Kind Star -- (T_AX)
tcheck env (Var s) = findVar env s       -- (T_VAR and T_WEAK)
tcheck env (App f a) =                   -- (T_APP)
  do tf <- tcheck env f
     case tf of
       Pi x at rt ->
         do ta <- tcheck env a
            unless (alphaEq ta at) $     -- up to alpha equivalence
              throwError "Bad function argument type"
            return $ subst x a rt
       _ -> throwError "Non-function in application"
tcheck env (Lam s t e) =                 -- (T_LAM)
  do let env' = extend s t env
     te <- tcheck env' e
     let lt = Pi s t te  -- Note: cannot have datatype
     tcheck env lt
     return lt
tcheck env (Pi x a b) =                  -- (T_PI)
  do s <- tcheck env a -- evaluate after type check
     let env' = extend x a env
     t <- tcheck env' b
     unless (alphaEq t (Kind Star) && alphaEq s (Kind Star)) $ throwError "Bad abstraction"
     return t
tcheck env (Mu i t e) =                  -- (T_MU)
  do let env' = extend i t env
     t' <- tcheck env' e
     tcheck env t'
     unless (alphaEq t t') $ throwError "Bad recursive type"
     return t
tcheck env (F n t1 e) =                    -- (T_CASTUP)
  do t2 <- tcheck env e
     tcheck env t1
     t2' <- reductN n t1
     unless (alphaEq t2 t2') $ throwError "Bad fold expression"
     return t1
tcheck env (U n e) =                       -- (T_CASTDOWN)
  do t1 <- tcheck env e
     t2 <- reductN n t1
     tcheck env t2
     return t2

tcheck _ Nat = return (Kind Star)
tcheck _ (Lit _) = return Nat
tcheck env (Add e1 e2) = do
  t1 <- tcheck env e1
  t2 <- tcheck env e2
  unless (t1 == Nat && t2 == Nat) $ throwError "Addition is only allowed for numbers!"
  return Nat

tcheck _ Error = return Error

tcheck _ e = throwError $ "TypeCheck: Impossible happened, trying to type check:\n" ++ show e

getActualTypes :: Type -> TC [Type]
getActualTypes (App a b) = getActualTypes a >>= \ts -> return (b : ts)
getActualTypes (Var _) = return []
getActualTypes _ = throwError "Bad scrutinee type"

-- allowedKinds :: [(Type, Type)]
-- allowedKinds =
--   [(Kind Star,Kind Star)
--   ,(Kind Star,Kind Box)
--   ,(Kind Box,Kind Star)
--   ,(Kind Box,Kind Box)]

arr :: Type -> Type -> Type
arr = Pi ""
