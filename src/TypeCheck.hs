module TypeCheck where

import Control.Monad (unless, when)

import Syntax
import Expr

type Env = [(Sym, Type)]

extend :: Sym -> Type -> Env -> Env
extend s t r =(s,t):r

type ErrorMsg = String

type TC a = Either ErrorMsg a

findVar :: Env -> Sym -> TC Type
findVar r s =
  case lookup s r of
   Just t -> return t
   Nothing -> Left $ "Cannot find variable " ++ s

tcheck :: Env -> Expr -> TC Type
tcheck env (Var s) = findVar env s       -- (Var and Weak)
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
tcheck env (Mu i t e) =                -- (Mu)
  do let env' = extend i t env
     t' <- tcheck env' e
     tcheck env t' -- check sorts?
     unless (alphaEq t t') $ Left "Bad recursive type"
     return t
tcheck env (F t1 e) =                    -- (Fold)
  do t2 <- tcheck env e
     tcheck env t1 --check sorts?
     t2' <- reduct t1
     unless (alphaEq t2 t2') $ Left "Bad fold expression"
     return t1
tcheck env (U e) =                       -- (Unfold)
  do t1 <- tcheck env e
     t2 <- reduct t1
     tcheck env t2
     return t2

allowedKinds :: [(Type, Type)]
allowedKinds =
  [(Kind Star,Kind Star)
  ,(Kind Star,Kind Box)
  ,(Kind Box,Kind Star)
  ,(Kind Box,Kind Box)]

-- tcheckT :: Env -> Expr -> TC Type
-- tcheckT env e = liftM nf (tcheck env e)

-- typeCheck :: Expr -> Either String Type
-- typeCheck e =
--   case tcheck initalEnv e of
--     Left msg -> Left ("Type error:\n" ++ msg)
--     Right t -> Right t

arr :: Expr -> Expr -> Expr
arr = Pi ""
