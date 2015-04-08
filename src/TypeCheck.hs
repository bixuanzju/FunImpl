module TypeCheck where

import Control.Monad (unless, when)

import Syntax
import Expr

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
