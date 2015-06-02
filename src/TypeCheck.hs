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
tcheck env (Var s) = findVar env s       -- (T_VAR and T_WEAK)
tcheck env (App f a) =                   -- (T_APP)
  do tf <- tcheck env f
     case tf of
       Pi x at rt ->
         do ta <- tcheck env a
            unless (alphaEq ta at) $     -- up to alpha equivalence
              Left "Bad function argument type"
            return $ subst x a rt
       _ -> Left "Non-function in application"
tcheck env (Lam s t e) =                 -- (T_LAM)
  do let env' = extend s t env
     te <- tcheck env' e
     let lt = Pi s t te
     tcheck env lt
     return lt
tcheck _ (Kind Star) = return $ Kind Box -- (T_AX)
tcheck _ (Kind Box) = Left "Found a Box"
tcheck env (Pi x a b) =                  -- (T_PI)
  do s <- tcheck env a -- evaluate after type check
     let env' = extend x a env
     t <- tcheck env' b
     when ((s,t) `notElem` allowedKinds) $ Left "Bad abstraction"
     return t
tcheck env (Mu i t e) =                  -- (T_MU)
  do let env' = extend i t env
     t' <- tcheck env' e
     tcheck env t'
     unless (alphaEq t t') $ Left "Bad recursive type"
     return t
tcheck env (F t1 e) =                    -- (T_CASTUP)
  do t2 <- tcheck env e
     tcheck env t1
     t2' <- reduct t1
     unless (alphaEq t2 t2') $ Left "Bad fold expression"
     return t1
tcheck env (U e) =                       -- (T_CASTDOWN)
  do t1 <- tcheck env e
     t2 <- reduct t1
     tcheck env t2
     return t2
tcheck env (Data databinds e) = do
  env' <- tcd databinds
  let nenv = env' ++ env
  tcheck nenv e
  where
    tcd :: DataBind -> TC Env
    tcd (DB tc tca constrs) = do
      let tct = chainType (Kind Star) . map snd $ tca
      tcs <- tcheck env tct
      unless (tcs == (Kind Box)) $ Left "Bad type constructor arguments"
      let du = foldl App (Var tc) (map (Var . fst) tca)
      let tduList = map (\dc -> chainType du (constrParams dc)) constrs
      dcts <- mapM (tcheck ((tc, tct) : tca ++ env)) tduList
      unless (any (== (Kind Star)) dcts) $ Left "Bad data constructor arguments"
      let dctList = map (\tdu -> foldr (\(u, k) t -> Pi u k t) tdu tca) tduList
      return ([(tc, tct)] ++ (zip (map constrName constrs) dctList))

chainType :: Type -> [Type] -> Type
chainType lt = foldr (\t t' -> Pi "" t t') lt

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
