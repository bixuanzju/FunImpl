module TypeCheck where

import Control.Monad (unless)
import Control.Monad.Except (throwError)
import Control.Applicative ((<|>))
-- import Parser
-- import Debug.Trace

import Syntax
import Expr
import Utils

type EnvIndex = (Sym, ClassTag)

type Env = [(EnvIndex, Type)]

extend :: EnvIndex -> Type -> Env -> Env
extend s t r = (s,t):r

type ErrorMsg = String

type TC a = Either ErrorMsg a

-- Classifier
data ClassTag = Prog
              | Logic
              deriving (Eq, Show)

-- Positivity
data PosTag = Pos
            | Neg
            deriving (Eq, Show)

flipp :: PosTag -> PosTag
flipp Pos = Neg
flipp Neg = Pos

-- New Expr
data Expr' = Expr' ClassTag PosTag Expr deriving Eq

findVar :: Env -> EnvIndex -> TC Type
findVar r s =
  case lookup s r of
   Just t -> return t
   Nothing -> throwError $ "Cannot find variable " ++ show s


tpcheck :: Env -> Expr' -> TC Type
tpcheck env = go
  where
    go (Expr' ctag ptag e) =
      let
        sameTags e = Expr' ctag ptag e
        cta Prog _ _ = True
        cta Logic x e = ctal e 
          where
            ctal (Kind _) = True
            ctal (Var y) = (y /= x)
            ctal (Pi _ _ _) = True
            ctal (App f a) = (ctal f) && (ctal a)
            ctal (Lam y _ e) = if y == x then True else ctal e
            ctal (F _ _ e) = ctal e
            ctal (U _ e) = ctal e
            ctal (Mu y _ e) = if y == x then True else ctal e
      in
      case e of
        -- T_AX
        (Kind Star) -> return (Kind Box)
        -- T_VARL & T_VARP
        (Var s) ->
          case (ctag, ptag) of
            (Logic, Neg) -> findVar env (s, Logic)
            _ -> (findVar env (s, Prog)) <|> (findVar env (s, Logic))
        -- T_APP
        (App f a) ->
          do tf <- tpcheck env (sameTags f)
             case tf of
               (Pi x t2 t1) ->
                 do ta <- tpcheck env (sameTags a)
                    unless (alphaEq ta t2) $ throwError "Incorrect argument type"
                    return $ subst x a t1 
               _ -> throwError "Non-function in application"
        -- T_LAM
        (Lam x t1 e) ->
          do let env' = extend (x, Logic) t1 env
             t2 <- tpcheck env' (sameTags e)
             let lt = Pi x t1 t2
             tpcheck env (sameTags lt)
             return lt
        -- T_PI
        (Pi x t1 t2) ->
          do s <- tpcheck env (Expr' ctag (flipp ptag) t1)
             let env' = extend (x, Logic) t1 env
             t <- tpcheck env' (sameTags t2)
             return t
        -- T_MU
        (Mu x t e) ->
          do let env' = extend (x, Prog) t env
             t' <- tpcheck env' (sameTags e)
             tpcheck env (sameTags t')
             unless (cta ctag x e) $ throwError "CTA wrong"
             return t'
        -- T_CASTUP
        (F n t1 e) ->
          do t2 <- tpcheck env (sameTags e)
             kt1 <- tpcheck env (sameTags t1)
             unless (alphaEq kt1 (Kind Star)) $ throwError "Kind of t1 is not star in castup"
             t2' <- reductN n t1
             unless (alphaEq t2 t2') $ throwError "Cannot derive t2 from t1 in castup"
             return t1
        -- T_CASTDOWN
        (U n e) ->
          do t1 <- tpcheck env (sameTags e)
             t2 <- reductN n t1
             kt2 <- tpcheck env (sameTags t2)
             unless (alphaEq kt2 (Kind Star)) $ throwError "Kind of t2 is not star in castdown"
             return t2
        -- Others
        Nat -> return (Kind Star)

        (Lit _) -> return Nat
        --
        (Add e1 e2) ->
          do t1 <- tpcheck env (sameTags e1)
             t2 <- tpcheck env (sameTags e2)
             unless (t1 == Nat && t2 == Nat) $ throwError "Addition is only allowed for numbers!"
             return Nat
        
        e -> throwError $ "TypeCheck: Impossible happened, trying to type check:\n" ++ show e


-- | Type checker for the core language
{-
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

-}

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
