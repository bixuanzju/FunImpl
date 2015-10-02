{-# LANGUAGE OverloadedStrings #-}

module TypeCheck (eval, typecheck) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless

import           PrettyPrint
import           Syntax

type Context = ExceptT T.Text

type M = Context LFreshM

type Env = Tele

done :: MonadPlus m => m a
done = mzero

-- | Small step, call-by-value operational semantics
step :: Expr -> M Expr
step (Var{}) = done
step (Kind{}) = done
step (Lam{}) = done
step (Pi{}) = done
step (F{}) = done
step (Lit{}) = done
step (Nat) = done
step (App (Lam bnd) t2) =
  lunbind bnd $ \(delta, b) -> multiSubst delta t2 b
step (App t1 t2) =
  App <$> step t1 <*> pure t2
  <|> App <$> pure t1 <*> mapM step t2
step (U (F _ e)) = return e
step (U e) = U <$> step e
step e@(Mu bnd) =
  lunbind bnd $ \((n, _), b) -> return $ subst n b e
step (PrimOp op (Lit n) (Lit m)) = do
  let x = evalOp op
  return (Lit (n `x` m))
step (PrimOp op e1 e2) =
  PrimOp <$> pure op <*> step e1 <*> pure e2
  <|> PrimOp <$> pure op <*> pure e1 <*> step e2

evalOp :: Operation -> (Int -> Int -> Int)
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mult = (*)

-- | transitive closure of `step`
tc :: (Monad m, Functor m) => (a -> Context m a) -> (a -> m a)
tc f a = do
  ma' <- runExceptT (f a)
  case ma' of
    Left err -> return a
    Right a' -> tc f a'

eval :: Expr -> Expr
eval x = runLFreshM (tc step x)

-- type checker

infer :: Env -> Expr -> M Expr
infer g (Var x) = lookUp x g
infer _ (Kind Star) = return (Kind Box)
infer g (Lam bnd) =
  lunbind bnd $ \(delta, m) -> do
    b <- infer (g `appTele` delta) m
    return . Pi $ bind delta b -- TODO: check validity of pi type
infer g (App m ns) = do
  bnd <- unPi =<< infer g m
  lunbind bnd $ \(delta, b) -> do
    checkList g ns delta
    multiSubst delta ns b
infer g e@(Pi bnd) =
  lunbind bnd $ \(delta, b) -> do
    t <- infer (g `appTele` delta) b
    unless (aeq b estar || aeq b ebox) $
      throwError $ T.concat ["In ", showExpr e, ", ", showExpr b, " should have sort ⋆ or □"]
    return t
infer g a@(Mu bnd) =
  lunbind bnd $ \((x, Embed t), e) -> do
    check (g `appTele` (mkTele [(name2String x, t)])) e t
    unless (aeq t estar || aeq t ebox) $
      throwError $ T.concat ["In ", showExpr a, ", ", showExpr t, " should have sort ⋆ or □"]
    return t
infer g (F t1 e) = do
  t2 <- step t1
  t2' <- infer g e
  checkEq t2 t2'
  check g t1 estar
  return t1
infer g (U e) = do
  t1 <- infer g e
  t2 <- step t1
  check g t2 estar
  return t2
infer _ Nat = return estar
infer _ (Lit{}) = return Nat
infer _ (PrimOp{}) = return Nat

infer _ e = throwError $ T.concat ["Type checking ", showExpr e, " falied"]

typecheck :: Expr -> Either T.Text Expr
typecheck = runLFreshM . runExceptT . (infer Empty)


-- helper functions

checkList :: Env -> [Expr] -> Tele -> M ()
checkList _ [] Empty = return ()
checkList g (e:es) (Cons rb) = do
  let ((x, Embed a), t') = unrebind rb
  check g e a
  checkList (subst x e g) (subst x e es) (subst x e t') -- FIXME: overkill?
checkList _ _ _ = throwError $ "Unequal number of parameters and arguments"

check :: Env -> Expr -> Expr -> M ()
check g m a = do
  b <- infer g m
  checkEq b a

unPi :: Expr -> M (Bind Tele Expr)
unPi (Pi bnd) = return bnd
unPi e = throwError $ T.concat ["Expected pi type, got ", showExpr e, " instead"]

-- | alpha equality
checkEq :: Expr -> Expr -> M ()
checkEq e1 e2 =
  if aeq e1 e2
    then return ()
    else throwError $ T.concat ["Couldn't match: ", showExpr e1, " with ", showExpr e2]

multiSubst :: Tele -> [Expr] -> Expr -> M Expr
multiSubst Empty [] e = return e
multiSubst (Cons rb) (e1:es) e = multiSubst t' es e'
  where
    ((x, _), t') = unrebind rb
    e' = subst x e1 e
multiSubst _ _ _ = throwError "Unequal number of parameters and arguments"

appTele :: Tele -> Tele -> Tele
appTele Empty t2 = t2
appTele (Cons rb) t2 = Cons (rebind p (appTele t1' t2))
  where
    (p, t1') = unrebind rb


lookUp :: TmName -> Tele -> M Expr
lookUp n Empty = throwError $ T.concat ["Not in scope: " , T.pack . show $ n]
lookUp v (Cons rb)
  | v == x = return a
  | otherwise = lookUp v t'
  where
    ((x, Embed a), t') = unrebind rb
