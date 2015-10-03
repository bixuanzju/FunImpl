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

-- TODO: move those tags to state monad

-- | type checker with positivity and contractiveness test
typecheck :: ClassTag -> Expr -> Either T.Text Expr
typecheck tag = runLFreshM . runExceptT . (infer tag Empty Pos)

infer :: ClassTag -> Env -> PosTag -> Expr -> M Expr
infer tag g p (Var x) = do
  (theta, t) <- (lookUp x g)
  when ((tag, theta, p) == (Logic, Prog, Neg)) $
    throwError $ T.concat
                   [ "Recursive variable "
                   , T.pack . show $ x
                   , " should not appear in the negative position"
                   ]
  return t
infer _ _ _ (Kind Star) = return (Kind Box)
infer tag g p (Lam bnd) =
  lunbind bnd $ \(delta, m) -> do
    b <- infer tag (g `appTele` delta) p m
    return . Pi $ bind delta b -- TODO: check validity of pi type
infer tag g p (App m ns) = do
  bnd <- unPi =<< infer tag g p m
  lunbind bnd $ \(delta, b) -> do
    checkList tag g p ns delta
    multiSubst delta ns b
infer tag g p e@(Pi bnd) =
  lunbind bnd $ \(delta, b) -> do
    checkDelta tag g p delta
    t <- infer tag (g `appTele` delta) p b
    unless (aeq t estar || aeq t ebox) $
      throwError $ T.concat [showExpr b, " should have sort ⋆ or □"]
    return t
infer tag g p a@(Mu bnd) =
  lunbind bnd $ \((x, Embed t), e) -> do
    check tag (g `appTele` (Cons (rebind (x, Embed Prog, Embed t) Empty))) p e t
    checkSort tag g p t
    ctaTest tag e x
    return t
infer tag g p (F t1 e) = do
  t2 <- step t1
  t2' <- infer tag g p e
  checkEq t2 t2'
  check tag g p t1 estar
  return t1
infer tag g p (U e) = do
  t1 <- infer tag g p e
  t2 <- step t1
  check tag g p t2 estar
  return t2
infer _ _ _ Nat = return estar
infer _ _ _ (Lit{}) = return Nat
infer _ _ _ (PrimOp{}) = return Nat
infer _ _ _ e = throwError $ T.concat ["Type checking ", showExpr e, " falied"]


-- helper functions

check :: ClassTag -> Env -> PosTag -> Expr -> Expr -> M ()
check tag g p m a = do
  b <- infer tag g p m
  checkEq b a

checkList :: ClassTag -> Env -> PosTag -> [Expr] -> Tele -> M ()
checkList _ _ _ [] Empty = return ()
checkList tag g p (e:es) (Cons rb) = do
  let ((x, _, Embed a), t') = unrebind rb
  check tag g p e a
  checkList tag (subst x e g) p (subst x e es) (subst x e t') -- FIXME: overkill?
checkList _ _ _ _ _ = throwError $ "Unequal number of parameters and arguments"

checkDelta :: ClassTag -> Env -> PosTag -> Tele -> M ()
checkDelta _ _ _ Empty = return ()
checkDelta tag g p (Cons bnd) = do
  checkSort tag g (flipp p) t
  checkDelta tag (g `appTele` mkTele [(name2String x, t)]) p t'

  where
    ((x, _, Embed t), t') = unrebind bnd

flipp :: PosTag -> PosTag
flipp Pos = Neg
flipp Neg = Pos

checkSort :: ClassTag -> Env -> PosTag -> Expr -> M ()
checkSort tag g p e = do
  t <- infer tag g p e
  unless (aeq t estar || aeq t ebox) $
    throwError $ T.concat [showExpr e, " should have sort ⋆ or □"]
  return ()

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
    ((x, _, _), t') = unrebind rb
    e' = subst x e1 e
multiSubst _ _ _ = throwError "Unequal number of parameters and arguments"

appTele :: Tele -> Tele -> Tele
appTele Empty t2 = t2
appTele (Cons rb) t2 = Cons (rebind p (appTele t1' t2))
  where
    (p, t1') = unrebind rb


lookUp :: TmName -> Tele -> M (ClassTag, Expr)
lookUp n Empty = throwError $ T.concat ["Not in scope: " , T.pack . show $ n]
lookUp v (Cons rb)
  | v == x = return (tag, a)
  | otherwise = lookUp v t'
  where
    ((x, Embed tag, Embed a), t') = unrebind rb

ctaTest :: ClassTag -> Expr -> TmName -> M ()
ctaTest Prog _ _ = return ()
ctaTest Logic e x = cta e
  where
    cta :: Expr -> M ()
    cta (Kind{}) = return ()
    cta (Var n) =
      if n == x
        then throwError $ T.concat ["Contractiveness test failed: ", T.pack . show $ n]
        else return ()
    cta (Pi{}) = return ()
    cta (App e1 e2) = mapM_ cta (e1 : e2)
    cta (Lam bnd) = lunbind bnd $ \(_, e) -> cta e
    cta (F _ e) = cta e
    cta (U e) = cta e
    cta (Mu bnd) = lunbind bnd $ \(_, e) -> cta e
    cta Nat = return ()
    cta (Lit{}) = return ()
    cta (PrimOp _ e1 e2) = cta e1 >> cta e2
