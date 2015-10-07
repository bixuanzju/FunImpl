{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module TypeCheck where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Lens.Micro
import           Lens.Micro.TH
import           Unbound.Generics.LocallyNameless

import           PrettyPrint
import           Syntax

data Context = Ctx {_env :: Tele, _tag :: ClassTag, _pos :: PosTag}

makeLenses ''Context

type C = ReaderT Context (ExceptT T.Text LFreshM)

done :: MonadPlus m => m a
done = mzero

-- | Small step, call-by-value operational semantics
step :: Expr -> C Expr
step (Var{}) = done
step (Kind{}) = done
step (Lam{}) = done
step (Pi{}) = done
step (F{}) = done
step (Lit{}) = done
step (Nat) = done
step (App (Lam bnd) t2) =
  lunbind bnd $ \(delta, b) -> do
    (b', e') <- multiSubst delta t2 b
    case b' of
      Empty -> return e'
      _     -> return (Lam (bind b' e'))
step (App t1 t2) =
  App <$> step t1 <*> pure t2
  <|> App <$> pure t1 <*> step t2
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
tc :: (a -> C a) -> (a -> LFreshM a)
tc f a = do
  ma' <- runExceptT $ runReaderT (f a) dummyCtx
  case ma' of
    Left err -> return a
    Right a' -> tc f a'

dummyCtx = Ctx Empty Prog Pos

eval :: Expr -> Expr
eval x = runLFreshM (tc step x)

-- | type checker with positivity and contractiveness test
typecheck :: ClassTag -> Expr -> Either T.Text Expr
typecheck tag e = runLFreshM . runExceptT $ runReaderT (infer e) (Ctx Empty tag Pos)

infer :: Expr -> C Expr
infer (Var x) = do
  ctx <- ask
  (theta, t) <- (lookUp x (ctx ^. env))
  when ((ctx ^. tag, theta, ctx ^. pos) == (Logic, Prog, Neg)) $
    throwError $ T.concat
                   [ "Recursive variable "
                   , T.pack . show $ x
                   , " should not appear in a negative position"
                   ]
  return t
infer (Kind Star) = return (Kind Box)
infer (Lam bnd) =
  lunbind bnd $ \(delta, m) -> do
    b <- withReaderT (over env (`appTele` delta)) (infer m)
    return . Pi $ bind delta b -- TODO: check validity of pi type
infer (App m n) = do
  bnd <- unPi =<< infer m
  lunbind bnd $ \(delta, b) -> do
    checkArg n delta
    (delta', b') <- multiSubst delta n b
    case delta' of
      Empty -> return b'
      _     -> return (Pi (bind delta' b'))
infer e@(Pi bnd) =
  lunbind bnd $ \(delta, b) -> do
    checkDelta delta
    t <- withReaderT (over env (`appTele` delta)) (infer b)
    unless (aeq t estar || aeq t ebox) $
      throwError $ T.concat [showExpr b, " should have sort ⋆ or □"]
    return t
infer a@(Mu bnd) =
  lunbind bnd $ \((x, Embed t), e) -> do
    withReaderT (over env (`appTele` (Cons (rebind (x, Embed Prog, Embed t) Empty)))) (check e t)
    checkSort t
    ctaTest e x
    return t
infer (F t1 e) = do
  t2 <- step t1
  t2' <- infer e
  checkEq t2 t2'
  check t1 estar
  return t1
infer (U e) = do
  t1 <- infer e
  t2 <- step t1
  check t2 estar
  return t2
infer Nat = return estar
infer (Lit{}) = return Nat
infer (PrimOp{}) = return Nat
infer e = throwError $ T.concat ["Type checking ", showExpr e, " falied"]


-- helper functions

check :: Expr -> Expr -> C ()
check m a = do
  b <- infer m
  checkEq b a

checkArg :: Expr -> Tele -> C ()
checkArg _ Empty = return ()
checkArg e (Cons rb) = do
  let ((x, _, Embed a), t') = unrebind rb
  check e a

checkDelta :: Tele -> C ()
checkDelta Empty = return ()
checkDelta (Cons bnd) = do
  withReaderT (over pos flipp) (checkSort t)
  withReaderT (over env (`appTele` mkTele [(name2String x, t)])) (checkDelta t')

  where
    ((x, _, Embed t), t') = unrebind bnd

flipp :: PosTag -> PosTag
flipp Pos = Neg
flipp Neg = Pos

checkSort :: Expr -> C ()
checkSort e = do
  t <- infer e
  unless (aeq t estar || aeq t ebox) $
    throwError $ T.concat [showExpr e, " should have sort ⋆ or □"]
  return ()

unPi :: Expr -> C (Bind Tele Expr)
unPi (Pi bnd) = return bnd
unPi e = throwError $ T.concat ["Expected pi type, got ", showExpr e, " instead"]

-- | alpha equality
checkEq :: Expr -> Expr -> C ()
checkEq e1 e2 =
  if aeq e1 e2
    then return ()
    else throwError $ T.concat ["Couldn't match: ", showExpr e1, " with ", showExpr e2]

multiSubst :: Tele -> Expr -> Expr -> C (Tele, Expr)
multiSubst Empty _ e = return (Empty, e)
multiSubst (Cons rb) t e = return (b', e')
  where
    ((x, _, _), b) = unrebind rb
    e' = subst x t e
    b' = subst x t b

appTele :: Tele -> Tele -> Tele
appTele Empty t2 = t2
appTele (Cons rb) t2 = Cons (rebind p (appTele t1' t2))
  where
    (p, t1') = unrebind rb


lookUp :: TmName -> Tele -> C (ClassTag, Expr)
lookUp n Empty = throwError $ T.concat ["Not in scope: " , T.pack . show $ n]
lookUp v (Cons rb)
  | v == x = return (tag, a)
  | otherwise = lookUp v t'
  where
    ((x, Embed tag, Embed a), t') = unrebind rb

-- | Contractiveness test
ctaTest :: Expr -> TmName -> C ()
ctaTest e x = do
  t <- (^. tag ) <$> ask
  case t of
    Prog  -> return ()
    Logic -> cta e

  where
    cta :: Expr -> C ()
    cta (Kind{}) = return ()
    cta (Var n)
      | n == x = throwError $ T.concat ["Contractiveness test failed: ", T.pack . show $ n]
      | otherwise = return ()
    cta (Pi{}) = return ()
    cta (App e1 e2) = mapM_ cta (e1 : [e2])
    cta (Lam bnd) = lunbind bnd $ cta . snd
    cta (F _ e) = cta e
    cta (U e) = cta e
    cta (Mu bnd) = lunbind bnd $ cta . snd
    cta Nat = return ()
    cta (Lit{}) = return ()
    cta (PrimOp _ e1 e2) = cta e1 >> cta e2
