{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module Environment (
    lookupTy,
    lookupCtx,
    extendCtx,
    flipPos,
    dummyCtx,
    runTcMonad,
    TcMonad,
    initialEnv,
    multiSubst
    ) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Lens.Micro
import           Lens.Micro.TH
import           Unbound.Generics.LocallyNameless

import           Syntax

data Context = Ctx {_env :: Tele, _tag :: ClassTag, _pos :: PosTag}

makeLenses ''Context

type TcMonad = FreshMT (ReaderT Context (Except T.Text))


runTcMonad :: Context -> TcMonad a -> (Either T.Text a)
runTcMonad env m = runExcept $ runReaderT (runFreshMT m) env


dummyCtx :: Context
dummyCtx = Ctx Empty Prog Pos

initialEnv :: ClassTag -> Context
initialEnv t = Ctx Empty t Pos

lookUpTele :: TmName -> Tele -> Maybe (Expr, ClassTag)
lookUpTele _ Empty = Nothing
lookUpTele v (Cons rb)
  | v == x = return (a, tag)
  | otherwise = lookUpTele v t'
  where
    ((x, Embed tag, Embed a), t') = unrebind rb

lookupTyMaybe :: (MonadReader Context m, MonadError T.Text m) => TmName -> m (Maybe (Expr, ClassTag))
lookupTyMaybe v = do
  tele <- asks _env
  return (lookUpTele v tele)

lookupTy :: (MonadReader Context m, MonadError T.Text m) => TmName -> m (Expr, ClassTag)
lookupTy v = do
  x <- lookupTyMaybe v
  case x of
    Nothing  -> throwError $ T.concat ["Not in scope: ", T.pack . show $ v]
    Just res -> return res

lookupCtx :: (MonadReader Context m) => m (ClassTag, PosTag)
lookupCtx = do
  ctx <- ask
  return (ctx ^. tag, ctx ^. pos)

extendCtx :: (MonadReader Context m) => Tele -> m a -> m a
extendCtx d = local (over env (`appTele` d))

flipPos :: (MonadReader Context m) => m a -> m a
flipPos = local (over pos flip)
  where
    flip Pos = Neg
    flip Neg = Pos


appTele :: Tele -> Tele -> Tele
appTele Empty t2 = t2
appTele (Cons rb) t2 = Cons (rebind p (appTele t1' t2))
  where
    (p, t1') = unrebind rb

multiSubst :: Tele -> Expr -> Expr -> (Tele, Expr)
multiSubst Empty _ e = (Empty, e)
multiSubst (Cons rb) t e = (b', e')
  where
    ((x, _, _), b) = unrebind rb
    e' = subst x t e
    b' = subst x t b
