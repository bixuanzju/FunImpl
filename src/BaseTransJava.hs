{-# LANGUAGE OverloadedStrings #-}

module BaseTransJava where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Text as T
import qualified Language.Java.Syntax as J
import           Unbound.Generics.LocallyNameless
import           Lens.Micro

import           JavaLang
import           StringPrefix
import           Syntax
import           TypeCheck

type TransJavaExp = Either J.Name J.Literal

type TransType = ([J.BlockStmt], TransJavaExp, Expr)

type Translate = C


compile :: Expr -> Either T.Text J.CompilationUnit
compile e = runLFreshM . runExceptT $ runReaderT (createWrap e) dummyCtx

createWrap :: Expr -> C J.CompilationUnit
createWrap e = do
  (bs, e, t) <- trans e
  let returnStmt = [bStmt $ J.Return $ Just (unwrap e)]
  let returnType = applyRetType t
  let javaCode = wrapperClass False "Test" (bs ++ returnStmt) returnType mainBody
  return (createCUB Nothing [javaCode])

applyRetType Nat = Just $ J.PrimType J.IntT
applyRetType _ = Just objClassTy

createCUB :: Maybe J.PackageDecl -> [J.TypeDecl] -> J.CompilationUnit
createCUB package compDef = cu
  where
    cu = J.CompilationUnit package [] compDef



-- | Translation to Java
trans :: Expr -> Translate TransType
trans e =
  case e of
    Var n -> do
      ctx <- ask
      t <- snd <$> (lookUp n (ctx ^. env))
      return ([], var (show n), t)
    Lam bnd -> do
      (s, je, t) <- translateScopeM bnd
      return (s, je, Pi t)
    _ -> throwError "Not implemented yet"


translateScopeM :: Bind Tele Expr -> Translate ([J.BlockStmt], TransJavaExp, Bind Tele Expr)
translateScopeM bnd =
  lunbind bnd $ \(delta@(Cons b), m) -> do
    (bodyBS, bodyV, bodyT) <- withReaderT (over env (`appTele` delta)) (trans m)
    closureBS <- translateScopeTyp delta (bodyBS, bodyV, bodyT)
    let x1 = (unrebind b) ^. _1 . _1
    x11 <- lfresh x1
    let fstmt = [localVar closureType (varDecl (show x11) (funInstCreate (show x1)))]
    return (closureBS ++ fstmt, var (show x11), bnd)


translateScopeTyp :: Tele -> TransType -> Translate ([J.BlockStmt])
translateScopeTyp (Cons bnd) body = do
  let (ostmts, oexpr, t1) = (body ^. _1, body ^. _2, body ^. _3)

  x11 <- lfresh x1

  let jt1 = javaType t1
  let flag = jt1 == objClassTy
  let accessField = fieldAccess (left $ var (show x11)) closureInput
  let xf = localFinalVar jt1
             (varDecl (localvarstr ++ show x1)
                (if flag
                   then accessField
                   else cast jt1 accessField))

  body' <- case b of
             Empty -> return ostmts
             Cons b' ->
               translateScopeTyp b body

  return
    ([ localClassDecl (closureTransName ++ show x1) closureClass
         (closureBodyGen [memberDecl $ fieldDecl (classTy closureClass) (varDecl (show x11) J.This)]
            ([xf] ++ body' ++ [bsAssign (name [closureOutput]) (unwrap oexpr)]))
     ])

  where
    ((x1, _, Embed t1), b) = unrebind bnd

javaType typ =
  case typ of
    Pi _ -> classTy closureClass
    Nat  -> classTy "java.lang.Integer"
    _    -> objClassTy
