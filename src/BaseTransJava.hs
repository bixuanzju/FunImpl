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

    (closureBS, x11) <- translateScopeTyp delta (bodyBS, bodyV, bodyT)

    return (closureBS, x11, bnd)


translateScopeTyp :: Tele -> TransType -> Translate ([J.BlockStmt], TransJavaExp)
translateScopeTyp b (ostmts, oexpr, t1) = translateScopeTyp' b
  where
    translateScopeTyp' (Cons bnd) = do
      let ((x1, _, Embed t1), b) = unrebind bnd

      let jt1 = javaType t1
      let cvar = "c" ++ show x1  -- FIXME: add prefix
      let accessField = fieldAccess (left $ var cvar) closureInput
      let xf = localFinalVar jt1
                 (varDecl (show x1)
                    (if jt1 == objClassTy
                       then accessField
                       else cast jt1 accessField))

      (body', xe) <- case b of
                       Empty -> return (ostmts, oexpr)
                       Cons b' ->
                         translateScopeTyp' b

      let fstmt = localVar closureType (varDecl cvar (funInstCreate (show x1)))

      return
        ([ localClassDecl (closureTransName ++ show x1) closureClass
             (closureBodyGen [memberDecl $ fieldDecl (classTy closureClass) (varDecl cvar J.This)]
                ([xf] ++ body' ++ [bsAssign (name [closureOutput]) (unwrap xe)]))
         , fstmt
         ], var cvar)



javaType typ =
  case typ of
    Pi _ -> classTy closureClass
    Nat  -> classTy "java.lang.Integer"
    _    -> objClassTy
