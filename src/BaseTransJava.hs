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
      t <- snd <$> lookUp n (ctx ^. env)
      return ([], var (show n), t)
    Lam bnd -> do
      (s, je, t) <- translateScopeM bnd
      return (s, je, Pi t)
    App e1 e2 -> transApply e1 e2
    Lit lit -> return ([], Right . J.Int . fromIntegral $ lit, Nat)
    PrimOp op e1 e2 -> do
      (s1, j1, _) <- trans e1
      (s2, j2, _) <- trans e2
      let j1' = unwrap j1
      let j2' = unwrap j2
      let (je, t) =
            case op of
              Add  -> (J.BinOp j1' J.Add j2', Nat)
              Mult -> (J.BinOp j1' J.Mult j2', Nat)
              Sub  -> (J.BinOp j1' J.Sub j2', Nat)
      newName <- lfresh (string2Name "prim" :: TmName)
      let assignExpr = localFinalVar (javaType t) (varDecl (show newName) je)
      return (s1 ++ s2 ++ [assignExpr], var (show newName), t)
    _ -> throwError "Not implemented yet"


transApply :: Expr -> Expr -> Translate TransType
transApply e1 e2 = do
  (s1, j1, Pi bnd) <- trans e1
  lunbind bnd $ \(d@(Cons de), b) -> do
    let ((x1, _, Embed t1), de') = unrebind de
    (s2, j2, _) <- trans e2
    (d', b') <- multiSubst d e2 b
    let retTy =
          case d' of
            Empty -> b'
            _     -> Pi (bind d' b)

    let fexp = unwrap j1
    let fs = assignField (fieldAccExp fexp closureInput) (unwrap j2)
    let fapply = bStmt . applyMethodCall $ fexp
    let fout = fieldAccess fexp closureOutput
    fret <- show <$> lfresh x1
    let fres = [initClass (javaType retTy) fret fout]

    return (s1 ++ s2 ++ (fs : fapply : fres), var fret, retTy)



translateScopeM :: Bind Tele Expr -> Translate ([J.BlockStmt], TransJavaExp, Bind Tele Expr)
translateScopeM bnd =
  lunbind bnd $ \(delta@(Cons b), m) -> do
    (bodyBS, bodyV, bodyT) <- withReaderT (over env (`appTele` delta)) (trans m)

    (closureBS, x11) <- translateScopeTy delta (bodyBS, bodyV, bodyT)

    return (closureBS, x11, bind delta bodyT)

{-

\(x1 : t1)(..) . e

==>

class Fx1 extends Closure {

  Closure cx1 = this;

  public void apply() {
    |t1| x1 = cx1.arg;
    <...>
  }
}
Closure cx1 = new Fx1();

-}
translateScopeTy :: Tele -> TransType -> Translate ([J.BlockStmt], TransJavaExp)
translateScopeTy b (ostmts, oexpr, t1) = translateScopeTyp' b
  where
    translateScopeTyp' (Cons bnd) = do
      let ((x1, _, Embed t1), b) = unrebind bnd

      let cvar = "c" ++ show x1  -- FIXME: add prefix
      let accessField = fieldAccess (left $ var cvar) closureInput
      let xf = initClass (javaType t1) (show x1) accessField

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



javaType ty =
  case ty of
    Pi _ -> classTy closureClass
    Nat  -> classTy "java.lang.Integer"
    _    -> objClassTy

initClass :: J.Type -> String -> J.Exp -> J.BlockStmt
initClass ty tempName expr =
  localFinalVar ty
    (varDecl tempName
       (if ty == objClassTy
          then expr
          else cast ty expr))
