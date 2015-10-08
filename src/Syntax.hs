{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, OverloadedStrings  #-}

module Syntax where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

type TmName = Name Expr

-- | Classifier
data ClassTag = Prog
              | Logic
  deriving (Eq, Show, Generic, Typeable)

-- | Positivity
data PosTag = Pos
            | Neg
  deriving (Eq, Show)

data Tele = Empty
          | Cons (Rebind (TmName, Embed ClassTag, Embed Expr) Tele)
  deriving (Show, Generic, Typeable)

-- | Datatype of the core, with optimization of aggregate bindings
data Expr = Var TmName
          | App Expr Expr
          | Lam (Bind Tele Expr)
          | Pi (Bind Tele Expr)
          | Mu (Bind (TmName, Embed Expr) Expr)
          | F Expr Expr
          | U Expr
          | Kind Kinds
          | Nat
          | Lit Int
          | PrimOp Operation Expr Expr
  deriving (Show, Generic, Typeable)

data Operation = Mult
               | Sub
               | Add
  deriving (Show, Generic, Typeable)

addExpr :: Expr -> Expr -> Expr
addExpr = PrimOp Add

subExpr :: Expr -> Expr -> Expr
subExpr = PrimOp Sub

multExpr :: Expr -> Expr -> Expr
multExpr = PrimOp Mult

data Kinds = Star
           | Box
  deriving (Show, Generic, Typeable)

instance Alpha ClassTag
instance Alpha Expr
instance Alpha Operation
instance Alpha Kinds
instance Alpha Tele

instance Subst Expr Operation
instance Subst Expr Kinds
instance Subst Expr Tele
instance Subst Expr ClassTag

instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing


-- Examples

-- \ x : ⋆ . \ y : x . y
polyid :: Expr
polyid = elam [("x", estar), ("y", evar "x")] (evar "y")


-- pi x : ⋆ . x -> x
polyidty :: Expr
polyidty = epi [("x", estar)] (earr (evar "x") (evar "x"))

-- castup [(\ x : * . x) int] 3
castupint :: Expr
castupint = F (eapp (elam [("x", estar)] (evar "x")) Nat) (Lit 3)


-- smart constructors

evar :: String -> Expr
evar = Var . string2Name

elam :: [(String, Expr)] -> Expr -> Expr
elam t b = Lam (bind (mkTele t) b)

emu :: (String, Expr) -> Expr -> Expr
emu (n, t) b = Mu (bind (string2Name n, embed t) b)

epi :: [(String, Expr)] -> Expr -> Expr
epi t b = Pi (bind (mkTele t) b)

earr :: Expr -> Expr -> Expr
earr t1 = epi [("_", t1)]

estar :: Expr
estar = Kind Star

ebox :: Expr
ebox = Kind Box

eapp :: Expr -> Expr -> Expr
eapp = App

mkTele :: [(String, Expr)] -> Tele
mkTele []          = Empty
mkTele ((x,e) : t) = Cons (rebind (string2Name x, Embed Logic, Embed e) (mkTele t))
