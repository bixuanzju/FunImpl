module Syntax where

type Sym = String


data Program = Progm [Expr] deriving Show

data Expr = Var Sym
          | App Expr Expr
          | Lam Sym Type Expr
          | Pi Sym Type Type
          | Mu Sym Type
          | F Type Expr
          | U Expr
          | Kind Kinds
          | Let Sym Type Expr Expr -- | Syntax sugar
          deriving (Eq, Read)

isVal :: Expr -> Bool
isVal (Lam _ _ _) = True
isVal (Pi _ _ _) = True
isVal (F _ _) = True
isVal _ = False

type Type = Expr

data Kinds = Star | Box deriving (Eq, Read)

instance Show Kinds where
  show Star = "⋆"
  show Box = "□"

instance Show Expr where
  show = showExp True

showExp :: Bool -> Expr -> String
showExp _ (Var n) = n
showExp flag (App e1 e2) =
  if flag
    then result
    else paren result
  where
    result = showExp False e1 ++ " " ++ showExp False e2
showExp flag (Lam n t e) =
  if flag
    then result
    else paren result
  where
    result = "λ(" ++ n ++ " : " ++ showExp True t ++ ") . " ++ showExp True e
showExp _ (Pi n t e) =
  if n == ""
    then paren (showExp True t ++ " → " ++ showExp True e)
    else "Π(" ++ n ++ " : " ++ showExp True t ++ ") . " ++ showExp True e
showExp _ (Mu n t) = "μ" ++ n ++ " . " ++ showExp True t
showExp _ (F t e) = "fold[" ++ showExp True t ++ "]" ++ showExp True e
showExp _ (U e) = "unfold" ++ paren (showExp True e)
showExp _ (Kind k) = show k
showExp _ (Let n t e1 e2) = "let " ++ n ++ " : " ++ showExp True t ++ " = " ++ showExp True e1 ++ " in " ++ showExp True e2

paren :: String -> String
paren x = "(" ++ x ++ ")"
