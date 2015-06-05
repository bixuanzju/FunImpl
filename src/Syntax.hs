module Syntax where

import Text.PrettyPrint.ANSI.Leijen
import Prelude hiding ((<$>))


data Program = Progm [Expr]

type Sym = String

data Expr = Var Sym
          | App Expr Expr
          | Lam Sym Type Expr
          | Pi Sym Type Type
          | Mu Sym Type Type
          | F Type Expr
          | U Expr
          | Kind Kinds
          -- Surface language
          | Data DataBind Expr
          | Case Expr [Alt]
          | Let Sym Type Expr Expr
          deriving Eq

data DataBind = DB String [(Sym, Type)] [Constructor]
  deriving (Eq, Show)

data Constructor = Constructor { constrName :: Sym, constrParams :: [Type] }
  deriving (Eq, Show)

data Alt = ConstrAlt Pattern Expr deriving Eq

data Pattern = PConstr Constructor [(Sym, Type)] deriving Eq

isVal :: Expr -> Bool
isVal (Lam _ _ _) = True
isVal (Pi _ _ _) = True
isVal (F _ _) = True
isVal _ = False

type Type = Expr

data Kinds = Star | Box deriving (Eq, Read)

-- Pretty printer

instance Show Expr where
  show e = show (pretty e)

instance Show Program where
  show (Progm exprs) = concatMap show exprs

instance Pretty Kinds where
  pretty Star = char '⋆'
  pretty Box = char '□'

instance Pretty Expr where
  pretty (Var x) = text x
  pretty (App e1 e2) = parens $ pretty e1 <+> pretty e2
  pretty (Lam n t e) = parens $ text "λ" <> parens (pretty n <+> colon <+> pretty t) <> dot <+> pretty e
  pretty (Pi n t e) =
    if n == ""
    then parens $ pretty t <+> char '→' <+> pretty e
    else parens $ char 'Π' <> parens (pretty n <+> colon <+> pretty t) <> dot <+> pretty e
  pretty (Mu n t e) = char 'μ' <> parens (pretty n <+> colon <+> pretty t) <> dot <+> pretty e
  pretty (F t e) = text "fold" <> brackets (pretty t) <+> parens (pretty e)
  pretty (U e) = text "unfold" <> parens (pretty e)
  pretty (Kind k) = pretty k
  pretty (Data datatypes e) = text "data" <+> (pretty datatypes) <$> pretty e
  pretty (Case e alts) = hang 2 (text "case" <+> pretty e <+> text "of" <$> text " " <+> intersperseBar (map pretty alts))
  pretty (Let n t e1 e2) = text "let" <+> parens (pretty n <+> colon <+> pretty t) <+> equals <+> pretty e1 <$> text "in" <$> pretty e2

instance Pretty Alt where
  pretty (ConstrAlt p e) = (pretty p) <+> char '⇒' <+> pretty e

instance Pretty Pattern where
  pretty (PConstr ctr []) = text (constrName ctr)
  pretty (PConstr ctr ps) =
    text (constrName ctr) <+>
    (hsep $
       map (\(n, t) -> parens (pretty n <+> colon <+> pretty t)) ps)

instance Pretty DataBind where
  pretty (DB n tpairs cons) =
    text n <+>
    hsep (map (\(tv, tk) -> parens (pretty tv <+> colon <+> pretty tk)) tpairs) <+>
    align (equals <+> intersperseBar (map pretty cons) <$$> semi)

instance Pretty Constructor where
  pretty (Constructor n ts) = hsep $ text n : map pretty ts

intersperseBar :: [Doc] -> Doc
intersperseBar = foldl1 (\acc x -> acc <$$> (char '|') <+> x)
