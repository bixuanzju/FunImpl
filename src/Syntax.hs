module Syntax where

import Data.List (intersperse)
import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen


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
          | Rec RecBind Expr  --TODO: could be merged to datatype?
          | Case Expr [Alt]
          | Let Sym Type Expr Expr
          -- Primitive nat
          | Nat
          | Lit Int
          | Add Expr Expr
          deriving Eq

data DataBind = DB Sym [(Sym, Type)] [Constructor]
  deriving Eq

data Constructor = Constructor { constrName :: Sym, constrParams :: [Type] }
  deriving Eq

data RecBind = RB Sym [(Sym, Type)] RecField
  deriving Eq

data RecField = RecField { recordName :: Sym, selector :: [(Sym, Type)] }
  deriving Eq

data Alt = Alt Pattern Expr deriving Eq

data Pattern = PConstr Constructor [(Sym, Type)] deriving Eq

isVal :: Expr -> Bool
isVal (Lam{}) = True
isVal (Pi{}) = True
isVal (F{}) = True
isVal (Lit _) = True
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
  pretty (Data datatypes e) = text "data" <+> pretty datatypes <$> pretty e
  pretty (Case e alts) = hang 2 (text "case" <+> pretty e <+> text "of" <$> text " " <+> intersperseBar (map pretty alts))
  pretty (Let n t e1 e2) = text "let" <+> pretty n <+> colon <+> pretty t <+> equals <+> pretty e1 <$> text "in" <$> pretty e2
  pretty (Rec recbind e) = text "Record" <+> pretty recbind <$> pretty e
  pretty Nat = text "nat"
  pretty (Add e1 e2) = parens (pretty e1 <+> text "+" <+> pretty e2)
  pretty (Lit n) = text (show n)

instance Pretty RecBind where
  pretty (RB n tpairs fields) = text n <+>
                                hsep
                                  (map (\(tv, tk) -> parens (pretty tv <+> colon <+> pretty tk))
                                     tpairs) <+>
                                equals <+>
                                pretty fields


instance Pretty RecField where
  pretty (RecField n binds) = text n <+>
                              lbrace <+>
                              hcat
                                (intersperse (comma <> space)
                                   (map (\(l, t) -> text l <+> colon <+> pretty t) binds)) <+>
                              rbrace <>
                              semi

instance Pretty Alt where
  pretty (Alt p e) = pretty p <+> char '⇒' <+> pretty e

instance Pretty Pattern where
  pretty (PConstr ctr []) = text (constrName ctr)
  pretty (PConstr ctr ps) =
    text (constrName ctr) <+>
    hsep (map (\(n, t) -> parens (pretty n <+> colon <+> pretty t)) ps)

instance Pretty DataBind where
  pretty (DB n tpairs cons) =
    text n <+>
    hsep (map (\(tv, tk) -> parens (pretty tv <+> colon <+> pretty tk)) tpairs) <+>
    align (equals <+> intersperseBar (map pretty cons) <$$> semi)

instance Pretty Constructor where
  pretty (Constructor n ts) = hsep $ text n : map pretty ts

intersperseBar :: [Doc] -> Doc
intersperseBar = foldl1 (\acc x -> acc <$$> char '|' <+> x)
