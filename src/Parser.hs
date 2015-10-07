module Parser where

import           Control.Applicative
import           Text.Parsec hiding (Empty, (<|>), many)
import           Text.Parsec.Expr
import           Text.Parsec.Language (emptyDef)
import qualified Text.Parsec.Token as TK

import           Syntax

parser :: String -> Either ParseError Expr
parser = parse parseTerm ""

parseTerm = parselam <|> parsepi1 <|> parsepi2 <|> parsemu <|> parseF <|> parseU <|> formula

parseTele = do
  reservedOp "("
  x <- ident
  reservedOp ":"
  t <- parseTerm
  reservedOp ")"
  return (x, t)

parselam = do
  reservedOp "\\"
  tele <- many1 parseTele
  reservedOp "."
  e <- parseTerm
  return (elam tele e)

parsepi1 = do
  reservedOp "pi"
  tele <- many1 parseTele
  reservedOp "."
  e <- parseTerm
  return (epi tele e)

parsepi2 = do
  pair <- parseTele
  reservedOp "->"
  e <- parseTerm
  return (epi [pair] e)

parsearr = do
  e1 <- parseAtom
  reservedOp "->"
  e2 <- parseAtom
  return (earr e1 e2)

parsemu = do
  reservedOp "mu"
  (x, t) <- parseTele
  reservedOp "."
  e <- parseTerm
  return (emu (x, t) e)

parseF = do
  reservedOp "castup"
  t <- brackets parseTerm
  e <- parseTerm
  return (F t e)

parseU = do
  reservedOp "castdown"
  e <- parseTerm
  return (U e)

formula = buildExpressionParser [[mulOp], [addOp, subOp]] juxta <?> "formula"
  where
    addOp = Infix (reservedOp "+" >> return addExpr) AssocLeft
    subOp = Infix (reservedOp "-" >> return subExpr) AssocLeft
    mulOp = Infix (reservedOp "*" >> return multExpr) AssocLeft


juxta = (foldl1 App) `fmap` (many1 parseAtom)

parseAtom =
  natTy
  <|> starTy
  <|> parens parseTerm
  <|> variable
  <|> number
  <?> "atom"

number = (Lit . fromInteger) <$> natural

variable = evar <$> ident

natTy = do
  reserved "nat"
  return Nat

starTy = do
  reserved "star"
  return (Kind Star)

-- Lexer
lexer :: TK.TokenParser ()
lexer = TK.makeTokenParser style
  where
    style = emptyDef
      { TK.reservedOpNames = [ "->"
                             , "\\"
                             , "+"
                             , "*"
                             , "-"
                             , "="
                             , "."
                             , "("
                             , ")"
                             , "mu"
                             , "pi"
                             , "castup"
                             , "castdown"
                             ]
      , TK.reservedNames = ["let", "in", "nat", "star"]
      , TK.commentLine = "#"
      }
parens = TK.parens lexer
brackets = TK.brackets lexer
ident = TK.identifier lexer
natural = TK.natural lexer
reserved = TK.reserved lexer
reservedOp = TK.reservedOp lexer
