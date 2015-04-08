{
module Parser (parseExpr) where
import Data.Char (isDigit, isSpace, isAlpha)
import Data.List (stripPrefix)
import Syntax
}


%name parser
%tokentype { Token }
%error { parseError }


%token
    fold     { TokenKeyword "fold" }
    unfold   { TokenKeyword "unfold" }
    pi       { TokenKeyword "pi" }
    mu       { TokenKeyword "mu" }
    lam       { TokenKeyword "lam" }
    id       { TokenIdent $$ }
    ':'       { TokenSymbol ":" }
    '.'       { TokenSymbol "." }
    '['       { TokenSymbol "[" }
    ']'       { TokenSymbol "]" }
    '->'       { TokenSymbol "->" }
    '('       { TokenSymbol "(" }
    ')'       { TokenSymbol ")" }
    '*'       { TokenSymbol "*" }

%right '->'

%%

Expr : lam id ':' Expr '.' Expr  { Lam $2 $4 $6 }
     | pi id ':' Expr '.' Expr    { Pi $2 $4 $6 }
     | mu id '.' Expr    { Mu $2 $4 }
     | fold '[' Expr ']' Expr     { App (F $3) $5 }
     | unfold '[' Expr ']' Expr     { App (U $3) $5 }
     | '(' Expr '->' Expr ')' { Pi "" $2 $4 }
     | Exp         { $1 }

Exp : Exp Term { App $1 $2 }
    | Term       { $1 }

Term : id   { Var $1 }
    | '*'  { Kind Star }
    | '(' Expr ')'    { $2 }


{

parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
      = TokenInt Int
      | TokenKeyword String
      | TokenSymbol String
      | TokenIdent String

lexer :: [String] -> [String] -> String -> [Token]
lexer symbols keywords = lexer'
  where lexer' [] = []
        lexer' s@(c:cs)
          | isSpace c = lexer' cs
          | isDigit c = lexNum s
          | isAlpha c = lexVar s
          | otherwise = lexSym s symbols

        lexNum cs = TokenInt (read num) : lexer' rest
          where (num, rest) = span isDigit cs

        lexVar cs = token : lexer' rest
          where (var, rest) = span isAlpha cs
                token = if var `elem` keywords
                        then TokenKeyword var
                        else TokenIdent var

        lexSym cs (s:ss) = case stripPrefix s cs of
                            Just rest -> TokenSymbol s : lexer' rest
                            Nothing -> lexSym cs ss
        lexSym cs [] = error $ "Cannot tokenize " ++ cs

symbols = [".", "(", ")", ":", "\\", "*", "->", "[", "]"]
keywords = ["fold", "unfold", "pi", "mu", "lam"]

parseExpr = parser . lexer symbols keywords

}
