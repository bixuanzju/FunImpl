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
    fold   { TokenKeyword "fold" }
    unfold { TokenKeyword "unfold" }
    pi     { TokenKeyword "pi" }
    let     { TokenKeyword "let" }
    in     { TokenKeyword "in" }
    mu     { TokenKeyword "mu" }
    lam    { TokenKeyword "lam" }
    data    { TokenKeyword "data" }
    id     { TokenIdent $$ }
    ':'    { TokenSymbol ":" }
    '='    { TokenSymbol "=" }
    '.'    { TokenSymbol "." }
    '['    { TokenSymbol "[" }
    ']'    { TokenSymbol "]" }
    '->'   { TokenSymbol "->" }
    '('    { TokenSymbol "(" }
    ')'    { TokenSymbol ")" }
    '*'    { TokenSymbol "*" }
    ';'    { TokenSymbol ";" }
    '|'    { TokenSymbol "|" }
    '&'    { TokenSymbol "&" }


%right ';'
%right '.'
%right '->'
%right ']'
%right in
%left UNFOLD


%monad { Either String }

%%

Progm : Exprs                           { Progm $1 }

Exprs : Expr                            { [$1] }
      | Exprs '&' Expr                  {$1 ++ [$3]}

Expr : lam id ':' Expr '.' Expr         { Lam $2 $4 $6 }
     | pi id ':' Expr '.' Expr          { Pi $2 $4 $6 }
     | mu id ':' Expr '.' Expr          { Mu $2 $4 $6}
     | fold '[' Expr ']' Expr           { F $3 $5 }
     | unfold Expr %prec UNFOLD         { U $2 }
     | data databind ';' Expr          { Data $2 $4 }
     -- desugar
     | Expr '->' Expr                   { Pi "" $1 $3 }
     | let id ':' Expr '=' Expr in Expr { App (Lam $2 $4 $8) $6 }
     | Exp                              { $1 }

Exp : Exp Term                          { App $1 $2 }
    | Term                              { $1 }

Term : id                               { Var $1 }
    | '*'                               { Kind Star }
    | '(' Expr ')'                      { $2 }

databind : id ty_param_list_or_empty '=' constrs_decl { DB $1 $2 $4 }

ty_param_list_or_empty
  : ty_param_list   { $1 }
  | {- empty -}     { [] }

ty_param_list
  : ty_param   { [$1] }
  | ty_param ty_param_list { $1:$2 }

ty_param : '(' id ':' kindExpr ')'  { ($2, $4) }

kindExpr : '*'   { Kind Star }
         | kindExpr '->' kindExpr  {Pi "" $1 $3 }

constrs_decl : constr_decl  { [$1] }
             | constr_decl '|' constrs_decl   { $1:$3 }

constr_decl : id types  { Constructor $1 $2 }

types : {- empty -}    { [] }
      | ftype types   { $1:$2 }

ftype : ftype atype    { App $1 $2 }
      | atype          { $1 }

atype : id   { Var $1 }
      | '(' ftype ')'  { $2 }



{

parseError _ = Left "Parse error!"

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

symbols = [".", "(", ")", ":", "\\", "*", "->", "[", "]", ";" , "=", "|", "&"]
keywords = ["fold", "unfold", "pi", "mu", "lam", "beta", "let", "in", "data"]

parseExpr = parser . lexer symbols keywords

}
