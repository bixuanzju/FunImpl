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
    let    { TokenKeyword "let" }
    in     { TokenKeyword "in" }
    mu     { TokenKeyword "mu" }
    data   { TokenKeyword "data" }
    rec   { TokenKeyword "rec" }
    case   { TokenKeyword "case" }
    of     { TokenKeyword "of" }
    nat     { TokenKeyword "nat" }
    id     { TokenIdent $$ }
    digits { TokenDigits $$ }
    ':'    { TokenSymbol ":" }
    '='    { TokenSymbol "=" }
    '.'    { TokenSymbol "." }
    '['    { TokenSymbol "[" }
    ']'    { TokenSymbol "]" }
    '->'   { TokenSymbol "->" }
    '=>'   { TokenSymbol "=>" }
    '('    { TokenSymbol "(" }
    ')'    { TokenSymbol ")" }
    '*'    { TokenSymbol "*" }
    ';'    { TokenSymbol ";" }
    '|'    { TokenSymbol "|" }
    '&'    { TokenSymbol "&" }
    '{'    { TokenSymbol "{" }
    '}'    { TokenSymbol "}" }
    ','    { TokenSymbol "," }
    '\\'    { TokenSymbol "\\" }
    '+'    { TokenSymbol "+" }


%right ';'
%right in
%right '.'
%right '=>'
%right '->'
%right ']'
%left '+'
%left UNFOLD


%monad { Either String }

%%

progm : exprs                                   { Progm $1 }

exprs : expr                                    { [$1] }
      | exprs '&' expr                          { $1 ++ [$3] }

expr : '\\' id ':' expr '.' expr                { Lam $2 $4 $6 }
     | pi id ':' expr '.' expr                  { Pi $2 $4 $6 }
     | mu id ':' expr '.' expr                  { Mu $2 $4 $6}
     | fold digits '[' expr ']' expr            { F $2 $4 $6 }
     | unfold digits expr %prec UNFOLD          { U $2 $3}
     | data databind ';' expr                   { Data $2 $4 }
     | rec recbind ';' expr                     { Rec $2 $4 }
     | case expr of alts                        { Case $2 $4}
     -- surface language
     | expr '+' expr                            { Add $1 $3 }
     | expr '->' expr                           { Pi "" $1 $3 }
     | let id ':' expr '=' expr in expr         { Let $2 $4 $6 $8 }
     | aexp                                     { $1 }

aexp : aexp term                                { App $1 $2 }
     | term                                     { $1 }

term : nat                                      { Nat }
     | id                                       { Var $1 }
     | digits                                   { Lit $1 }
     | '*'                                      { Kind Star }
     | '(' expr ')'                             { $2 }

recbind : id ty_param_list_or_empty '=' records { RB $1 $2 $4 }

records : id '{' fields '}'                     { RecField $1 $3 }

fields : fparam                                 { [$1] }
       | fparam ',' fields                      { $1:$3 }

fparam : id ':' expr                            { ($1,$3) }

databind
  : id ty_param_list_or_empty '=' constrs_decl  { DB $1 $2 $4 }

ty_param_list_or_empty
  : ty_param_list                               { $1 }
  | {- empty -}                                 { [] }

ty_param_list
  : ty_param                                    { [$1] }
  | ty_param ty_param_list                      { $1:$2 }

ty_param : '(' id ':' expr ')'                  { ($2, $4) }

constrs_decl : constr_decl                      { [$1] }
             | constr_decl '|' constrs_decl     { $1:$3 }

constr_decl : id types                          { Constructor $1 $2 }

types : {- empty -}                             { [] }
      | ftype types                             { $1:$2 }

ftype : '(' expr ')'                            { $2 }
      | nat                                     { Nat }
      | id                                      { Var $1 }

alts : alt                                      { [$1] }
     | alt '|' alts                             { $1:$3 }

alt : pattern '=>' expr                         { Alt $1 $3 }

pattern : id ty_param_list_or_empty             { PConstr (Constructor $1 []) $2 }


{

parseError _ = Left "Parse error!"

data Token
      = TokenDigits Int
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

        lexNum cs = TokenDigits (read num) : lexer' rest
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

symbols = [".", "(", ")", ":", "\\", "*", "->", "=>", "[", "]", ";" , "=", "|", "&", "{", "}", ",", "+"]
keywords = ["fold", "unfold", "pi", "mu", "beta", "let", "in", "data", "case", "of", "rec", "nat"]

parseExpr = parser . lexer symbols keywords

}
