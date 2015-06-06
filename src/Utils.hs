module Utils where

import Syntax

genLambdas :: [(Sym, Type)] -> Expr -> Expr
genLambdas params body = foldr (\(x, t) l -> Lam x t l) body params

genVarsAndTypes :: Char -> [Type] -> [(Sym, Type)]
genVarsAndTypes c ts = map (\(n, t) -> (c : show n, t)) (zip [0 :: Int ..] ts)
