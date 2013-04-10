module Main where

import Parser
import Evaluation

preludeStr :: String
preludeStr =
    "module Main where\n\n" ++
    "import Parser\n\n"

compile :: LamExpr -> String
compile (Var x) = x
compile (Ap e1 e2) = "applyC (" ++ compile e1 ++ ") (" ++ compile e2 ++ ")"
compile (Lam x e) = "LamC $ \\" ++ x ++ " -> " ++ compile e

mainStr :: String
mainStr =
    "main :: IO ()\n" ++
    "main = putStrLn . showExpr . unBuildExprBruijn . buildExprBruijn . unBuildExprC $ expr\n"

progGen :: LamExpr -> String
progGen e =
    preludeStr ++
    mainStr ++ "\n" ++
    "expr :: LamExprC\n" ++
    "expr = " ++ compile e ++ "\n"

main :: IO ()
main = do
    exprStr <- getContents
    let exprRead = unBuildExprBruijn . buildExprBruijn . simplifyExprInline $ readExpr exprStr
    putStrLn $ progGen exprRead
