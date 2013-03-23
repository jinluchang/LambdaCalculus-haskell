module Main where

import Parser

main :: IO ()
main = do
    exprStr <- getContents
    let expr = readExpr exprStr
    putStrLn $ showExpr . unBuildExprBruijn . buildExprBruijn $ expr
