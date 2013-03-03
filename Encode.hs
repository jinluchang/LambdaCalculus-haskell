module Main where

import Parser

main :: IO ()
main = do
    exprStr <- getContents
    let expr = readExpr exprStr
    putStrLn $ encodeBoolList . encodeBruijn . buildExprBruijn $ expr
