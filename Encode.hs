module Main where

import Parser
import System.Environment

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    let expr = readExpr exprStr
    if "-b" `elem` args
    then putStrLn $ encodeBruijn . buildExprBruijn $ expr
    else putStrLn $ encodeBoolList . encodeBruijn . buildExprBruijn $ expr
