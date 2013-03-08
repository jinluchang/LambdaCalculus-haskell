module Main where

import Parser
import Evaluation
import System.Environment

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    if "-b" `elem` args
        then putStrLn $ showExpr . unBuildExprBruijn . decodeBruijn $ exprStr
        else do
            let expr = readExpr exprStr
            e' <- evalSKIRefSP expr
            putStrLn $ showExpr . unBuildExprBruijn . decodeBruijn . unBuildBinaryList $ e'
