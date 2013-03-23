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
--            let e' = evalBFunc expr
--            e' <- evalSKIRefSP expr
--            e' <- evalLiftedRefS expr
            e' <- evalLiftedCRefS expr
            putStrLn $ showExpr . unBuildExprBruijn . decodeBruijn . unBuildBinaryList $ e'
