module Main where

import Parser
import Evaluation

import System.Environment

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    let expr = readExpr exprStr
    putStrLn exprStr
    if "-v" `elem` args then putStrLn $ showLiftedExpr . buildLiftedExpr . buildExprList $ expr else return ()
    if "-v" `elem` args then putStrLn $ showExprSKI . buildExprSKI $ expr else return ()
--    e' <- evalRefS expr
--    e' <- return $ evalLifted expr
--    e' <- evalLiftedRefS expr
--    e' <- evalLiftedCRefS expr
    e' <- evalSKIRefSP expr
    putStrLn $ showExpr . simplifyExpr . unBuildExprBruijn . buildExprBruijn $ e'

