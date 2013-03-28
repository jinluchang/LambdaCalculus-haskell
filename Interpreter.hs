module Main where

import Parser
import Evaluation

import System.Environment

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    let exprRead = readExpr exprStr
        expr = simplifyExprInline exprRead
    putStrLn $ showExpr exprRead
    putStrLn $ showExpr expr
    putStrLn "Evaluation Start"
    if "-v" `elem` args then putStrLn $ showLiftedExpr . buildLiftedExpr . buildExprList $ expr else return ()
    if "-v" `elem` args then putStrLn $ showExprSKI . buildExprSKI $ expr else return ()
--    e' <- evalRefS expr
--    let e' = evalSKI expr
--    let e' = evalLifted expr
--    e' <- evalLiftedRefS expr
--    e' <- evalLiftedCRefS expr
--    e' <- evalSKIRefSP expr
    let e' = evalBFunc expr
    putStrLn $ showExpr . simplifyExpr . unBuildExprBruijn . buildExprBruijn $ e'
