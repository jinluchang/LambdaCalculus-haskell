module Main where

import Parser
import Evaluation

import System.Environment

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    let expr = readExpr exprStr
        expr' = if "-O" `elem` args || "--inline" `elem` args
            then simplifyExprInline expr
            else expr
    if "-v" `elem` args
        then do
            putStrLn "Original Expression"
            putStrLn $ showExpr expr
            if "-O" `elem` args || "--inline" `elem` args
                then do
                    putStrLn "Inlined Expression"
                    putStrLn $ showExpr expr'
                else return ()
            putStrLn "Evaluation Start"
        else return ()

--    if "-v" `elem` args then putStrLn $ showLiftedExpr . buildLiftedExpr . buildExprList $ expr else return ()
--    if "-v" `elem` args then putStrLn $ showExprSKI . buildExprSKI $ expr else return ()

--    e' <- evalRefS expr
--    let e' = evalSKI expr
--    let e' = evalLifted expr
--    e' <- evalLiftedRefS expr
--    e' <- evalLiftedCRefS expr
--    e' <- evalSKIRefSP expr
    let e' = evalBC expr
    putStrLn $ showExpr . simplifyExpr . unBuildExprBruijn . buildExprBruijn $ e'
