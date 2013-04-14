{-# LANGUAGE QuasiQuotes #-}

module Main where

import Parser
import Evaluation
import StringQQ

main :: IO ()
main = do
    exprStr <- getContents
    let exprRead = unBuildExprBruijn' . explicitFreeVariable . buildExprBruijn . simplifyExprInline $ readExpr exprStr
    putStrLn $ progGen exprRead

explicitFreeVariable :: LamExprBruijn -> LamExprBruijn
explicitFreeVariable = go where
    go (VarBruijn x) = VarBruijn $ "(VarC \"" ++ x ++ "\")"
    go (BoundBruijn n) = BoundBruijn n
    go (ApBruijn e1 e2) = ApBruijn (go e1) (go e2)
    go (LamBruijn eb) = LamBruijn $ go eb

unBuildExprBruijn' :: LamExprBruijn -> LamExpr
unBuildExprBruijn' = go names where
    go _ (VarBruijn x) = Var x
    go ns (ApBruijn e1 e2) = Ap (go ns e1) (go ns e2)
    go (n:ns) (LamBruijn eb) = Lam n' $ go ns' eb' where
        (n',ns') = if eb' `hasVarBruijn` n then (n,ns) else ("_", n:ns)
        eb' = substituteBruijn (VarBruijn n) eb
    go _ _ = error "unBuildExprBruijn"

compile :: LamExpr -> String
compile (Var x) = x
compile (Ap e1 e2) = "applyC " ++ compileA e1 ++ " " ++ compileA e2
compile (Lam x e) = "LamC $ \\" ++ x ++ " -> " ++ compile e

compileA :: LamExpr -> String
compileA (Var x) = x
compileA e = "(" ++ compile e ++ ")"

progGen :: LamExpr -> String
progGen e =
    preludeStr ++
    "expression :: LamExprC\n" ++
    "expression = " ++ compile e

preludeStr :: String
preludeStr = [stringQQ|
module Main where

import Data.List

data Expr a
    = Var a
    | Ap (Expr a) (Expr a)
    | Lam a (Expr a)
    deriving (Eq, Show)

data ExprBruijn a
    = VarBruijn a
    | BoundBruijn Int
    | ApBruijn (ExprBruijn a) (ExprBruijn a)
    | LamBruijn (ExprBruijn a)
    deriving Show

data ExprC a
    = VarC a
    | ApC (ExprC a) (ExprC a)
    | LamC (ExprC a -> ExprC a)

type Name = String
type LamExpr = Expr Name
type LamExprBruijn = ExprBruijn Name
type LamExprC = ExprC Name

main :: IO ()
main = putStrLn . showExpr . unBuildExprBruijn . buildExprBruijn . unBuildExprC $ expression

showExpr :: LamExpr -> String
showExpr (Var x) = x
showExpr (Ap expr1 expr2@(Ap _ _)) = showExpr expr1 ++ " (" ++ showExpr expr2 ++ ")"
showExpr (Ap expr1 expr2) = showExpr expr1 ++ " " ++ showExpr expr2
showExpr (Lam x expr) = showLamList [x] expr

showLamList :: [Name] -> LamExpr -> String
showLamList xs (Lam x expr) = showLamList (x:xs) expr
showLamList xs expr = "(\\" ++ intercalate " " (reverse xs) ++ " -> " ++ showExpr expr ++ ")"

unBuildExprC :: LamExprC -> LamExpr
unBuildExprC = go variableNames where
    go vns (LamC f) = Lam (head vns) $ go (tail vns) $ f (VarC (head vns))
    go vns (ApC e1 e2) = Ap (go vns e1) (go vns e2)
    go _ (VarC x) = Var x

buildExprBruijn :: Eq a => Expr a -> ExprBruijn a
buildExprBruijn (Var x) = VarBruijn x
buildExprBruijn (Ap e1 e2) = ApBruijn (buildExprBruijn e1) (buildExprBruijn e2)
buildExprBruijn (Lam x e) = LamBruijn $ go 0 $ buildExprBruijn e where
    go n (LamBruijn b) = LamBruijn (go (n+1) b)
    go n (ApBruijn e1 e2) = ApBruijn (go n e1) (go n e2)
    go n (VarBruijn y) | y == x = BoundBruijn n
                       | otherwise = VarBruijn y
    go _ (BoundBruijn i) = BoundBruijn i

unBuildExprBruijn :: LamExprBruijn -> LamExpr
unBuildExprBruijn (VarBruijn x) = Var x
unBuildExprBruijn (ApBruijn e1 e2) = Ap (unBuildExprBruijn e1) (unBuildExprBruijn e2)
unBuildExprBruijn (LamBruijn b) = Lam x' $ unBuildExprBruijn b' where
    x' = if b' `hasVarBruijn` x then x else "_"
    b' = substituteBruijn (VarBruijn x) b
    x = firstUnusedNameBruijn names [b]
unBuildExprBruijn (BoundBruijn _) = error "unBuildExprBruijn"

substituteBruijn :: ExprBruijn a -> ExprBruijn a -> ExprBruijn a
substituteBruijn arg body = go 0 body where
    go n (LamBruijn b) = LamBruijn (go (n+1) b)
    go n (ApBruijn e1 e2) = ApBruijn (go n e1) (go n e2)
    go _ (VarBruijn x) = VarBruijn x
    go n (BoundBruijn i) | i == n = arg
                         | otherwise = BoundBruijn i

firstUnusedNameBruijn :: Eq a => [a] -> [ExprBruijn a] -> a
firstUnusedNameBruijn [] _ = error "firstUnusedNameBruijn"
firstUnusedNameBruijn (n:ns) exprs
    | all (not . (`hasVarBruijn` n)) exprs = n
    | otherwise = firstUnusedNameBruijn ns exprs

hasVarBruijn :: Eq a => ExprBruijn a -> a -> Bool
hasVarBruijn (VarBruijn y) x = x == y
hasVarBruijn (BoundBruijn _) _ = False
hasVarBruijn (LamBruijn b) x = b `hasVarBruijn` x
hasVarBruijn (ApBruijn e1 e2) x = e1 `hasVarBruijn` x || e2 `hasVarBruijn` x

names :: [Name]
names = (map (\c -> [c]) "abcdefghijklmnopqrstuvwxyz" ++) . map ("var"++) $ map show ([1..] :: [Integer])

variableNames :: [Name]
variableNames = map ("$Var" ++) $ map show ([1..] :: [Integer])

applyC :: ExprC a -> ExprC a -> ExprC a
applyC fun arg = case fun of
    LamC f -> f arg
    _ -> ApC fun arg

|]
