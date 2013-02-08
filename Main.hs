module Main where

import Data.List
import Text.Parsec
import Text.Parsec.String

data Expr a
    = Var a
    | Ap (Expr a) (Expr a)
    | Lam a (Expr a)
    deriving (Eq, Show)

type Name = String
type LamExpr = Expr Name

names :: [Name]
names = map ("var"++) $ map show ([1..] :: [Integer])

firstUnusedName :: [Name] -> [LamExpr] -> Name
firstUnusedName [] _ = error "firstUnusedName"
firstUnusedName (n:ns) exprs
    | all (not . (`hasVar` n)) exprs = n
    | otherwise = firstUnusedName ns exprs

hasVar :: LamExpr -> Name -> Bool
hasVar (Var y) x = x == y
hasVar (Ap expr1 expr2) x = expr1 `hasVar` x || expr2 `hasVar` x
hasVar (Lam y expr) x
    | x == y = False
    | otherwise = expr `hasVar` x

substitude :: Name -> LamExpr -> LamExpr -> LamExpr
substitude x arg (Var y)
    | y == x = arg
    | otherwise = Var y
substitude x arg (Ap expr1 exp2) = Ap (substitude x arg expr1) (substitude x arg exp2)
substitude x arg (Lam y expr)
    | y == x = Lam y expr
    | arg `hasVar` y = Lam y' $ substitude x arg $ substitude y (Var y') expr
    | otherwise = Lam y (substitude x arg expr)
  where
    y' = firstUnusedName names [arg, expr]

apply :: LamExpr -> LamExpr -> LamExpr
apply (Var f) arg = Ap (Var f) $ eval arg
apply (Lam x expr) arg = substitude x arg expr
apply (Ap expr1 expr2) arg = Ap (apply expr1 expr2) $ eval arg

eval :: LamExpr -> LamExpr
eval (Lam x expr) = Lam x $ eval expr
eval (Var x) = (Var x)
eval (Ap expr1 expr2) = apply expr1 expr2

main :: IO ()
main = do
    exprStr <- getContents
    let expr = readLamExpr exprStr
    putStr exprStr
    mapM_ putStrLn $ take 300 . drop 500 . map showLamExpr $ iterate eval expr

showLamExpr :: LamExpr -> String
showLamExpr (Var x) = x
showLamExpr (Ap expr1 expr2@(Ap _ _)) = showLamExpr expr1 ++ " (" ++ showLamExpr expr2 ++ ")"
showLamExpr (Ap expr1 expr2) = showLamExpr expr1 ++ " " ++ showLamExpr expr2
showLamExpr (Lam x expr) = showLamList [x] expr

readLamExpr :: String -> LamExpr
readLamExpr str = case parse pLamExpr (take 10 str) str of
    Left e -> error $ show e
    Right expr -> expr

pLamExpr :: Parser LamExpr
pLamExpr = chainl1 (try $ spaces >> (pParentheseExpr <|> pVar <|> pLam)) (return Ap)

pParentheseExpr :: Parser LamExpr
pParentheseExpr = do
    _ <- char '('
    expr <- pLamExpr
    spaces
    _ <- char ')'
    return expr

pVar :: Parser LamExpr
pVar = do
    x <- pName
    return $ Var x

pName :: Parser Name
pName = do
    cs <- many1 (oneOf "+*!@$%^&_=" <|> alphaNum)
    return cs

pLam :: Parser LamExpr
pLam = do
    _ <- char '\\'
    spaces
    xs <- many1 (try $ spaces >> pName)
    spaces
    _ <- string "->"
    spaces
    expr <- pLamExpr
    return $ genLamList xs expr

genLamList :: [Name] -> LamExpr -> LamExpr
genLamList [] expr = expr
genLamList (x:xs) expr = Lam x $ genLamList xs expr

showLamList :: [Name] -> LamExpr -> String
showLamList xs (Lam x expr) = showLamList (x:xs) expr
showLamList xs expr = "(\\" ++ intercalate " " (reverse xs) ++ " -> " ++ showLamExpr expr ++ ")"
