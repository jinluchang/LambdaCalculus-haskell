module Main where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Text.Parsec
import Text.Parsec.String

data Expr a
    = Var a
    | Ap (Expr a) (Expr a)
    | Lam a (Expr a)
    deriving (Eq, Show)

type Env a = M.Map a (Expr a)
type Closure a = (Expr a, Env a)

type Name = String
type LamExpr = Expr Name

type LamClosure = Closure Name

names :: [Name]
names = map ("var"++) $ map show ([1..] :: [Integer])

firstUnusedName :: [Name] -> [LamExpr] -> Name
firstUnusedName [] _ = error "firstUnusedName"
firstUnusedName (n:ns) exprs
    | all (not . (`hasVar` n)) exprs = n
    | otherwise = firstUnusedName ns exprs

freeVariables :: LamExpr -> S.Set Name
freeVariables (Var x) = S.singleton x
freeVariables (Ap expr1 expr2) = S.union (freeVariables expr1) (freeVariables expr2)
freeVariables (Lam x expr) = S.delete x $ freeVariables expr

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

{-
applyStep' :: LamExpr -> LamExpr -> Maybe LamExpr
applyStep' (Var f) arg = do
    arg' <- evalStep arg
    return $ Ap (Var f) $ arg'
applyStep' (Lam x expr) arg = case evalStep arg of
    Nothing -> Just $ substitude x arg expr
    Just arg' -> Just $ Ap (Lam x expr) arg'
applyStep' (Ap expr1 expr2) arg = case evalStep arg of
    Nothing -> do
        expr <- applyStep' expr1 expr2
        return $ Ap expr arg
    Just arg' -> Just $ Ap (Ap expr1 expr2) arg'
-- -}

applyStep :: LamExpr -> LamExpr -> Maybe LamExpr
applyStep (Var f) arg = do
    arg' <- evalStep arg
    return $ Ap (Var f) $ arg'
applyStep (Lam x expr) arg = Just $ substitude x arg expr
applyStep (Ap expr1 expr2) arg = case applyStep expr1 expr2 of
    Nothing -> do
        arg' <- evalStep arg
        return $ Ap (Ap expr1 expr2) arg'
    Just expr -> Just $ Ap expr arg

evalStep :: LamExpr -> Maybe LamExpr
evalStep (Lam x expr) = do
    expr' <- evalStep expr
    return $ Lam x expr'
evalStep (Var _) = Nothing
evalStep (Ap expr1 expr2) = applyStep expr1 expr2

repeatEval :: LamExpr -> [LamExpr]
repeatEval expr = expr : case evalStep expr of
    Nothing -> []
    Just expr' -> repeatEval expr'

statistics :: [a] -> (Int, a)
statistics exprs = go 0 exprs where
    go _ [] = error "statistics"
    go n [e] = (n,e)
    go n (_:es) = go (n+1) es

main :: IO ()
main = do
    exprStr <- getContents
    let expr = readLamExpr exprStr
    putStr exprStr
    putStrLn $ (\(n,e)-> show n ++ "\n" ++ showLamExpr e) . statistics $ repeatEval expr
--    mapM_ putStrLn $ map showLamExpr $ repeatEval expr

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
