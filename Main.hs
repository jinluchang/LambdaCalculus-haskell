module Main where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Data.IORef

import Text.Parsec
import Text.Parsec.String

data Expr a
    = Var a
    | Ap (Expr a) (Expr a)
    | Lam a (Expr a)
    deriving (Eq, Show)

data ExprRef a
    = VarRef a
    | ApRef (IORef (ExprRef a)) (IORef (ExprRef a))
    | LamRef a (IORef (ExprRef a))

type Name = String
type LamExpr = Expr Name
type LamExprRef = ExprRef Name

-- Return True if the expression got reduced
evalStepRef :: IORef LamExprRef -> IO Bool
evalStepRef exprRef = do
    expr <- readIORef exprRef
    case expr of
        (VarRef _) -> return False
        (LamRef _ er) -> evalStepRef er
        (ApRef funRef argRef) -> applyStepRef exprRef funRef argRef

applyStepRef :: IORef LamExprRef -> IORef LamExprRef -> IORef LamExprRef -> IO Bool
applyStepRef exprRef funRef argRef = do
    fun <- readIORef funRef
    case fun of
        (VarRef _) -> evalStepRef argRef
        (ApRef e1 e2) -> do
            funRedex <- applyStepRef funRef e1 e2
            if funRedex
            then return True
            else evalStepRef argRef
        (LamRef x bodyRef) -> do
            body <- readIORef bodyRef
            maybeExprRef <- substitudeRef x argRef body
            case maybeExprRef of
                Nothing -> writeIORef exprRef body
                Just bodyRef' -> do
                    body' <- readIORef bodyRef'
                    writeIORef exprRef body'
            return True

substitudeRef :: Name -> IORef LamExprRef -> LamExprRef -> IO (Maybe (IORef LamExprRef))
substitudeRef x argRef body = do
    case body of
        (VarRef y)
            | y /= x -> return Nothing
            | otherwise -> do
                return $ Just argRef
        (LamRef y er)
            | x == y -> return Nothing
            | otherwise -> do
                e <- readIORef er
                b <- e `hasVarRef` x
                if not b
                then return Nothing
                else do
                    arg <- readIORef argRef
                    b' <- arg `hasVarRef` y
                    b'' <- e `hasVarRef` y
                    if not b' || not b''
                    then do
                        mer' <- substitudeRef x argRef e
                        liftM Just $ newIORef $ LamRef y $ fromJust mer'
                    else do
                        y' <- firstUnusedNameRef names [arg, e]
                        y'Ref <- newIORef $ VarRef y'
                        mer' <- substitudeRef y y'Ref e
                        e' <- readIORef $ fromJust mer'
                        mer'' <- substitudeRef x argRef e'
                        liftM Just $ newIORef $ LamRef y' $ fromJust mer''
        (ApRef er1 er2) -> do
            e1 <- readIORef er1
            mer1 <- substitudeRef x argRef e1
            e2 <- readIORef er2
            mer2 <- substitudeRef x argRef e2
            case (mer1, mer2) of
                (Nothing, Nothing) -> return Nothing
                (Just er1', Nothing) -> do
                    liftM Just $ newIORef $ ApRef er1' er2
                (Nothing, Just er2') -> do
                    liftM Just $ newIORef $ ApRef er1 er2'
                (Just er1', Just er2') -> do
                    liftM Just $ newIORef $ ApRef er1' er2'

hasVarRef :: LamExprRef -> Name -> IO Bool
hasVarRef (VarRef y) x = return $ x == y
hasVarRef (ApRef er1 er2) x = do
    e1 <- readIORef er1
    e2 <- readIORef er2
    b1 <- hasVarRef e1 x
    b2 <- hasVarRef e2 x
    return $ b1 || b2
hasVarRef (LamRef y er) x
    | x == y = return False
    | otherwise = do
        e <- readIORef er
        hasVarRef e x

firstUnusedNameRef :: [Name] -> [LamExprRef] -> IO Name
firstUnusedNameRef [] _ = error "firstUnusedName"
firstUnusedNameRef (n:ns) exprs = do
    bs <- mapM (`hasVarRef` n) exprs
    if all not bs
    then return n
    else firstUnusedNameRef ns exprs

buildLamExprRef :: LamExpr -> IO (IORef LamExprRef)
buildLamExprRef (Var x) = newIORef $ VarRef x
buildLamExprRef (Lam x expr) = do
    exprRef <- buildLamExprRef expr
    newIORef $ LamRef x exprRef
buildLamExprRef (Ap e1 e2) = do
    er1 <- buildLamExprRef e1
    er2 <- buildLamExprRef e2
    newIORef $ ApRef er1 er2

unBuildLamExprRef :: LamExprRef -> IO LamExpr
unBuildLamExprRef (VarRef x) = return $ Var x
unBuildLamExprRef (LamRef x er) = do
    e' <- readIORef er
    e <- unBuildLamExprRef e'
    return $ Lam x e
unBuildLamExprRef (ApRef er1 er2) = do
    e'1 <- readIORef er1
    e'2 <- readIORef er2
    e1 <- unBuildLamExprRef e'1
    e2 <- unBuildLamExprRef e'2
    return $ Ap e1 e2

repeatEvalRef :: LamExpr -> IO (Int, LamExpr)
repeatEvalRef expr = do
    exprRef <- buildLamExprRef expr
    go 0 exprRef
  where
    go n er = do
        print n
--        e' <- readIORef er
--        e <- unBuildLamExprRef e'
--        putStrLn $ showLamExpr e
        b <- evalStepRef er
        if b
        then seq n $ go (n+1) er
        else do
            e' <- readIORef er
            e <- unBuildLamExprRef e'
            return (n,e)

evalStep :: LamExpr -> Maybe LamExpr
evalStep (Lam x expr) = do
    expr' <- evalStep expr
    return $ Lam x expr'
evalStep (Var _) = Nothing
evalStep (Ap expr1 expr2) = applyStep expr1 expr2

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
    putStrLn $ showLamExpr expr
    (n,e) <- repeatEvalRef expr
    putStrLn $ show n ++ "\n" ++ showLamExpr e
--    putStrLn $ (\(n,e)-> show n ++ "\n" ++ showLamExpr e) . statistics $ repeatEval expr
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
