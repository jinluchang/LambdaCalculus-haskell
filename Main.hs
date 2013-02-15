module Main where

import Control.Monad
import Data.List
import Data.Maybe
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

data ExprSKI a
    = VarSKI a
    | ApSKI (ExprSKI a) (ExprSKI a)
    | SSKI
    | KSKI
    | ISKI
    | FstSKI
    | SndSKI

data ExprSKIRef a
    = VarSKIRef a
    | ApSKIRef (IORef (ExprSKIRef a)) (IORef (ExprSKIRef a))
    | SSKIRef
    | KSKIRef
    | ISKIRef
    | FstSKIRef
    | SndSKIRef

type Name = String
type LamExpr = Expr Name
type LamExprRef = ExprRef Name
type LamExprSKI = ExprSKI Name
type LamExprSKIRef = ExprSKIRef Name

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
{-

buildExprSKIRef :: ExprSKI a -> IO (IORef (ExprSKIRef a))
buildExprSKIRef (VarSKI x) = newIORef $ VarSKIRef x
buildExprSKIRef (ApSKI e1 e2) = do
    er1 <- buildExprSKIRef e1
    er2 <- buildExprSKIRef e2
    newIORef $ ApSKIRef er1 er2
buildExprSKIRef SSKI = newIORef $ SSKIRef
buildExprSKIRef KSKI = newIORef $ KSKIRef
buildExprSKIRef ISKI = newIORef $ ISKIRef
buildExprSKIRef FstSKI = newIORef $ FstSKIRef
buildExprSKIRef SndSKI = newIORef $ SndSKIRef

unBuildExprSKIRef :: IORef (ExprSKIRef a) -> IO (ExprSKI a)
unBuildExprSKIRef er = do
    e <- readIORef er
    case e of
        (VarSKIRef x) -> return $ VarSKI x
        (ApSKIRef er1 er2) -> do
            e1 <- unBuildExprSKIRef er1
            e2 <- unBuildExprSKIRef er2
            return $ ApSKI e1 e2
        SSKIRef -> return SSKI
        KSKIRef -> return KSKI
        ISKIRef -> return ISKI
        FstSKIRef -> return FstSKI
        SndSKIRef -> return SndSKI

evalStepSKIRef :: IORef LamExprSKIRef -> IO Bool
evalStepSKIRef

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalStepSKI :: LamExprSKI -> Maybe LamExprSKI
evalStepSKI SSKI = Nothing
evalStepSKI KSKI = Nothing
evalStepSKI ISKI = Nothing
evalStepSKI FstSKI = Nothing
evalStepSKI SndSKI = Nothing
evalStepSKI (VarSKI _) = Nothing
evalStepSKI (ApSKI ISKI e) = Just e
evalStepSKI (ApSKI (ApSKI KSKI e1) _) = Just e1
evalStepSKI (ApSKI (ApSKI (ApSKI SSKI e1) e2) e3) = Just $ ApSKI (ApSKI e1 e3) (ApSKI e2 e3)
evalStepSKI (ApSKI (ApSKI (ApSKI FstSKI e1) e2) e3) = Just $ ApSKI (ApSKI e1 e3) e2
evalStepSKI (ApSKI (ApSKI (ApSKI SndSKI e1) e2) e3) = Just $ ApSKI e1 (ApSKI e2 e3)
evalStepSKI (ApSKI e1 e2) = applyStepSKI e1 e2

applyStepSKI :: LamExprSKI -> LamExprSKI -> Maybe LamExprSKI
applyStepSKI e1 e2 = case evalStepSKI e1 of
    Nothing -> case evalStepSKI e2 of
        Nothing -> Nothing
        Just e2' -> Just $ ApSKI e1 e2'
    Just e1' -> Just $ ApSKI e1' e2

repeatEvalSKI :: LamExprSKI -> [LamExprSKI]
repeatEvalSKI expr = expr : case evalStepSKI expr of
    Nothing -> []
    Just expr' -> repeatEvalSKI expr'

evalSKI :: LamExprSKI -> LamExprSKI
evalSKI e = case evalStepSKI e of
    Nothing -> e
    Just e' -> evalSKI e'

buildExprSKI :: (Eq a) => Expr a -> ExprSKI a
buildExprSKI (Var x) = VarSKI x
buildExprSKI (Ap e1 e2) = ApSKI (buildExprSKI e1) (buildExprSKI e2)
buildExprSKI (Lam x e) = buildExprSKILam x $ buildExprSKI e

buildExprSKILam :: (Eq a) => a -> ExprSKI a -> ExprSKI a
buildExprSKILam x e | not (e `hasVarSKI` x) = ApSKI KSKI e
buildExprSKILam x (VarSKI y)
    | x == y = ISKI
    | otherwise = ApSKI KSKI (VarSKI y)
buildExprSKILam x (ApSKI e1 e2)
    | not (e1 `hasVarSKI` x) = ApSKI (ApSKI SndSKI e1) (buildExprSKILam x e2)
    | not (e2 `hasVarSKI` x) = ApSKI (ApSKI FstSKI (buildExprSKILam x e1)) e2
    | otherwise = ApSKI (ApSKI SSKI (buildExprSKILam x e1)) (buildExprSKILam x e2)
buildExprSKILam _ SSKI = ApSKI KSKI SSKI
buildExprSKILam _ KSKI = ApSKI KSKI KSKI
buildExprSKILam _ ISKI = ApSKI KSKI ISKI
buildExprSKILam _ FstSKI = ApSKI KSKI FstSKI
buildExprSKILam _ SndSKI = ApSKI KSKI SndSKI

unBuildExprSKI :: LamExprSKI -> LamExpr
unBuildExprSKI (VarSKI x) = Var x
unBuildExprSKI (ApSKI e1 e2) = Ap (unBuildExprSKI e1) (unBuildExprSKI e2)
unBuildExprSKI SSKI = readExpr "\\X Y Z -> (X Z) (Y Z)"
unBuildExprSKI KSKI = readExpr "\\X Y -> X"
unBuildExprSKI ISKI = readExpr "\\X -> X"
unBuildExprSKI FstSKI = readExpr "\\X Y Z -> (X Z) Y"
unBuildExprSKI SndSKI = readExpr "\\X Y Z -> X (Y Z)"

hasVarSKI :: (Eq a) => ExprSKI a -> a -> Bool
hasVarSKI SSKI _ = False
hasVarSKI KSKI _ = False
hasVarSKI ISKI _ = False
hasVarSKI (VarSKI y) x = x == y
hasVarSKI (ApSKI e1 e2) x = e1 `hasVarSKI` x || e2 `hasVarSKI` x
hasVarSKI FstSKI _ = False
hasVarSKI SndSKI _ = False

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

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
substitudeRef x argRef body = case body of
    (VarRef y)
        | y /= x -> return Nothing
        | otherwise -> do
            return $ Just argRef
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
--                    putStrLn "Have to find an unused variable name"
                    y' <- firstUnusedNameRef names [arg, e]
                    y'Ref <- newIORef $ VarRef y'
                    mer' <- substitudeRef y y'Ref e
                    e' <- readIORef $ fromJust mer'
                    mer'' <- substitudeRef x argRef e'
                    liftM Just $ newIORef $ LamRef y' $ fromJust mer''

hasVarRef :: LamExprRef -> Name -> IO Bool
hasVarRef (VarRef y) x = return $ x == y
hasVarRef (ApRef er1 er2) x = do
    e1 <- readIORef er1
    b1 <- hasVarRef e1 x
    if b1
    then return True
    else do
        e2 <- readIORef er2
        b2 <- hasVarRef e2 x
        return b2
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

buildExprRef :: LamExpr -> IO (IORef LamExprRef)
buildExprRef (Var x) = newIORef $ VarRef x
buildExprRef (Lam x expr) = do
    exprRef <- buildExprRef expr
    newIORef $ LamRef x exprRef
buildExprRef (Ap e1 e2) = do
    er1 <- buildExprRef e1
    er2 <- buildExprRef e2
    newIORef $ ApRef er1 er2

unBuildExprRef :: IORef LamExprRef -> IO LamExpr
unBuildExprRef er = do
    e <- readIORef er
    case e of
        (VarRef x) -> return $ Var x
        (LamRef x er') -> do
            e' <- unBuildExprRef er'
            return $ Lam x e'
        (ApRef er1 er2) -> do
            e1 <- unBuildExprRef er1
            e2 <- unBuildExprRef er2
            return $ Ap e1 e2

evalRef :: LamExpr -> IO LamExpr
evalRef expr = do
    exprRef <- buildExprRef expr
    go exprRef
  where
    go er = do
--        e' <- readIORef er
--        e <- unBuildLamExprRef e'
--        putStrLn $ showLamExpr e
        b <- evalStepRef er
        if b
        then go er
        else do
            e <- unBuildExprRef er
            return e

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

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
names = (map (\c -> [c]) "ABCDEFGHIJKLMNOPQRSTUVWXYZ" ++) . map ("VAR"++) $ map show ([1..] :: [Integer])

freeVariables :: LamExpr -> S.Set Name
freeVariables (Var x) = S.singleton x
freeVariables (Ap expr1 expr2) = S.union (freeVariables expr1) (freeVariables expr2)
freeVariables (Lam x expr) = S.delete x $ freeVariables expr

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

repeatEval :: LamExpr -> [LamExpr]
repeatEval expr = expr : case evalStep expr of
    Nothing -> []
    Just expr' -> repeatEval expr'

eval :: LamExpr -> LamExpr
eval e = case evalStep e of
    Nothing -> e
    Just e' -> eval e'

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

main :: IO ()
main = do
    exprStr <- getContents
    let expr = readExpr exprStr
    putStr exprStr
    putStrLn $ showExprSKI $ buildExprSKI $ expr
    putStrLn $ showExprSKI $ evalSKI . buildExprSKI $ expr
    e <- evalRef $ unBuildExprSKI . evalSKI . buildExprSKI $ expr
    putStrLn $ showExpr e
    e <- evalRef expr
    putStrLn $ showExpr e
--    putStrLn $ showLamExpr $ eval expr

showExprSKI :: LamExprSKI -> String
showExprSKI (VarSKI x) = x
showExprSKI (ApSKI e1 e2@(ApSKI _ _)) = showExprSKI e1 ++ " (" ++ showExprSKI e2 ++ ")"
showExprSKI (ApSKI e1 e2) = showExprSKI e1 ++ " " ++ showExprSKI e2
showExprSKI SSKI = "$S"
showExprSKI KSKI = "$K"
showExprSKI ISKI = "$I"
showExprSKI FstSKI = "$Fst"
showExprSKI SndSKI = "$Snd"

showExpr :: LamExpr -> String
showExpr (Var x) = x
showExpr (Ap expr1 expr2@(Ap _ _)) = showExpr expr1 ++ " (" ++ showExpr expr2 ++ ")"
showExpr (Ap expr1 expr2) = showExpr expr1 ++ " " ++ showExpr expr2
showExpr (Lam x expr) = showLamList [x] expr

readExpr :: String -> LamExpr
readExpr str = case parse pLamExpr (take 10 str) str of
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
    cs <- many1 (oneOf "+*!@%^&_=" <|> alphaNum)
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
showLamList xs expr = "(\\" ++ intercalate " " (reverse xs) ++ " -> " ++ showExpr expr ++ ")"

-- -}
