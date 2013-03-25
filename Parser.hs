module Parser where

import Control.Arrow
import Control.Monad
import Data.List
import Data.Maybe

import Data.IORef

import Text.Parsec
import Text.Parsec.String

-- import Debug.Trace
-- import System.IO.Unsafe
-- counter = unsafePerformIO $ newIORef 0
-- addCounter = (\x -> unsafePerformIO (modifyIORef counter (+1) >> (readIORef counter >>= \n -> print n) >> return x))

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

data ExprBFunc a
    = VarBFunc a
    | ApBFunc (ExprBFunc a) (ExprBFunc a)
    | LamBFunc (ExprBFunc a -> ExprBFunc a)

data ExprList a
    = VarList a
    | ApList (ExprList a) (ExprList a)
    | LamList [a] (ExprList a)

data ExprFunc a
    = VarFunc a
    | FuncFunc a
    | ApFunc (ExprFunc a) (ExprFunc a)

data GlobleFunction a = GlobleFunction [a] (ExprFunc a)

data ExprFuncRef a
    = VarFuncRef a
    | FuncFuncRef a
    | ApFuncRef (IORef (ExprFuncRef a)) (IORef (ExprFuncRef a))
    | IndFuncRef (IORef (ExprFuncRef a))

type Env a = [(a, GlobleFunction a)]

data GlobleFunctionCompiled a = GlobleFunctionCompiled Int ([IORef (ExprFuncCRef a)] -> IO (IORef (ExprFuncCRef a)))

data ExprFuncCRef a
    = VarFuncCRef a
    | FuncFuncCRef (IORef (GlobleFunctionCompiled a))
    | ApFuncCRef (IORef (ExprFuncCRef a)) (IORef (ExprFuncCRef a))
    | IndFuncCRef (IORef (ExprFuncCRef a))

type EnvC a = [(a, IORef (GlobleFunctionCompiled a))]

data ExprRef a
    = VarRef a
    | ApRef (IORef (ExprRef a)) (IORef (ExprRef a))
    | LamRef a (IORef (ExprRef a))
    | IndRef (IORef (ExprRef a))

data ExprSKI a
    = VarSKI a
    | ApSKI (ExprSKI a) (ExprSKI a)
    | SSKI
    | KSKI
    | ISKI
    | CSKI
    | BSKI
    deriving Eq

data ExprSKIRef a
    = VarSKIRef a
    | ApSKIRef (IORef (ExprSKIRef a)) (IORef (ExprSKIRef a))
    | SSKIRef
    | KSKIRef
    | ISKIRef
    | CSKIRef
    | BSKIRef
    | IndSKIRef (IORef (ExprSKIRef a))

type Name = String
type LamExpr = Expr Name
type LamExprList = ExprList Name
type LamExprFunc = ExprFunc Name
type LamExprFuncRef = ExprFuncRef Name
type LamExprFuncCRef = ExprFuncCRef Name
type LamEnv = Env Name
type LamEnvC = EnvC Name
type LamExprRef = ExprRef Name
type LamExprSKI = ExprSKI Name
type LamExprSKIRef = ExprSKIRef Name
type LamExprBruijn = ExprBruijn Name
type LamExprBFunc = ExprBFunc Name

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

buildExprBFunc :: Eq a => Expr a -> ExprBFunc a
buildExprBFunc = go [] . buildExprBruijn where
    go env (LamBruijn e) = LamBFunc $ \x -> go (x:env) e
    go env (BoundBruijn n) = env !! n
    go env (ApBruijn e1 e2) = ApBFunc (go env e1) (go env e2)
    go env (VarBruijn x) = VarBFunc x

unBuildExprBFunc :: LamExprBFunc -> LamExpr
unBuildExprBFunc = go variableNames where
    go vns (LamBFunc f) = Lam (head vns) $ go (tail vns) $ f (VarBFunc (head vns))
    go vns (ApBFunc e1 e2) = Ap (go vns e1) (go vns e2)
    go _ (VarBFunc x) = Var x

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

buildExprBruijn :: Eq a => Expr a -> ExprBruijn a
buildExprBruijn (Var x) = VarBruijn x
buildExprBruijn (Ap e1 e2) = ApBruijn (buildExprBruijn e1) (buildExprBruijn e2)
buildExprBruijn (Lam x e) = LamBruijn $ go 0 $ buildExprBruijn e where
    go n (LamBruijn b) = LamBruijn (go (n+1) b)
    go n (ApBruijn e1 e2) = ApBruijn (go n e1) (go n e2)
    go n (VarBruijn y) | y == x = BoundBruijn n
                       | otherwise = VarBruijn y
    go n (BoundBruijn i) = BoundBruijn i

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
    go n (VarBruijn x) = VarBruijn x
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

encodeBruijn :: Eq a => ExprBruijn a -> String
encodeBruijn (VarBruijn _) = error "encodeBruijn: Free Variables are not allowed."
encodeBruijn (BoundBruijn i) = replicate (i+1) '1' ++ "0"
encodeBruijn (LamBruijn e) = "00" ++ encodeBruijn e
encodeBruijn (ApBruijn e1 e2) = "01" ++ encodeBruijn e1 ++ encodeBruijn e2

encodeBoolList :: String -> String
encodeBoolList str = "(" ++ "(\\f b -> b f) (\\f b -> b f) \\define ->\n" ++
    "define (\\x y -> x) \\true ->\n" ++
    "define (\\x y -> y) \\false ->\n" ++
    "define (\\r z -> z true r) \\0 ->\n" ++
    "define (\\r z -> z false r) \\1 ->\n" ++
    gen "false" str "\n" ++
    ")"
  where
    gen r [] = (r ++)
    gen r ('0':ps) = ("0 (" ++) . gen r ps . (")" ++)
    gen r ('1':ps) = ("1 (" ++) . gen r ps . (")" ++)
    gen _ _ = error "encodeBoolList"

decodeBruijn :: Eq a => String -> ExprBruijn a
decodeBruijn = fst . go where
    go ('1':nstr) = first (BoundBruijn . pred . length) $ span' (=='1') nstr
    go ('0':'0':lstr) = first (LamBruijn) $ go lstr
    go ('0':'1':e1e2str) = ((ApBruijn e1 e2), str) where
        (e1, e2str) = go e1e2str
        (e2, str) = go e2str
    go (' ':str) = go str
    go ('\n':str) = go str
    go rest = error $ "decodeBruijn: " ++ rest
    span' _ [] = ([],[])
    span' p (x:xs) | p x = let (ys,zs) = span' p xs in (x:ys,zs)
                   | otherwise = ([x], xs)

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

buildExprSKIRef :: ExprSKI a -> IO (IORef (ExprSKIRef a))
buildExprSKIRef (VarSKI x) = newIORef $ VarSKIRef x
buildExprSKIRef (ApSKI e1 e2) = do
    er1 <- buildExprSKIRef e1
    er2 <- buildExprSKIRef e2
    newIORef $ ApSKIRef er1 er2
buildExprSKIRef SSKI = newIORef $ SSKIRef
buildExprSKIRef KSKI = newIORef $ KSKIRef
buildExprSKIRef ISKI = newIORef $ ISKIRef
buildExprSKIRef CSKI = newIORef $ CSKIRef
buildExprSKIRef BSKI = newIORef $ BSKIRef

unBuildExprSKIRef :: IORef (ExprSKIRef a) -> IO (ExprSKI a)
unBuildExprSKIRef er = do
    e <- readIORef er
    case e of
        VarSKIRef x -> return $ VarSKI x
        ApSKIRef er1 er2 -> do
            e1 <- unBuildExprSKIRef er1
            e2 <- unBuildExprSKIRef er2
            return $ ApSKI e1 e2
        SSKIRef -> return SSKI
        KSKIRef -> return KSKI
        ISKIRef -> return ISKI
        CSKIRef -> return CSKI
        BSKIRef -> return BSKI
        IndSKIRef er' -> unBuildExprSKIRef er'

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-


buildExprSKI :: (Eq a) => Expr a -> ExprSKI a
buildExprSKI (Var x) = VarSKI x
buildExprSKI (Ap e1 e2) = simplifySKI $ ApSKI (buildExprSKI e1) (buildExprSKI e2)
buildExprSKI (Lam x e) = simplifySKI $ buildExprSKILam x $ buildExprSKI e

buildExprSKILam :: (Eq a) => a -> ExprSKI a -> ExprSKI a
buildExprSKILam x (ApSKI (ApSKI SSKI KSKI) _) = ApSKI SSKI KSKI
buildExprSKILam x m | not (m `hasVarSKI` x) = ApSKI KSKI m
buildExprSKILam x (VarSKI _) = ISKI
buildExprSKILam x (ApSKI m (VarSKI y)) | x == y && not (m `hasVarSKI` x) = m
buildExprSKILam x (ApSKI (ApSKI (VarSKI y) m) (VarSKI z))
    | y == x && z == x = buildExprSKILam x $ ApSKI (ApSKI (ApSKI (ApSKI SSKI SSKI) KSKI) (VarSKI x)) m
{-
buildExprSKILam x (ApSKI m (ApSKI n l)) | isCombinator m && isCombinator n =
    buildExprSKILam x $ ApSKI (ApSKI (ApSKI SSKI (buildExprSKILam x m)) n) l
buildExprSKILam x (ApSKI (ApSKI m n) l) | isCombinator m && isCombinator l =
    buildExprSKILam x $ ApSKI (ApSKI (ApSKI SSKI m) (buildExprSKILam x l)) n
buildExprSKILam x (ApSKI (ApSKI m l) (ApSKI n l')) | l == l' && isCombinator m && isCombinator n =
    buildExprSKILam x $ ApSKI (ApSKI (ApSKI SSKI m) n) l
buildExprSKILam x (ApSKI m n) = ApSKI (ApSKI SSKI (buildExprSKILam x m)) (buildExprSKILam x n)
buildExprSKILam _ _ = error "buildExprSKILam"
-- -}
{-
buildExprSKILam x e | not (e `hasVarSKI` x) = ApSKI KSKI e
buildExprSKILam x (VarSKI y)
    | x == y = ISKI
    | otherwise = ApSKI KSKI (VarSKI y)
-- -}
buildExprSKILam x (ApSKI e1 e2)
    | not (e1 `hasVarSKI` x) = ApSKI (ApSKI BSKI e1) (buildExprSKILam x e2)
    | not (e2 `hasVarSKI` x) = ApSKI (ApSKI CSKI (buildExprSKILam x e1)) e2
    | otherwise = ApSKI (ApSKI SSKI (buildExprSKILam x e1)) (buildExprSKILam x e2)
buildExprSKILam _ _ = error "buildExprSKILam"

isCombinator :: ExprSKI a -> Bool
isCombinator SSKI = True
isCombinator KSKI = True
isCombinator ISKI = True
isCombinator CSKI = True
isCombinator BSKI = True
isCombinator (ApSKI e1 e2) = isCombinator e1 && isCombinator e2
isCombinator _ = False

simplifySKI :: Eq a => ExprSKI a -> ExprSKI a
simplifySKI x = fromMaybe x $ simplifySKIMaybe x

simplifySKIMaybe :: Eq a => ExprSKI a -> Maybe (ExprSKI a)
simplifySKIMaybe (ApSKI BSKI ISKI) = Just ISKI
simplifySKIMaybe (ApSKI (ApSKI BSKI x) ISKI) = Just $ simplifySKI x
simplifySKIMaybe (ApSKI (ApSKI CSKI BSKI) ISKI) = Just ISKI
simplifySKIMaybe (ApSKI (ApSKI m l) (ApSKI n l')) | l == l' = Just $ simplifySKI e where
    e = ApSKI (ApSKI (ApSKI SSKI m) n) l

simplifySKIMaybe (ApSKI ISKI x) = Just $ simplifySKI x
simplifySKIMaybe (ApSKI (ApSKI KSKI x) _) = Just $ simplifySKI x
simplifySKIMaybe (ApSKI (ApSKI (ApSKI CSKI x) y) z) = Just $ simplifySKI e where
    e = ApSKI (ApSKI x z) y
simplifySKIMaybe (ApSKI (ApSKI (ApSKI BSKI x) y) z) = Just $ simplifySKI e where
    e = ApSKI x (ApSKI y z)

simplifySKIMaybe (ApSKI e1 e2) = case simplifySKIMaybe e1 of
    Nothing -> case simplifySKIMaybe e2 of
        Nothing -> Nothing
        Just e2' -> Just . simplifySKI $ ApSKI e1 e2'
    Just e1' -> Just . simplifySKI $ ApSKI e1' e2
simplifySKIMaybe _ = Nothing

unBuildExprSKI :: LamExprSKI -> LamExpr
unBuildExprSKI (VarSKI x) = Var x
unBuildExprSKI (ApSKI e1 e2) = Ap (unBuildExprSKI e1) (unBuildExprSKI e2)
unBuildExprSKI SSKI = readExpr "\\X Y Z -> (X Z) (Y Z)"
unBuildExprSKI KSKI = readExpr "\\X Y -> X"
unBuildExprSKI ISKI = readExpr "\\X -> X"
unBuildExprSKI CSKI = readExpr "\\X Y Z -> (X Z) Y"
unBuildExprSKI BSKI = readExpr "\\X Y Z -> X (Y Z)"

hasVarSKI :: (Eq a) => ExprSKI a -> a -> Bool
hasVarSKI SSKI _ = False
hasVarSKI KSKI _ = False
hasVarSKI ISKI _ = False
hasVarSKI (VarSKI y) x = x == y
hasVarSKI (ApSKI e1 e2) x = e1 `hasVarSKI` x || e2 `hasVarSKI` x
hasVarSKI CSKI _ = False
hasVarSKI BSKI _ = False

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

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
        VarRef x -> return $ Var x
        LamRef x er' -> do
            e' <- unBuildExprRef er'
            return $ Lam x e'
        ApRef er1 er2 -> do
            e1 <- unBuildExprRef er1
            e2 <- unBuildExprRef er2
            return $ Ap e1 e2
        IndRef er' -> unBuildExprRef er'

hasVarRef :: LamExprRef -> Name -> IO Bool
hasVarRef (IndRef er) x = readIORef er >>= \e -> hasVarRef e x
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

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

buildLiftedExpr :: LamExprList -> (LamExprFunc, LamEnv)
buildLiftedExpr = snd . buildEnvGen functionNames [] . eliminatingFreeVariables

functionNames :: [Name]
functionNames = map ("$Func" ++) $ map show ([1..] :: [Integer])

variableNames :: [Name]
variableNames = map ("$Var" ++) $ map show ([1..] :: [Integer])

buildEnvGen :: [Name] -> LamEnv -> LamExprList -> ([Name], (LamExprFunc, LamEnv))
buildEnvGen fns env (VarList x) = (fns, (VarFunc x, env))
buildEnvGen fns env (ApList e1 e2) = (fns'', (ApFunc e1' e2', env'')) where
    (fns', (e1', env')) = buildEnvGen fns env e1
    (fns'', (e2', env'')) = buildEnvGen fns' env' e2
buildEnvGen fns env (LamList xs e) = (tail fns', (FuncFunc (head fns'), (head fns', GlobleFunction xs e'):env')) where
    (fns', (e', env')) = buildEnvGen fns env e

eliminatingFreeVariables :: LamExprList -> LamExprList
eliminatingFreeVariables (VarList x) = VarList x
eliminatingFreeVariables (ApList e1 e2) = ApList (eliminatingFreeVariables e1) (eliminatingFreeVariables e2)
eliminatingFreeVariables (LamList xs e) = foldl ApList b $ map VarList xs' where
    b = LamList (xs' ++ xs) e'
    xs' = freeVariablesList e' \\ xs
    e' = eliminatingFreeVariables e

freeVariablesList :: LamExprList -> [Name]
freeVariablesList (VarList x) = [x]
freeVariablesList (ApList e1 e2) = union (freeVariablesList e1) (freeVariablesList e2)
freeVariablesList (LamList xs e) = freeVariablesList e \\ xs

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

buildExprList :: LamExpr -> LamExprList
buildExprList (Var x) = VarList x
buildExprList (Ap e1 e2) = ApList (buildExprList e1) (buildExprList e2)
buildExprList (Lam x e) = buildExprListLam (x:) e

buildExprListLam :: ([Name] -> [Name]) -> LamExpr -> LamExprList
buildExprListLam gxs (Lam x e) = buildExprListLam (gxs . (x:)) e
buildExprListLam gxs e = LamList (gxs []) $ buildExprList e

unBuildExprList :: LamExprList -> LamExpr
unBuildExprList (VarList x) = Var x
unBuildExprList (ApList e1 e2) = Ap (unBuildExprList e1) (unBuildExprList e2)
unBuildExprList (LamList xs e) = genLamList xs $ unBuildExprList e

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

buildExprLiftedRef :: LamExprFunc -> IO (IORef LamExprFuncRef)
buildExprLiftedRef (VarFunc x) = newIORef (VarFuncRef x)
buildExprLiftedRef (FuncFunc x) = newIORef (FuncFuncRef x)
buildExprLiftedRef (ApFunc e1 e2) = do
    er1 <- buildExprLiftedRef e1
    er2 <- buildExprLiftedRef e2
    newIORef $ ApFuncRef er1 er2

buildExprLiftedCRef :: LamEnv -> LamExprFunc -> IO (IORef LamExprFuncCRef)
buildExprLiftedCRef env e = do
    envC <- liftM (zip (map fst env)) . mapM newIORef $ replicate len (GlobleFunctionCompiled 0 (return . head))
    mapM_ (compileF envC) env
    compile envC e
  where
    len = length env
    compile _    (VarFunc x) = newIORef $ VarFuncCRef x
    compile envC (FuncFunc f) = newIORef . FuncFuncCRef . fromJust $ lookup f envC
    compile envC (ApFunc e1 e2) = do
        er1 <- compile envC e1
        er2 <- compile envC e2
        newIORef $ ApFuncCRef er1 er2
    compileF envC (f, GlobleFunction xs fe) = writeIORef (fromJust $ lookup f envC) $
        GlobleFunctionCompiled (length xs) $ genFunc envC xs fe
    genFunc _    xs (VarFunc x) = return . (!! n) where
        n = length xs - 1 - (fromJust $ elemIndex x $ reverse xs)
    genFunc envC _  (FuncFunc f) = const fr where
        fr = newIORef $ FuncFuncCRef (fromJust $ lookup f envC)
    genFunc envC xs (ApFunc e1 e2) = \args -> do
        er1 <- f1 args
        er2 <- f2 args
        newIORef $ ApFuncCRef er1 er2
      where
        f1 = genFunc envC xs e1
        f2 = genFunc envC xs e2

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

names :: [Name]
names = (map (\c -> [c]) "ABCDEFGHIJKLMNOPQRSTUVWXYZ" ++) . map ("VAR"++) $ map show ([1..] :: [Integer])

firstUnusedName :: [Name] -> [LamExpr] -> Name
firstUnusedName [] _ = error "firstUnusedName"
firstUnusedName (n:ns) exprs
    | all (not . (`hasVar` n)) exprs = n
    | otherwise = firstUnusedName ns exprs

freeVariables :: LamExpr -> [Name]
freeVariables (Var x) = [x]
freeVariables (Ap e1 e2) = union (freeVariables e1) (freeVariables e2)
freeVariables (Lam x e) = freeVariables e \\ [x]

hasVar :: LamExpr -> Name -> Bool
hasVar (Var y) x = x == y
hasVar (Ap expr1 expr2) x = expr1 `hasVar` x || expr2 `hasVar` x
hasVar (Lam y expr) x
    | x == y = False
    | otherwise = expr `hasVar` x

simplifyExpr :: LamExpr -> LamExpr
simplifyExpr (Var x) = (Var x)
simplifyExpr (Ap e1 e2) = Ap (simplifyExpr e1) (simplifyExpr e2)
simplifyExpr (Lam x (Ap e1 (Var y))) | not (e1 `hasVar` x) && x == y = simplifyExpr e1
simplifyExpr (Lam x e) = Lam x $ simplifyExpr e

buildBinaryList :: String -> LamExpr
buildBinaryList [] = readExpr "\\x y -> y"
buildBinaryList ('0':str) = Lam "z" $ Ap (Ap (Var "z") (readExpr "\\x y -> x")) (buildBinaryList str)
buildBinaryList ('1':str) = Lam "z" $ Ap (Ap (Var "z") (readExpr "\\x y -> y")) (buildBinaryList str)
buildBinaryList _ = error "buildBinaryList"

unBuildBinaryList :: LamExpr -> String
unBuildBinaryList (Lam x (Lam y (Var xy))) | xy == y = []
unBuildBinaryList (Lam z (Ap (Ap (Var z') b) bs)) = check b : unBuildBinaryList bs where
    check (Lam x (Lam y (Var xy))) | xy == x = '0'
                                   | xy == y = '1'
    check _ = error "unBuildBinaryList"
unBuildBinaryList _ = "unBuildBinaryList"

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

showExprSKI :: LamExprSKI -> String
showExprSKI (VarSKI x) = x
showExprSKI (ApSKI e1 e2@(ApSKI _ _)) = showExprSKI e1 ++ " (" ++ showExprSKI e2 ++ ")"
showExprSKI (ApSKI e1 e2) = showExprSKI e1 ++ " " ++ showExprSKI e2
showExprSKI SSKI = "$S"
showExprSKI KSKI = "$K"
showExprSKI ISKI = "$I"
showExprSKI CSKI = "$C"
showExprSKI BSKI = "$B"

showExpr :: LamExpr -> String
showExpr (Var x) = x
showExpr (Ap expr1 expr2@(Ap _ _)) = showExpr expr1 ++ " (" ++ showExpr expr2 ++ ")"
showExpr (Ap expr1 expr2) = showExpr expr1 ++ " " ++ showExpr expr2
showExpr (Lam x expr) = showLamList [x] expr

showLiftedExpr :: (LamExprFunc, LamEnv) -> String
showLiftedExpr (e, env) = showEnv env ++ "\n" ++ showExprFunc e ++ "\n"

showExprFunc :: LamExprFunc -> String
showExprFunc (VarFunc x) = x
showExprFunc (FuncFunc x) = x
showExprFunc (ApFunc e1 e2@(ApFunc _ _)) = showExprFunc e1 ++ " (" ++ showExprFunc e2 ++ ")"
showExprFunc (ApFunc e1 e2) = showExprFunc e1 ++ " " ++ showExprFunc e2

showEnv :: LamEnv -> String
showEnv = unlines . map go where
    go (fn, GlobleFunction xs e) = fn ++ " " ++ intercalate " " xs ++ " = " ++ showExprFunc e

readExpr :: String -> LamExpr
readExpr str = case parse pLamExpr (take 10 str) str of
    Left e -> error $ show e
    Right expr -> expr

pLamExpr :: Parser LamExpr
pLamExpr = chainl1 (try $ pSpaces >> (pParentheseExpr <|> pVar <|> pLam)) (return Ap)

pSpaces :: Parser ()
pSpaces = spaces >> (try pComment <|> return ())

pComment :: Parser ()
pComment = do
    _ <- string ";" <|> try (string "--")
    _ <- many $ noneOf "\n"
    _ <- char '\n'
    pSpaces

pParentheseExpr :: Parser LamExpr
pParentheseExpr = do
    _ <- char '('
    expr <- pLamExpr
    pSpaces
    _ <- char ')'
    return expr

pVar :: Parser LamExpr
pVar = do
    x <- pName
    return $ Var x

pName :: Parser Name
pName = do
    cs <- many1 (oneOf "+-*/<>=!@%&_?" <|> alphaNum)
    if cs `elem` ["->", "--"]
        then fail ""
        else return cs

pLam :: Parser LamExpr
pLam = do
    _ <- char '\\'
    pSpaces
    xs <- many1 (try $ pSpaces >> pName)
    pSpaces
    _ <- try $ string "->"
    pSpaces
    expr <- pLamExpr
    return $ genLamList xs expr

genLamList :: [Name] -> LamExpr -> LamExpr
genLamList [] expr = expr
genLamList (x:xs) expr = Lam x $ genLamList xs expr

showLamList :: [Name] -> LamExpr -> String
showLamList xs (Lam x expr) = showLamList (x:xs) expr
showLamList xs expr = "(\\" ++ intercalate " " (reverse xs) ++ " -> " ++ showExpr expr ++ ")"
