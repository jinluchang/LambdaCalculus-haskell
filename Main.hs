module Main where

import Control.Monad
import Data.List
import Data.Maybe

import Data.IORef

import Text.Parsec
import Text.Parsec.String

import System.Environment

data Expr a
    = Var a
    | Ap (Expr a) (Expr a)
    | Lam a (Expr a)
    deriving (Eq, Show)

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
type LamEnv = Env Name
type LamExprRef = ExprRef Name
type LamExprSKI = ExprSKI Name
type LamExprSKIRef = ExprSKIRef Name


-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalSKIRefS :: LamExprSKI -> IO LamExprSKI
evalSKIRefS e = do
    er <- buildExprSKIRef e
    er' <- evalStackSKIRef [er] []
    unBuildExprSKIRef er'

evalStackSKIRef :: [IORef LamExprSKIRef] -> [IORef LamExprSKIRef] -> IO (IORef LamExprSKIRef)
evalStackSKIRef (n:ns) as = readIORef n >>= \ne -> case ne of
    VarSKIRef x -> do
        as' <- mapM (\a -> evalStackSKIRef [a] []) as
        n' <- foldM (\n' a -> newIORef $ ApSKIRef n' a) n as'
        return n'
    ApSKIRef n0 a -> evalStackSKIRef (n0:n:ns) (a:as)
    IndSKIRef n' -> case (ns,as) of
        ([], []) -> evalStackSKIRef [n'] []
        (n1:_, a1:_) -> do
            writeIORef n1 $ ApSKIRef n' a1
            evalStackSKIRef (n':ns) as
        _ -> error "evalStackSKIRef"
    ISKIRef -> case (ns,as) of
        ([], []) -> return n
        (n1:n1s, a1:a1s) -> do
            writeIORef n1 $ IndSKIRef a1
            evalStackSKIRef (a1:n1s) a1s
        _ -> error "evalStackSKIRef"
    KSKIRef -> case (ns,as) of
        ([], []) -> return n
        ([n1], [a1]) -> do
            a1' <- evalStackSKIRef [a1] []
            writeIORef n1 $ ApSKIRef n a1'
            return n1
        (n1:n2:n2s, a1:a2:a2s) -> do
            writeIORef n2 $ IndSKIRef a1
            evalStackSKIRef (a1:n2s) a2s
        _ -> error "evalStackSKIRef"
    SSKIRef -> case (ns,as) of
        ([], []) -> return n
        ([n1], [a1]) -> do
            a1' <- evalStackSKIRef [a1] []
            writeIORef n1 $ ApSKIRef n a1'
            return n1
        ([n1,n2], [a1,a2]) -> do
            a1' <- evalStackSKIRef [a1] []
            a2' <- evalStackSKIRef [a2] []
            writeIORef n1 $ ApSKIRef n a1'
            writeIORef n2 $ ApSKIRef n1 a2'
            return n2
        (n1:n2:n3:n3s, a1:a2:a3:a3s) -> do
            n2' <- newIORef $ ApSKIRef a1 a3
            a3' <- newIORef $ ApSKIRef a2 a3
            writeIORef n3 $ ApSKIRef n2' a3'
            evalStackSKIRef (a1:n2':n3:n3s) (a3:a3':a3s)
        _ -> error "evalStackSKIRef"
    CSKIRef -> case (ns,as) of
        ([], []) -> return n
        ([n1], [a1]) -> do
            a1' <- evalStackSKIRef [a1] []
            writeIORef n1 $ ApSKIRef n a1'
            return n1
        ([n1,n2], [a1,a2]) -> do
            a1' <- evalStackSKIRef [a1] []
            a2' <- evalStackSKIRef [a2] []
            writeIORef n1 $ ApSKIRef n a1'
            writeIORef n2 $ ApSKIRef n1 a2'
            return n2
        (n1:n2:n3:n3s, a1:a2:a3:a3s) -> do
            n2' <- newIORef $ ApSKIRef a1 a3
            writeIORef n3 $ ApSKIRef n2' a2
            evalStackSKIRef (a1:n2':n3:n3s) (a3:a2:a3s)
        _ -> error "evalStackSKIRef"
    BSKIRef -> case (ns,as) of
        ([], []) -> return n
        ([n1], [a1]) -> do
            a1' <- evalStackSKIRef [a1] []
            writeIORef n1 $ ApSKIRef n a1'
            return n1
        ([n1,n2], [a1,a2]) -> do
            a1' <- evalStackSKIRef [a1] []
            a2' <- evalStackSKIRef [a2] []
            writeIORef n1 $ ApSKIRef n a1'
            writeIORef n2 $ ApSKIRef n1 a2'
            return n2
        (n1:n2:n3:n3s, a1:a2:a3:a3s) -> do
            a3' <- newIORef $ ApSKIRef a2 a3
            writeIORef n3 $ ApSKIRef a1 a3'
            evalStackSKIRef (a1:n3:n3s) (a3':a3s)
        _ -> error "evalStackSKIRef"
evalStackSKIRef _ _ = error "evalStackSKIRef"

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

evalStepSKI :: LamExprSKI -> Maybe LamExprSKI
evalStepSKI SSKI = Nothing
evalStepSKI KSKI = Nothing
evalStepSKI ISKI = Nothing
evalStepSKI CSKI = Nothing
evalStepSKI BSKI = Nothing
evalStepSKI (VarSKI _) = Nothing
evalStepSKI (ApSKI ISKI e) = Just e
evalStepSKI (ApSKI (ApSKI KSKI e1) _) = Just e1
evalStepSKI (ApSKI (ApSKI (ApSKI SSKI e1) e2) e3) = Just $ ApSKI (ApSKI e1 e3) (ApSKI e2 e3)
evalStepSKI (ApSKI (ApSKI (ApSKI CSKI e1) e2) e3) = Just $ ApSKI (ApSKI e1 e3) e2
evalStepSKI (ApSKI (ApSKI (ApSKI BSKI e1) e2) e3) = Just $ ApSKI e1 (ApSKI e2 e3)
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
buildExprSKI (Ap e1 e2) = simplifySKI $ ApSKI (buildExprSKI e1) (buildExprSKI e2)
buildExprSKI (Lam x e) = simplifySKI $ buildExprSKILam x $ buildExprSKI e

buildExprSKILam :: (Eq a) => a -> ExprSKI a -> ExprSKI a
buildExprSKILam x e | not (e `hasVarSKI` x) = ApSKI KSKI e
buildExprSKILam x (VarSKI y)
    | x == y = ISKI
    | otherwise = ApSKI KSKI (VarSKI y)
buildExprSKILam x (ApSKI e1 e2)
    | not (e1 `hasVarSKI` x) = ApSKI (ApSKI BSKI e1) (buildExprSKILam x e2)
    | not (e2 `hasVarSKI` x) = ApSKI (ApSKI CSKI (buildExprSKILam x e1)) e2
    | otherwise = ApSKI (ApSKI SSKI (buildExprSKILam x e1)) (buildExprSKILam x e2)
buildExprSKILam _ SSKI = ApSKI KSKI SSKI
buildExprSKILam _ KSKI = ApSKI KSKI KSKI
buildExprSKILam _ ISKI = ApSKI KSKI ISKI
buildExprSKILam _ CSKI = ApSKI KSKI CSKI
buildExprSKILam _ BSKI = ApSKI KSKI BSKI

simplifySKI :: ExprSKI a -> ExprSKI a
simplifySKI x = fromMaybe x $ simplifySKIMaybe x

simplifySKIMaybe :: ExprSKI a -> Maybe (ExprSKI a)
simplifySKIMaybe (ApSKI BSKI ISKI) = Just ISKI
simplifySKIMaybe (ApSKI (ApSKI BSKI x) ISKI) = Just . fromMaybe x $ simplifySKIMaybe x
simplifySKIMaybe (ApSKI (ApSKI CSKI BSKI) ISKI) = Just ISKI

simplifySKIMaybe (ApSKI ISKI x) = Just . fromMaybe x $ simplifySKIMaybe x
simplifySKIMaybe (ApSKI (ApSKI KSKI x) _) = Just . fromMaybe x $ simplifySKIMaybe x
simplifySKIMaybe (ApSKI (ApSKI (ApSKI CSKI x) y) z) = Just . fromMaybe e $ simplifySKIMaybe e where
    e = ApSKI (ApSKI x z) y
simplifySKIMaybe (ApSKI (ApSKI (ApSKI BSKI x) y) z) = Just . fromMaybe e $ simplifySKIMaybe e where
    e = ApSKI x (ApSKI y z)

simplifySKIMaybe (ApSKI e1 e2) = case simplifySKIMaybe e1 of
    Nothing -> case simplifySKIMaybe e2 of
        Nothing -> Nothing
        Just e2' -> Just . fromMaybe (ApSKI e1 e2') $ simplifySKIMaybe (ApSKI e1 e2')
    Just e1' -> Just . fromMaybe (ApSKI e1' e2) $ simplifySKIMaybe (ApSKI e1' e2)
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

evalRefS :: LamExpr -> IO LamExpr
evalRefS expr = do
    exprRef <- buildExprRef expr
    exprRef' <- evalStackRef [exprRef] []
    unBuildExprRef exprRef'

evalStackRef :: [IORef LamExprRef] -> [IORef LamExprRef] -> IO (IORef LamExprRef)
evalStackRef (n:ns) as = readIORef n >>= \ne -> case ne of
    VarRef x -> do
        as' <- mapM (\a -> evalStackRef [a] []) as
        foldM (\n' (n'',a) -> writeIORef n'' (ApRef n' a) >> return n'') n $ zip ns as'
    ApRef n0 a -> evalStackRef (n0:n:ns) (a:as)
    IndRef n' -> case (ns,as) of
        ([], []) -> evalStackRef [n'] []
        (n1:_, a1:_) -> do
            writeIORef n1 $ ApRef n' a1
            evalStackRef (n':ns) as
        _ -> error "evalStackRef"
    LamRef x er -> case (ns,as) of
        ([], []) -> do
            er' <- evalStackRef [er] []
            writeIORef n $ LamRef x er'
            return n
        (n1:n1s, a1:a1s) -> do
            e <- readIORef er
            mn1' <- substitudeRef x a1 e
            case mn1' of
                Nothing -> do
                    writeIORef n1 $ IndRef er
                    evalStackRef (er:n1s) a1s
                Just n1' -> do
                    writeIORef n1 $ IndRef n1'
                    evalStackRef (n1':n1s) a1s
        _ -> error "evalStackRef"
evalStackRef _ _ = error "evalStackRef"

substitudeRef :: Name -> IORef LamExprRef -> LamExprRef -> IO (Maybe (IORef LamExprRef))
substitudeRef x argRef body = case body of
    IndRef er -> do
        e <- readIORef er
        mer <- substitudeRef x argRef e
        case mer of
            Nothing -> return Nothing
            Just er' -> return $ Just er'
    VarRef y
        | y /= x -> return Nothing
        | otherwise -> do
            return $ Just argRef
    ApRef er1 er2 -> do
        e1 <- readIORef er1
        mer1 <- substitudeRef x argRef e1
        e2 <- readIORef er2
        mer2 <- substitudeRef x argRef e2
        case (mer1, mer2) of
            (Nothing, Nothing) -> return Nothing
            (Just er1', Nothing) -> liftM Just $ newIORef $ ApRef er1' er2
            (Nothing, Just er2') -> liftM Just $ newIORef $ ApRef er1 er2'
            (Just er1', Just er2') -> liftM Just $ newIORef $ ApRef er1' er2'
    LamRef y er
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

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalLiftedRefS :: LamExpr -> IO LamExpr
evalLiftedRefS e = do
    er <- buildExprLiftedRef el
    el' <- evalStackLiftedRef variableNames env [er] []
    return $ unBuildExprList el'
  where
    (el, env) = buildLiftedExpr $ buildExprList e

evalStackLiftedRef :: [Name] -> LamEnv -> [IORef LamExprFuncRef] -> [IORef LamExprFuncRef] -> IO LamExprList
evalStackLiftedRef vns env (n:ns) as = readIORef n >>= \ne -> case ne of
    IndFuncRef n' -> case (ns,as) of
        ([], []) -> evalStackLiftedRef vns env [n'] []
        (n1:n1s, a1:a1s) -> do
            writeIORef n1 $ ApFuncRef n' a1
            evalStackLiftedRef vns env (n':ns) as
        _ -> error "evalStackLiftedRef"
    VarFuncRef x -> do
        as' <- mapM (\a -> evalStackLiftedRef vns env [a] []) as
        return $ foldl (\n' a -> ApList n' a) (VarList x) as'
    ApFuncRef n0 a -> evalStackLiftedRef vns env (n0:n:ns) (a:as)
    FuncFuncRef f -> if diff <= 0
        then do
            n' <- mkInstanceRef xs body $ take argc as
            writeIORef (ns !! (argc-1)) $ IndFuncRef n'
            if diff < 0 then writeIORef (ns !! argc) $ ApFuncRef n' (as !! argc) else return ()
            evalStackLiftedRef vns env (n' : drop argc ns) (drop argc as)
        else do
            as' <- mapM (newIORef . VarFuncRef) (take diff vns)
            n' <- mkInstanceRef xs body $ as ++ as'
            e <- evalStackLiftedRef (drop diff vns) env [n'] []
            return $ LamList (take diff vns) e
      where
        diff = argc - length as
        argc = length xs
        GlobleFunction xs body = fromJust $ lookup f env
evalStackLiftedRef _ _ _ _ = error "evalStackLiftedRef"

mkInstanceRef :: [Name] -> LamExprFunc -> [IORef LamExprFuncRef] -> IO (IORef LamExprFuncRef)
mkInstanceRef xs body as = go body where
    env = zip xs as
    go (FuncFunc f) = newIORef $ FuncFuncRef f
    go (VarFunc x) = return . fromJust $ lookup x env
    go (ApFunc e1 e2) = do
        e1' <- go e1
        e2' <- go e2
        newIORef $ ApFuncRef e1' e2'

buildExprLiftedRef :: LamExprFunc -> IO (IORef LamExprFuncRef)
buildExprLiftedRef (VarFunc x) = newIORef (VarFuncRef x)
buildExprLiftedRef (FuncFunc x) = newIORef (FuncFuncRef x)
buildExprLiftedRef (ApFunc e1 e2) = do
    er1 <- buildExprLiftedRef e1
    er2 <- buildExprLiftedRef e2
    newIORef $ ApFuncRef er1 er2

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalLifted :: LamExpr -> LamExpr
evalLifted e = unBuildExprList $ evalStackLifted variableNames env [el] [] where
    (el, env) = buildLiftedExpr $ buildExprList e

evalStackLifted :: [Name] -> LamEnv -> [LamExprFunc] -> [LamExprFunc] -> LamExprList
evalStackLifted vns env (n:ns) as = case n of
    VarFunc x -> foldl (\n' a -> ApList n' a) (VarList x) $ map (\a -> evalStackLifted vns env [a] []) as
    ApFunc n0 a -> evalStackLifted vns env (n0:n:ns) (a:as)
    FuncFunc f -> if diff <= 0
        then evalStackLifted vns env ((mkInstance xs body $ take argc as) : drop argc ns) (drop argc as)
        else LamList (take diff vns) $
            evalStackLifted (drop diff vns) env [mkInstance xs body $ as ++ map VarFunc (take diff vns)] []
      where
        diff = argc - length as
        argc = length xs
        GlobleFunction xs body = fromJust $ lookup f env
evalStackLifted _ _ _ _ = error "evalStackLifted"

mkInstance :: [Name] -> LamExprFunc -> [LamExprFunc] -> LamExprFunc
mkInstance xs body as = go body where
    env = zip xs as
    go (VarFunc x) = fromJust $ lookup x env
    go (ApFunc e1 e2) = ApFunc (go e1) (go e2)
    go (FuncFunc f) = FuncFunc f

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
    xs' = freeVariables e' \\ xs
    e' = eliminatingFreeVariables e

freeVariables :: LamExprList -> [Name]
freeVariables (VarList x) = [x]
freeVariables (ApList e1 e2) = union (freeVariables e1) (freeVariables e2)
freeVariables (LamList xs e) = freeVariables e \\ xs

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
    args <- getArgs
    exprStr <- getContents
    let expr = readExpr exprStr
    putStrLn exprStr
    if "-v" `elem` args then putStrLn $ showLiftedExpr . buildLiftedExpr . buildExprList $ expr else return ()
--    if "-v" `elem` args then putStrLn $ showExpr expr else return ()
--    if "-v" `elem` args then putStrLn . showExprSKI $ simplifySKI . buildExprSKI $ expr else return ()
--    eSKI <- evalSKIRefS . simplifySKI . buildExprSKI $ expr
--    if "-v" `elem` args then putStrLn $ showExprSKI . simplifySKI $ eSKI else return ()
--    e <- evalRefS $ unBuildExprSKI . simplifySKI $ eSKI
--    putStrLn $ showExpr e
    e' <- evalLiftedRefS expr
    putStrLn $ showExpr e'
--    putStrLn $ showExpr . evalLifted $ expr

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
