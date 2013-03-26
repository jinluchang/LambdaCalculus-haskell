module Evaluation where

import Parser

import Control.Monad
import Data.Maybe

import Data.IORef

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalBFunc :: LamExpr -> LamExpr
evalBFunc = unBuildExprBFunc . nf . buildExprBFunc where
    nf (LamBFunc f) = LamBFunc (nf . f)
    nf (ApBFunc fun arg) = case nf fun of
        LamBFunc f -> f $ nf arg
        fun' -> ApBFunc fun' $ nf arg
    nf (VarBFunc x) = VarBFunc x

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalSKIRefSP :: LamExpr -> IO LamExpr
evalSKIRefSP e = do
    er <- buildExprSKIRef . buildExprSKI $ e
    evalStackSKIPadRef variableNames [er] []

evalStackSKIPadRef :: [Name] -> [IORef LamExprSKIRef] -> [IORef LamExprSKIRef] -> IO LamExpr
evalStackSKIPadRef vns (n:ns) as = readIORef n >>= \ne -> case ne of
    VarSKIRef x -> do
        as' <- mapM (\a -> evalStackSKIPadRef vns [a] []) as
        return $ foldl (\ne' a -> Ap ne' a) (Var x) as'
    ApSKIRef n0 a -> evalStackSKIPadRef vns (n0:n:ns) (a:as)
    IndSKIRef n' -> case (ns,as) of
        ([], []) -> evalStackSKIPadRef vns [n'] []
        (n1:_, a1:_) -> do
            writeIORef n1 $ ApSKIRef n' a1
            evalStackSKIPadRef vns (n':ns) as
        _ -> error "evalStackSKIPadRef"
    ISKIRef -> case (ns,as) of
        ([], []) -> return . readExpr $ "\\X -> X"
        (n1:n1s, a1:a1s) -> do
            writeIORef n1 $ IndSKIRef a1
            evalStackSKIPadRef vns (a1:n1s) a1s
        _ -> error "evalStackSKIPadRef"
    KSKIRef -> case (ns,as) of
        ([], []) -> return . readExpr $ "\\X _ -> X"
        ([n1], [a1]) -> do
            a1' <- evalStackSKIPadRef (tail vns) [a1] []
            return $ Lam "_" a1'
        (n1:n2:n2s, a1:a2:a2s) -> do
            writeIORef n2 $ IndSKIRef a1
            evalStackSKIPadRef vns (a1:n2s) a2s
        _ -> error "evalStackSKIPadRef"
    SSKIRef -> case (ns,as) of
        ([], []) -> return . readExpr $ "\\X Y Z -> (X Z) (Y Z)"
        ([n1], [a1]) -> do
            a2 <- newIORef $ VarSKIRef $ vns !! 0
            a3 <- newIORef $ VarSKIRef $ vns !! 1
            n2' <- newIORef $ ApSKIRef a1 a3
            a3' <- newIORef $ ApSKIRef a2 a3
            n3' <- newIORef $ ApSKIRef n2' a3'
            e' <- evalStackSKIPadRef (drop 2 vns) [a1,n2',n3'] [a3,a3']
            return . Lam (vns !! 0) . Lam (vns !! 1) $ e'
        ([n1,n2], [a1,a2]) -> do
            a3 <- newIORef $ VarSKIRef $ head vns
            n2' <- newIORef $ ApSKIRef a1 a3
            a3' <- newIORef $ ApSKIRef a2 a3
            n3' <- newIORef $ ApSKIRef n2' a3'
            e' <- evalStackSKIPadRef (tail vns) [a1,n2',n3'] [a3,a3']
            return . Lam (head vns) $ e'
        (n1:n2:n3:n3s, a1:a2:a3:a3s) -> do
            n2' <- newIORef $ ApSKIRef a1 a3
            a3' <- newIORef $ ApSKIRef a2 a3
            writeIORef n3 $ ApSKIRef n2' a3'
            evalStackSKIPadRef vns (a1:n2':n3:n3s) (a3:a3':a3s)
        _ -> error "evalStackSKIPadRef"
    CSKIRef -> case (ns,as) of
        ([], []) -> return . readExpr $ "\\X Y Z -> (X Z) Y"
        ([n1], [a1]) -> do
            a2 <- newIORef $ VarSKIRef $ vns !! 0
            a3 <- newIORef $ VarSKIRef $ vns !! 1
            n2' <- newIORef $ ApSKIRef a1 a3
            n3' <- newIORef $ ApSKIRef n2' a2
            e' <- evalStackSKIPadRef (drop 2 vns) [a1,n2',n3'] [a3,a2]
            return . Lam (vns !! 0) . Lam (vns !! 1) $ e'
        ([n1,n2], [a1,a2]) -> do
            a3 <- newIORef $ VarSKIRef $ head vns
            n2' <- newIORef $ ApSKIRef a1 a3
            n3' <- newIORef $ ApSKIRef n2' a2
            e' <- evalStackSKIPadRef (tail vns) [a1,n2',n3'] [a3,a2]
            return . Lam (head vns) $ e'
        (n1:n2:n3:n3s, a1:a2:a3:a3s) -> do
            n2' <- newIORef $ ApSKIRef a1 a3
            writeIORef n3 $ ApSKIRef n2' a2
            evalStackSKIPadRef vns (a1:n2':n3:n3s) (a3:a2:a3s)
        _ -> error "evalStackSKIPadRef"
    BSKIRef -> case (ns,as) of
        ([], []) -> return . readExpr $ "\\X Y Z -> X (Y Z)"
        ([n1], [a1]) -> do
            a2 <- newIORef $ VarSKIRef $ vns !! 0
            a3 <- newIORef $ VarSKIRef $ vns !! 1
            a3' <- newIORef $ ApSKIRef a2 a3
            n3' <- newIORef $ ApSKIRef a1 a3'
            e' <- evalStackSKIPadRef (drop 2 vns) [a1,n3'] [a3']
            return . Lam (vns !! 0) . Lam (vns !! 1) $ e'
        ([n1,n2], [a1,a2]) -> do
            a3 <- newIORef $ VarSKIRef $ head vns
            a3' <- newIORef $ ApSKIRef a2 a3
            n3' <- newIORef $ ApSKIRef a1 a3'
            e' <- evalStackSKIPadRef (tail vns) [a1,n3'] [a3']
            return . Lam (head vns) $ e'
        (n1:n2:n3:n3s, a1:a2:a3:a3s) -> do
            a3' <- newIORef $ ApSKIRef a2 a3
            writeIORef n3 $ ApSKIRef a1 a3'
            evalStackSKIPadRef vns (a1:n3:n3s) (a3':a3s)
        _ -> error "evalStackSKIPadRef"
evalStackSKIPadRef _ _ _ = error "evalStackSKIPadRef"

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalSKIRefS :: LamExpr -> IO LamExpr
evalSKIRefS e = do
    er <- buildExprSKIRef . buildExprSKI $ e
    er' <- evalStackSKIRef [er] []
    e' <- liftM unBuildExprSKI $ unBuildExprSKIRef er'
    evalRefS e'

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

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalSKI :: LamExpr -> LamExpr
evalSKI = eval . unBuildExprSKI . go . buildExprSKI where
    go e = case evalStepSKI e of
        Nothing -> e
        Just e' -> go e'

repeatEvalSKI :: LamExprSKI -> [LamExprSKI]
repeatEvalSKI expr = expr : case evalStepSKI expr of
    Nothing -> []
    Just expr' -> repeatEvalSKI expr'

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

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalLiftedRefS :: LamExpr -> IO LamExpr
evalLiftedRefS e = do
    er <- buildExprLiftedRef ef
    el' <- evalStackLiftedRef variableNames env [er] []
    return $ unBuildExprList el'
  where
    (ef, env) = buildLiftedExpr $ buildExprList e

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
    env = reverse $ zip xs as
    go (FuncFunc f) = newIORef $ FuncFuncRef f
    go (VarFunc x) = return . fromJust $ lookup x env
    go (ApFunc e1 e2) = do
        e1' <- go e1
        e2' <- go e2
        newIORef $ ApFuncRef e1' e2'

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

evalLiftedCRefS :: LamExpr -> IO LamExpr
evalLiftedCRefS e = do
    er <- buildExprLiftedCRef env ef
    el' <- evalStackLiftedCRef variableNames 0 [er] []
    return $ unBuildExprList el'
  where
    (ef, env) = buildLiftedExpr $ buildExprList e

evalStackLiftedCRef :: [Name] -> Int -> [IORef LamExprFuncCRef] -> [IORef LamExprFuncCRef] -> IO LamExprList
evalStackLiftedCRef vns narg (n:ns) as = seq narg $ readIORef n >>= \ne -> case ne of
    IndFuncCRef n' -> case (ns,as) of
        ([], []) -> evalStackLiftedCRef vns narg [n'] []
        (n1:n1s, a1:a1s) -> do
            writeIORef n1 $ ApFuncCRef n' a1
            evalStackLiftedCRef vns narg (n':ns) as
        _ -> error "evalStackLiftedCRef"
    VarFuncCRef x -> do
        as' <- mapM (\a -> evalStackLiftedCRef vns 0 [a] []) as
        return $ foldl (\n' a -> ApList n' a) (VarList x) as'
    ApFuncCRef n0 a -> evalStackLiftedCRef vns (narg+1) (n0:n:ns) (a:as)
    FuncFuncCRef fr -> readIORef fr >>= \(GlobleFunctionCompiled argc func) -> do
        if narg >= argc
            then do
                (narg', ns', as') <- func narg ns as
                -- writeIORef (head ns') $ IndFuncCRef n'
                -- evalStackLiftedCRef vns (n' : tail ns') (tail as')
                evalStackLiftedCRef vns narg' ns' as'
            else do
                let diff = argc - narg
                asPad <- mapM (newIORef . VarFuncCRef) (take diff vns)
                let nsPadGen _ [] = return []
                    nsPadGen nlast (argp:argps) = do
                        np <- newIORef $ ApFuncCRef nlast argp
                        nps <- nsPadGen np argps
                        return $ np : nps
                nsPad <- nsPadGen (last (n:ns)) asPad
                let as' = as ++ asPad
                    ns' = ns ++ nsPad
                e <- evalStackLiftedCRef (drop diff vns) argc (n:ns') as'
                return $ LamList (take diff vns) e
evalStackLiftedCRef _ _ _ _ = error "evalStackLiftedCRef"

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
    env = reverse $ zip xs as
    go (VarFunc x) = fromJust $ lookup x env
    go (ApFunc e1 e2) = ApFunc (go e1) (go e2)
    go (FuncFunc f) = FuncFunc f

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

eval :: LamExpr -> LamExpr
eval e = case evalStep e of
    Nothing -> e
    Just e' -> eval e'

repeatEval :: LamExpr -> [LamExpr]
repeatEval expr = expr : case evalStep expr of
    Nothing -> []
    Just expr' -> repeatEval expr'

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

substitude :: Name -> LamExpr -> LamExpr -> LamExpr
substitude x arg (Var y)
    | y == x = arg
    | otherwise = Var y
substitude x arg (Ap e1 e2) = Ap (substitude x arg e1) (substitude x arg e2)
substitude x arg (Lam y e)
    | y == x = Lam y e
    | not $ e `hasVar` x = Lam y e
    | arg `hasVar` y = Lam y' $ substitude x arg $ substitude y (Var y') e
    | otherwise = Lam y $ substitude x arg e
  where
    y' = firstUnusedName names [arg, e]

-- -}
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- ------------------------------------------------------------------------------------
-- {-

occurFree :: Name -> LamExpr -> Bool
occurFree x (Var y) = x /= y
occurFree x (Lam y e) = x == y || x `occurFree` e
occurFree x (Ap e1 e2) = x `occurFree` e1 && x `occurFree` e2

occurOnce :: Name -> LamExpr -> Bool
occurOnce x e = numberOfOccurrence x e <= 1

numberOfOccurrence:: Name -> LamExpr -> Int
numberOfOccurrence x (Var y)
    | x == y = 1
    | otherwise = 0
numberOfOccurrence x (Lam y e)
    | x == y = 0
    | otherwise = numberOfOccurrence x e
numberOfOccurrence x (Ap e1 e2) = numberOfOccurrence x e1 + numberOfOccurrence x e2

simplifyExprInline :: LamExpr -> LamExpr
simplifyExprInline x = fromMaybe x $ simplifyExprInlineMaybe x

simplifyExprInlineMaybe :: LamExpr -> Maybe LamExpr
simplifyExprInlineMaybe expr@(Ap (Lam x e) arg)
    | x `occurOnce` e = Just . simplifyExprInline $ substitude x arg e
    | evalStep arg == Nothing && freeVariables arg == [] = Just .simplifyExprInline $ substitude x arg e

simplifyExprInlineMaybe (Lam x e) = case simplifyExprInlineMaybe e of
    Nothing -> Nothing
    Just e' -> Just $ Lam x e'

simplifyExprInlineMaybe (Ap e1 e2) = case simplifyExprInlineMaybe e1 of
    Nothing -> case simplifyArgInlineMaybe e2 of
        Nothing -> Nothing
        Just e2' -> Just . simplifyExprInline $ Ap e1 e2'
    Just e1' -> Just . simplifyExprInline $ Ap e1' e2
simplifyExprInlineMaybe _ = Nothing

simplifyArgInline :: LamExpr -> LamExpr
simplifyArgInline x = fromMaybe x $ simplifyArgInlineMaybe x

simplifyArgInlineMaybe :: LamExpr -> Maybe LamExpr
simplifyArgInlineMaybe expr@(Ap (Lam x e) arg)
    | x `occurOnce` e = Just . simplifyArgInline $ substitude x arg e
simplifyArgInlineMaybe expr@(Ap (Lam x e) arg@(Ap _ _))
    | evalStep arg == Nothing && freeVariables arg == [] = Just . simplifyArgInline $ substitude x arg e
simplifyArgInlineMaybe expr@(Ap (Lam x e) arg@(Var _)) = Just . simplifyArgInline $ substitude x arg e

simplifyArgInlineMaybe (Lam x e) = case simplifyArgInlineMaybe e of
    Nothing -> Nothing
    Just e' -> Just $ Lam x e'

simplifyArgInlineMaybe (Ap e1 e2) = case simplifyArgInlineMaybe e1 of
    Nothing -> case simplifyArgInlineMaybe e2 of
        Nothing -> Nothing
        Just e2' -> Just . simplifyArgInline $ Ap e1 e2'
    Just e1' -> Just . simplifyArgInline $ Ap e1' e2
simplifyArgInlineMaybe _ = Nothing

-- -}
