{-# LANGUAGE QuasiQuotes #-}

module Main where

import Data.List
import System.Environment
import Control.Arrow
import Control.Monad.State
import Control.Applicative

import Parser
import Evaluation
import StringQQ

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    let expr = (if "-O" `elem` args then simplifyExprInline else id) $ readExpr exprStr
        exprCoreNM = convertExprToExprCore expr >>= floatComplexExpression
        exprCore = evalState exprCoreNM namesCore
        exprStg = convertExprCoreToExprStg exprCore
    if "-C" `elem` args
        then do
            putStrLn "/*\n"
            putStrLn $ showStg exprStg
            putStrLn "*/\n"
            putStrLn $ compileStgToC exprStg
        else putStrLn $ progGen $ compileStg exprStg

progGen :: String -> String
progGen eStr =
    preludeStr ++
    "expression :: LamExprC\n" ++
    "expression = " ++ eStr

fixPoint :: Eq a => (a -> a) -> a -> a
fixPoint f x = go $ iterate f x where
    go (x1:x2:xs) | x1 == x2 = x1
                  | otherwise = go (x2:xs)
    go _ = error $ "fixPoint"

type NameM = State [Name]

newName :: NameM Name
newName = state $ \ns -> (head ns, tail ns)

data ExprCore a
    = SymCore Name
    | VarCore a
    | AppCore (ExprCore a) (ExprCore a)
    | LetCore (BindingCore a) (ExprCore a)
    | LamCore a (ExprCore a)
    deriving (Eq, Show)

data BindingCore a
    = NonRec a (ExprCore a)
    | Rec [(a, ExprCore a)]
    deriving (Eq, Show)

type LamExprCore = ExprCore Name

convertExprToExprCore :: LamExpr -> NameM LamExprCore
convertExprToExprCore = go [] . buildExprBruijn where
    go env exprBruijn = case exprBruijn of
        VarBruijn x -> return $ SymCore x
        BoundBruijn n -> return $ VarCore $ env !! n
        ApBruijn e1 e2 -> do
            e1' <- go env e1
            e2' <- go env e2
            return $ AppCore e1' e2'
        LamBruijn eb -> do
            x <- newName
            LamCore x <$> go (x:env) eb

namesCore :: [Name]
namesCore = map ("v" ++) $ map show ([1..] :: [Integer])

compileCore :: LamExprCore -> String
compileCore = go where
    go exprCore = case exprCore of
        SymCore x -> "VarC \"" ++ x ++ "\""
        VarCore x -> x
        AppCore f a -> "applyC (" ++ go f ++ ") (" ++ go a ++ ")"
        LetCore (NonRec n1 e1) e -> "\n let\n" ++ goDefns [(n1, e1)] ++ " in " ++ go e
        LetCore (Rec ds) e -> "\n letrec\n" ++ goDefns ds ++ " in " ++ go e
        LamCore x e -> "LamC $ \\" ++ x ++ " -> " ++ go e
    goDefn (v,e) = v ++ " = " ++ go e
    goDefns ds = unlines . map ("  " ++) . lines . intercalate "\n" $ map goDefn ds

isVarCore :: LamExprCore -> Bool
isVarCore (VarCore _) = True
isVarCore _ = False

fromVarCore :: LamExprCore -> Name
fromVarCore (VarCore x) = x
fromVarCore _ = error "fromVarCore"

nameExprCore :: LamExprCore -> NameM Name
nameExprCore (VarCore x) = return x
nameExprCore _ = newName

floatComplexExpression :: LamExprCore -> NameM LamExprCore
floatComplexExpression = go where
    go exprCore = case exprCore of
        SymCore x -> return $ SymCore x
        VarCore x -> return $ VarCore x
        AppCore f a -> goApp f [a]
        LetCore b e -> LetCore b <$> go e
        LamCore _ _ -> do
            n <- newName
            binding <- NonRec n <$> goBinding exprCore
            return $ LetCore binding $ VarCore n
    goApp f as = case f of
        AppCore f' a -> goApp f' (a:as)
        _ -> do
            fas' <- mapM goBinding (f:as)
            nfas <- mapM nameExprCore fas'
            let bindings = map (uncurry NonRec) $ filter (not . isVarCore . snd) $ zip nfas fas'
                expr = foldl1 AppCore $ map VarCore nfas
            return $ foldr LetCore expr bindings
    goBinding exprCore = case exprCore of
        LamCore x e -> LamCore x <$> goBinding e
        _ -> go exprCore

data ExprStg a
    = SymStg Name
    | AppStg a [a]
    | LetStg (BindingStg a) (ExprStg a)
    deriving Eq

data BindingStg a
    = NonRecStg a (ClosureStg a)
    | RecStg [(a, ClosureStg a)]
    deriving Eq

data UpdateFlag = ReEntrant | Updatable | SingleEntry
    deriving Eq

data ClosureStg a = ClosureStg [a] UpdateFlag [a] (ExprStg a)
    deriving Eq

type LamExprStg = ExprStg Name
type LamBindingStg = BindingStg Name
type LamClosureStg = ClosureStg Name

instance Show UpdateFlag where
    show ReEntrant = "r"
    show Updatable = "u"
    show SingleEntry = "s"

convertExprCoreToExprStg :: LamExprCore -> LamExprStg
convertExprCoreToExprStg = go where
    go exprCore = case exprCore of
        SymCore x -> SymStg x
        VarCore x -> AppStg x []
        AppCore f a -> goApp f [a]
        LamCore _ _ -> error $ "convertExprCoreToExprStg : LamCore"
        LetCore b e -> LetStg (goBinding b) (go e)
    goApp f as = case f of
        AppCore f' a -> goApp f' (a:as)
        _ -> AppStg (fromVarCore f) $ map fromVarCore as
    goBinding (NonRec n exprCore) = NonRecStg n $ goClosure exprCore
    goBinding (Rec bs) = RecStg $ map (second goClosure) bs
    goClosure exprCore = case exprCore of
        LamCore x e -> goLamClosure [x] e
        _ -> ClosureStg fvs Updatable [] exprStg where
            exprStg = go exprCore
            fvs = freeVariablesInExprStg exprStg
    goLamClosure xs exprCore = case exprCore of
        LamCore x e -> goLamClosure (x:xs) e
        _ -> ClosureStg fvs ReEntrant (reverse xs) exprStg where
            exprStg = go exprCore
            fvs = freeVariablesInExprStg exprStg \\ xs

freeVariablesInExprStg :: LamExprStg -> [Name]
freeVariablesInExprStg exprStg = case exprStg of
    SymStg _ -> []
    AppStg f as -> nub (f:as)
    LetStg b e -> union bfvs $ freeVariablesInExprStg e \\ bns where
        bfvs = freeVariablesInBindingStg b
        bns = namesInBindingStg b

freeVariablesInClosure :: ClosureStg a -> [a]
freeVariablesInClosure (ClosureStg fvs _ _ _) = fvs

freeVariablesInBindingStg :: Eq a => BindingStg a -> [a]
freeVariablesInBindingStg (NonRecStg _ c) = freeVariablesInClosure c
freeVariablesInBindingStg (RecStg bs) = foldr1 union $ map (freeVariablesInClosure . snd) bs

namesInBindingStg :: BindingStg a -> [a]
namesInBindingStg (NonRecStg x _) = [x]
namesInBindingStg (RecStg bs) = map fst bs

compileStg :: LamExprStg -> String
compileStg = go where
    go exprStg = case exprStg of
        SymStg x -> "VarC \"" ++ x ++ "\""
        AppStg f [] -> f
        AppStg f as -> goApp (tail as) $ "applyC " ++ f ++ " " ++ head as
        LetStg (NonRecStg n1 e1) e -> "\n let\n" ++ goDefns [(n1, e1)] ++ " in " ++ go e
        LetStg (RecStg ds) e -> "\n letrec\n" ++ goDefns ds ++ " in " ++ go e
    goApp [] str = str
    goApp (a:as) str = goApp as $ "applyC (" ++ str ++ ") " ++ a
    goDefn (v,e) = v ++ " = " ++ goClosure e
    goDefns ds = unlines . map ("  " ++) . lines . intercalate "\n" $ map goDefn ds
    goClosure (ClosureStg fvs updFlag [] exprStg) =
        "{- " ++ unwords fvs ++ " \\" ++ show updFlag ++ " -} " ++ go exprStg
    goClosure (ClosureStg fvs updFlag xs exprStg) =
        "{- " ++ unwords fvs ++ " \\" ++ show updFlag ++ " -} " ++ goLam xs (go exprStg)
    goLam [] = id
    goLam (x:xs) = (("LamC $ \\" ++ x ++ " -> ") ++) . goLam xs

showStg :: LamExprStg -> String
showStg = go where
    go exprStg = case exprStg of
        SymStg x -> "VarC \"" ++ x ++ "\""
        AppStg f [] -> f ++ " {}"
        AppStg f as -> f ++ " {" ++ unwords as ++ "}"
        LetStg b e -> "\n let\n" ++ showBindingStg b ++ " in " ++ go e

showBindingStg :: LamBindingStg -> String
showBindingStg binding = case binding of
    NonRecStg n1 e1 -> goDefns [(n1, e1)]
    RecStg ds -> goDefns ds
  where
    goDefn (v,e) = v ++ " = " ++ showClosureStg e
    goDefns ds = unlines . map ("  " ++) . lines . intercalate "\n" $ map goDefn ds

showClosureStg :: LamClosureStg -> String
showClosureStg = goClosure where
    goClosure (ClosureStg fvs updFlag [] exprStg) =
        "{" ++ unwords fvs ++ "} \\" ++ show updFlag ++ " {} -> " ++ showStg exprStg
    goClosure (ClosureStg fvs updFlag xs exprStg) =
        "{" ++ unwords fvs ++ "} \\" ++ show updFlag ++ " {" ++ unwords xs ++ "} -> " ++ showStg exprStg

compileStgToC :: LamExprStg -> String
compileStgToC exprStg = (header ++) . unlines $
    map showFunctionDeclCmm allCode ++ [""] ++
    map showFunctionCmm allCode
  where
    header = "#include \"lam_stg.h\"\n\n"
    allCode = makeCode ++ enterCode ++ [mainCode]
    mainCode = FunctionCmm "int" "main" []
        [ StatCmm $ FunctionCallCmm "initialize" []
        , AssignCmm (VarCmm "cur_closure") $ FunctionCallCmm "enter_closure_mainLam" []
        , StatCmm $ LitCmm "while (1) { cur_closure = cur_closure->code(); if (need_gc()) gc(); }"
        , ReturnCmm $ LitCmm "0" ]
    makeCode = map makeCodeGen . sort . nub $ [1..4] ++ map nfvsGen allBindings where
        makeCodeGen nfvs = FunctionCmm "closure *" ("make_closure_" ++ show nfvs) params defns where
            fvs = map (\n -> "c" ++ show n) [0..nfvs-1]
            params = ("func_ptr", "func") : zip (repeat "closure *") fvs
            defns =
                [ DeclInitCmm "closure *" "ret" $ FunctionCallCmm "alloc_heap" [LitCmm $ show $ length fvs]
                , AssignCmm (VarCmm "ret->code") $ VarCmm "func"
                , AssignCmm (VarCmm "ret->fv_cnt") $ LitCmm (show $ length fvs)
                , DeclInitCmm "closure **" "fv_ptr" $ CoercionCmm "closure **" $ VarCmm "(ret + 1)" ]
                ++ assigns ++
                [ ReturnCmm $ VarCmm "ret" ]
            assigns = zipWith AssignCmm (map (ArrayIndexCmm (VarCmm "fv_ptr")) [0..]) (map VarCmm fvs)
        nfvsGen binding = case binding of
            RecStg _ -> undefined
            NonRecStg _ (ClosureStg fvs _ _ _) -> length fvs
    enterCode = map enterCodeGen allBindings where
        enterCodeGen binding = case binding of
            RecStg _ -> undefined
            NonRecStg name (ClosureStg fvs updFlag xs expr) ->
                FunctionCmm "closure *" ("enter_closure_" ++ name) [] defns
              where
                defns = paramsInit ++ freeVarsInit ++ lets ++ final
                paramsInit = if null params then [] else needArg : params ++ [popArg] where
                    needArg = StatCmm $ FunctionCallCmm "need_args" [LitCmm $ show $ length xs]
                    params = zipWith getParamGen xs ([0..] :: [Int])
                    getParamGen x k = DeclInitCmm "closure *" x $ FunctionCallCmm "get_param" [LitCmm $ show k]
                    popArg = StatCmm $ FunctionCallCmm "pop" [LitCmm $ show $ length xs]
                freeVarsInit = if null freeVars then [] else fvPtr : freeVars where
                    fvPtr = DeclInitCmm "closure **" "fv_ptr" $
                        CoercionCmm "closure **" $ VarCmm "(cur_closure + 1)"
                    freeVars = zipWith freeVarGen fvs ([0..] :: [Int])
                    freeVarGen fv k = DeclInitCmm "closure *" fv $ ArrayIndexCmm (VarCmm "fv_ptr") k
                lets = map letGen $ bindingsGen expr where
                    letGen b = case b of
                        RecStg _ -> undefined
                        NonRecStg n (ClosureStg fvs' _ _ _) -> DeclInitCmm "closure *" n $
                            FunctionCallCmm ("make_closure_" ++ show (length fvs')) $
                            VarCmm ("enter_closure_" ++ n) : map VarCmm fvs'
                    bindingsGen e = case e of
                        LetStg b e' -> b : bindingsGen e'
                        _ -> []
                final = exprGen expr where
                    exprGen e = case e of
                        LetStg _ e' -> exprGen e'
                        SymStg x ->
                            [ StatCmm $ FunctionCallCmm "create_ubsym"
                                [VarCmm "symbol", LitCmm $ "\"" ++ x ++ "\""]
                            , ReturnCmm $ VarCmm "symbol" ]
                        AppStg f as -> if updFlag == Updatable
                            then [ StatCmm $ FunctionCallCmm "push_upd_frame" []
                                 , AssignCmm (VarCmm "cur_closure->code") $ VarCmm "black_hole" ]
                                ++ pushEnter
                            else pushEnter
                          where
                            pushEnter = map pushArgGen (reverse as) ++ [ ReturnCmm $ VarCmm f ]
                            pushArgGen a = StatCmm $ FunctionCallCmm "push" [VarCmm a]
    mainBinding = NonRecStg "mainLam" (ClosureStg [] SingleEntry [] exprStg)
    allBindings = bindingsB mainBinding where
        bindingsB binding = case binding of
            RecStg _ -> undefined
            NonRecStg _ (ClosureStg _ _ _ e) -> binding : bindingsE e
        bindingsE expr = case expr of
            LetStg binding e -> bindingsE e ++ bindingsB binding
            _ -> []

data FunctionCmm = FunctionCmm TypeCmm Name [(TypeCmm, Name)] [StatementCmm]

showFunctionDeclCmm :: FunctionCmm -> String
showFunctionDeclCmm (FunctionCmm typeCmm funcName params _) =
    typeCmm ++ " " ++ funcName ++ "(" ++ showParams params ++ ");"
  where
    showParam (ty, name) = ty ++ " " ++ name
    showParams = intercalate ", " . map showParam

showFunctionCmm :: FunctionCmm -> String
showFunctionCmm (FunctionCmm typeCmm funcName params stats) =
    typeCmm ++ " " ++ funcName ++ "(" ++ showParams params ++ ") {\n" ++
    indentCmm (concatMap showStatementCmm stats) ++ "}\n"
  where
    indentCmm = unlines . map ("    " ++) . lines
    showParam (ty, name) = ty ++ " " ++ name
    showParams = intercalate ", " . map showParam

data StatementCmm
    = DeclCmm TypeCmm Name
    | DeclInitCmm TypeCmm Name ExprCmm
    | AssignCmm ExprCmm ExprCmm
    | StatCmm ExprCmm
    | ReturnCmm ExprCmm

showStatementCmm :: StatementCmm -> String
showStatementCmm statCmm = go statCmm ++ ";\n" where
    go stat = case stat of
        DeclCmm ty name -> ty ++ " " ++ name
        DeclInitCmm ty name expr -> ty ++ " " ++ name ++ " = " ++ showExprCmm expr
        AssignCmm le re -> showExprCmm le ++ " = " ++ showExprCmm re
        StatCmm e -> showExprCmm e
        ReturnCmm e -> "return " ++ showExprCmm e

data ExprCmm
    = LitCmm LiteralCmm
    | VarCmm Name
    | ArrayIndexCmm ExprCmm Int
    | CoercionCmm TypeCmm ExprCmm
    | IndirectionCmm ExprCmm
    | FunctionCallCmm Name [ExprCmm]

showExprCmm :: ExprCmm -> String
showExprCmm = go where
    go exprCmm = case exprCmm of
        LitCmm lit -> lit
        VarCmm var -> var
        ArrayIndexCmm e i -> go e ++ "[" ++ show i ++ "]"
        CoercionCmm ty e -> "(" ++ ty ++ ")" ++ showExprCmm e
        IndirectionCmm e -> "*(" ++ go e ++ ")"
        FunctionCallCmm fn es -> fn ++ "(" ++ intercalate ", " (map go es) ++ ")"

type TypeCmm = String
type LiteralCmm = String

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
