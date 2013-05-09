{-# LANGUAGE QuasiQuotes #-}

module Main where

import Data.List
import Data.Maybe
import System.Environment
import Control.Arrow

import Parser
import Evaluation
import StringQQ

main :: IO ()
main = do
    args <- getArgs
    exprStr <- getContents
    let expr = (if "-O" `elem` args then simplifyExprInline else id) $ readExpr exprStr
        exprRead = unBuildExprBruijn' . explicitFreeVariable . buildExprBruijn $ expr
    putStrLn $ progGen exprRead

explicitFreeVariable :: LamExprBruijn -> LamExprBruijn
explicitFreeVariable = go where
    go (VarBruijn x) = VarBruijn $ "$Free:" ++ x
    go (BoundBruijn n) = BoundBruijn n
    go (ApBruijn e1 e2) = ApBruijn (go e1) (go e2)
    go (LamBruijn eb) = LamBruijn $ go eb

unBuildExprBruijn' :: LamExprBruijn -> LamExpr
unBuildExprBruijn' = snd . go names' where
    go ns (VarBruijn x) = (ns, Var x)
    go ns (ApBruijn e1 e2) = (ns'', Ap e1' e2') where
        (ns', e1') = go ns e1
        (ns'', e2') = go ns' e2
    go (n:ns) (LamBruijn eb) = second (Lam n') $ go ns' eb' where
        (n',ns') = if eb' `hasVarBruijn` n then (n,ns) else ("_", n:ns)
        eb' = substituteBruijn (VarBruijn n) eb
    go _ _ = error "unBuildExprBruijn"

names' :: [Name]
names' = map ("v" ++) $ map show ([1..] :: [Integer])

compile :: LamExpr -> String
compile (Var x) | "$Free:" `isPrefixOf` x = "VarC \"" ++ fromJust (stripPrefix "$Free:" x) ++ "\""
                | otherwise = x
compile (Ap e1 e2) = "applyC " ++ compileA e1 ++ " " ++ compileA e2
compile (Lam x e) = "LamC $ \\" ++ x ++ " -> " ++ compile e

compileA :: LamExpr -> String
compileA (Var x) | "$Free:" `isPrefixOf` x = "(" ++ compile (Var x) ++ ")"
                 | otherwise = x
compileA e = "(" ++ compile e ++ ")"

progGen :: LamExpr -> String
progGen e =
    preludeStr ++
    "expression :: LamExprC\n" ++
    "expression = " ++
    ( compileStg
    . convertExprCoreToExprStg
    . fixPoint fullLazinessTransLet
    . validTransCore
    . convertExprToExprCore
    $ e )

fixPoint :: Eq a => (a -> a) -> a -> a
fixPoint f x = go $ iterate f x where
    go (x1:x2:xs) | x1 == x2 = x1
                  | otherwise = go (x2:xs)
    go _ = error $ "fixPoint"

data ExprCore a
    = SymCore Name
    | VarCore a
    | AppCore a [a] -- non-empty
    | LetCore [(a, ExprCore a)] (ExprCore a) -- cannot be Let or Lam
    | LamCore [a] (ExprCore a) -- cannnot be Lam
  deriving Eq

type LamExprCore = ExprCore Name

namesCore :: [Name]
namesCore = map ("cv" ++) $ map show ([1..] :: [Integer])

convertExprToExprCore :: LamExpr -> LamExprCore
convertExprToExprCore = snd . go namesCore where
    go ns expr = case expr of
        Var x | "$Free:" `isPrefixOf` x -> (ns, SymCore $ fromJust (stripPrefix "$Free:" x))
              | otherwise -> (ns, VarCore x)
        Ap e1 e2 -> goAp ns e1 [e2]
        Lam x e -> second (goLam x) $ go ns e
    goLam x (LamCore xs e) = LamCore (x:xs) e
    goLam x e = LamCore [x] e
    goAp ns (Ap f a) as = goAp ns f (a:as)
    goAp ns f as = (,) ns'' $ if null bs then elet else LetCore bs elet where
        elet = AppCore (head nsl) (tail nsl)
        (ns'', bs) = second (zip nsl') $ mapAccumL go ns' fas
        (nsl',ns') = splitAt (length fas) ns
        nsl = padList (f:as) nsl'
        padList [] xs = xs
        padList (x:xs) ys | isComplex x = head ys : padList xs (tail ys)
                          | otherwise = xn : padList xs ys
          where (Var xn) = x
        fas = filter isComplex (f:as)
        isComplex (Var x) | "$Free:" `isPrefixOf` x = True
                          | otherwise = False
        isComplex _ = True

isLetCore :: ExprCore a -> Bool
isLetCore (LetCore _ _) = True
isLetCore _ = False

fromLetCore :: ExprCore a -> ([(a, ExprCore a)], ExprCore a)
fromLetCore (LetCore bs e) = (bs, e)
fromLetCore _ = error "fromLetLet"

validTransCore :: ExprCore a -> ExprCore a
validTransCore = go where
    go expr = case expr of
        SymCore x -> SymCore x
        VarCore x -> VarCore x
        AppCore f [] -> VarCore f
        AppCore f as -> AppCore f as
        LetCore [] e -> e
        LetCore bs (LetCore bs' e) -> go $ LetCore (bs ++ bs') $ go e
        LetCore bs e -> LetCore (bs'1'bs1 ++ bs'1'bs2 ++ bs'2) $ go e
          where
            bs' = map (second go) bs
            (bs'1, bs'2) = partition (isLetCore . snd) bs'
            bs'1' = map (second fromLetCore) bs'1
            bs'1'bs1 = concatMap (fst . snd) bs'1'
            bs'1'bs2 = map (id *** snd) bs'1'
        LamCore [] e -> e
        LamCore xs (LamCore xs' e) -> LamCore (xs ++ xs') $ go e
        LamCore xs e -> LamCore xs $ go e

isNotFreeInCore :: Name -> LamExprCore -> Bool
isNotFreeInCore "_" = const True
isNotFreeInCore x = go where
    go expr = case expr of
        SymCore _ -> True
        VarCore y -> x /= y
        AppCore f xs -> x `notElem` (f:xs)
        LetCore bs e -> all (go . snd) bs && go e
        LamCore _ e -> go e

isNoneFreeInCore :: [Name] -> LamExprCore -> Bool
isNoneFreeInCore xs e = all (`isNotFreeInCore` e) xs

fullLazinessTransLet :: LamExprCore -> LamExprCore
fullLazinessTransLet = validTransCore . go where
    go expr = case expr of
        LamCore xs (LetCore bs e) -> (if null bs1 then id else LetCore bs1) $
            LamCore xs $ LetCore bs2 $ go e
          where
            (bs1, bs2) = iter bs [] xs
            iter bs1' bs2' [] = (bs1', bs2')
            iter bs1' bs2' xs' = iter bs1'' (bs2'' ++ bs2') $ map fst bs2''
              where
                (bs1'', bs2'') = partition ((xs' `isNoneFreeInCore`) . snd) $ map (second go) bs1'

        LetCore bs e -> LetCore (map (second go) bs) $ go e
        _ -> expr

compileCore :: LamExprCore -> String
compileCore = go where
    go estg = case estg of
        SymCore x -> "VarC \"" ++ x ++ "\""
        VarCore x -> x
        AppCore f as -> showApp (tail as) $ "applyC " ++ f ++ " " ++ (head as)
        LetCore ds e -> "\n let\n" ++ showDefns ds ++ " in " ++ go e
        LamCore [] e -> go e
        LamCore (x:xs) e -> "LamC $ \\" ++ x ++ " -> " ++ go (LamCore xs e)
    showApp [] appStr = appStr
    showApp (a:as) appStr = showApp as $ "applyC (" ++ appStr ++ ") " ++ a
    showDefn (v,e) = v ++ " = " ++ go e
    showDefns ds = unlines . map ("  " ++) . lines . intercalate "\n" $ map showDefn ds

data ExprStg a
    = SymStg Name
    | VarStg a
    | AppStg a [a] -- non-empty
    | LetStg [(a, ClosureStg a)] (ExprStg a) -- cannot be Let
  deriving Eq

data ClosureStg a
    = UpdatableStg [a] (ExprStg a)
    | NonUpdatableStg [a] (ExprStg a)
    | FunctionStg [a] [a] (ExprStg a)
  deriving Eq

type LamExprStg = ExprStg Name

convertExprCoreToExprStg :: LamExprCore -> LamExprStg
convertExprCoreToExprStg = go where
    go exprLET = case exprLET of
        SymCore x -> SymStg x
        VarCore x -> VarStg x
        AppCore f as -> AppStg f as
        LetCore ds e -> LetStg ds' $ go e where
            ds' = map (second toClosure) ds
        LamCore xs _ -> error $ "convertExprCoreToExprStg : go : LamCore : " ++ show xs
    toClosure exprLET = case exprLET of
        LamCore xs e -> FunctionStg fvs xs e' where
            fvs = freeVariablesInStg e' \\ xs
            e' = go e
        VarCore x -> error $ "convertExprCoreToExprStg : toClosure : " ++ x
        e -> UpdatableStg (freeVariablesInStg e') e' where
            e' = go e

freeVariablesInStg :: LamExprStg -> [Name]
freeVariablesInStg = go where
    go exprStg = case exprStg of
        SymStg _ -> []
        VarStg x -> [x]
        AppStg f as -> nub (f:as)
        LetStg ds e -> foldr union (freeVariablesInStg e) $ map (freeVariablesInClosureStg . snd) ds

freeVariablesInClosureStg :: ClosureStg a -> [a]
freeVariablesInClosureStg = go where
    go closure = case closure of
        UpdatableStg fvs _ -> fvs
        NonUpdatableStg fvs _ -> fvs
        FunctionStg fvs _ _ -> fvs

compileStg :: LamExprStg -> String
compileStg = go where
    go estg = case estg of
        SymStg x -> "VarC \"" ++ x ++ "\""
        VarStg x -> x
        AppStg f as -> goApp (tail as) $ "applyC " ++ f ++ " " ++ (head as)
        LetStg ds e -> "\n let\n" ++ goDefns ds ++ " in " ++ go e
    goClosure closure = case closure of
        UpdatableStg fvs e -> "{- " ++ unwords fvs ++ " -} " ++ go e
        NonUpdatableStg fvs e -> "{- " ++ unwords fvs ++ " -} " ++ go e
        FunctionStg fvs xs e -> "{- " ++ unwords fvs ++ " -} " ++ (concat $ map (\x -> "LamC $ \\" ++ x ++ " -> ") xs ++ [go e])
    goApp [] appStr = appStr
    goApp (a:as) appStr = goApp as $ "applyC (" ++ appStr ++ ") " ++ a
    goDefn (v,e) = v ++ " = " ++ goClosure e
    goDefns ds = unlines . map ("  " ++) . lines . intercalate "\n" $ map goDefn ds

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
