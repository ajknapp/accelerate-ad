module Data.Array.Accelerate.AD.AD where

import Data.List (transpose)

data AdExpr =
    Constant Double
  | Pi Int
  | Plus AdExpr AdExpr
  | Times AdExpr AdExpr
  deriving (Show, Eq)

evalAd :: AdExpr -> [Double] -> Double
evalAd (Constant x) _ = x
evalAd (Pi i) v = v !! i
evalAd (Plus x y) v = evalAd x v + evalAd y v
evalAd (Times x y) v = evalAd x v * evalAd y v

domainDim :: AdExpr -> Int
domainDim expr = if count == 0 then 0 else 1 + count
  where count = go expr 0
        go (Pi i) j = max i j
        go (Constant _) j = j
        go (Plus x y) j = max (go x j) (go y j)
        go (Times x y) j = max (go x j) (go y j)

diff :: AdExpr -> Int -> AdExpr
diff (Plus x y) i = Plus (diff x i) (diff y i)
diff (Times x y) i = Plus (Times (diff x i) y) (Times x (diff y i))
diff (Constant _) _ = Constant 0.0
diff (Pi i) j = if i == j then Constant 1.0 else Constant 0.0

grad :: AdExpr -> [AdExpr]
grad expr = map (diff expr) [0..domainDim expr - 1]

instance Num AdExpr where
  (+) = Plus
  (*) = Times
  fromInteger i = Constant (fromInteger i)

matVecMul :: (Num a) => [[a]] -> [a] -> [a]
matVecMul a v = map (sum . zipWith (*) v) a

matMatMul :: Num a => [[a]] -> [[a]] -> [[a]]
matMatMul a b = [[ sum $ zipWith (*) ar bc | bc <- (transpose b) ] | ar <- a]

jacobian :: [AdExpr] -> [[AdExpr]]
jacobian expr = map grad' expr
  where dim = max 0 . decf . maximum $ map domainDim expr
        decf x = x-1
        grad' e = map (diff e) [0..dim]

chain :: [AdExpr] -> [AdExpr] -> [Double] -> [[Double]]
chain f g a = matMatMul jfga jga
  where ga = map (evalAd' a) g
        jga = map (map $ evalAd' a) $ jacobian g
        jfga = map (map $ evalAd' ga) $ jacobian f
        evalAd' = flip evalAd

foo :: [AdExpr]
foo =
  let
    x = Pi 0
    y = Pi 1
    z = Pi 2
  in [y*z + x*z + x*y, x*x + y*y + z*z]

bar :: [AdExpr]
bar =
  let
    u = Pi 0
    v = Pi 1
  in
    [u*u+2*v, v*v*v+u]

pipeline :: [[AdExpr]] -> [Double] -> [[Double]]
pipeline [f] v = map (map $ flip evalAd v) $ jacobian f
pipeline (f:fs) gv = matMatMul rest jf
  where rest = (pipeline fs (map (flip evalAd gv) f))
        jf = map (map $ flip evalAd gv) $ jacobian f
