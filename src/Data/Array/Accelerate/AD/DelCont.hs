module Data.Array.Accelerate.AD.DelCont where

import Control.Monad.CC

data Expr = Const Double
          | Add Expr Expr
          | Mul Expr Expr
          | Var Int
          | Tup Expr Expr
          deriving (Show)

instance Num Expr where
  (+) = Add
  (*) = Mul
  fromInteger = Const . fromInteger

exp1 = let
  x = Var 0
  y = Var 1
  in x*x + y*y

autodiff x = case x of
  Add a b -> \k -> let
    Tup a' da' = k a
    Tup b' db' = k b
    in Tup (a'+b') (da' + db')
