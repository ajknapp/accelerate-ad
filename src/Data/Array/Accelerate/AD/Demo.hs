{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Array.Accelerate.AD.Demo where

import Data.Array.Accelerate.AD.Skeletons (matMul, idMat, runExp, swapLastTwo, transposeLastTwo, adFold1)

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate.Interpreter (run)

-- evaluated at x
f' = A.use $ A.fromList (A.Z A.:. (2::Int) A.:. (10::Int)) [0::Double ..]
-- evaluated at f(x)
g' = A.use $ A.fromList (A.Z A.:. (10::Int) A.:. (3::Int)) [0::Double ..]
-- evaluated at g(f(x))
h' = A.use $ A.fromList (A.Z A.:. (3::Int) A.:. (50::Int)) [0::Double ..]
-- evaluated at h(g(f(x)))
j' = A.use $ A.fromList (A.Z A.:. (50::Int) A.:. (80::Int)) [0::Double ..]
-- evaluated at j(h(g(f(x))))
k' = A.use $ A.fromList (A.Z A.:. (80::Int) A.:. (100::Int)) [0::Double ..]

-- type D a b = a -> (b, a -o b)
scale a = \da -> a*da

compForward x = (matMul x .)
compReverse x = (. flip matMul x)

squareE :: A.Exp Double -> (A.Exp Double, A.Exp Double -> A.Exp Double)
squareE = \x -> (x A.* x, scale (2.0 A.* x))

subE :: A.Exp Double -> A.Exp Double -> (A.Exp Double, A.Exp (Double, Double) -> A.Exp (Double, Double))
subE = \x y -> (A.lift $ x A.- y, \z -> let
                   (da, db) = A.unlift (z :: A.Exp (Double, Double))
                   in A.lift (da :: A.Exp Double, A.negate db :: A.Exp Double))

prepareUnary :: UnaryD -> (A.Exp Double -> A.Exp (Double, Double))
prepareUnary f x = let (y, f') = f x in A.lift (y, f' 1.0)

prepareBinary :: BinaryD -> A.Exp Double -> A.Exp Double -> A.Exp (Double, (Double, Double))
prepareBinary f x y =
  let
    (z, z') = uncurry f (x,y)
  in A.lift (z, z' $ A.lift (1.0 :: A.Exp Double, 1.0 :: A.Exp Double))

type UnaryD = A.Exp Double -> (A.Exp Double, A.Exp Double -> A.Exp Double)
type BinaryD = A.Exp Double -> A.Exp Double -> (A.Exp Double, A.Exp (Double, Double) -> A.Exp (Double, Double))

-- zipwith, but treat first input as a constant
-- quick hack to avoid proper treatment of variables
zipWithD'
  :: (A.Shape sh, A.Slice sh) =>
     BinaryD
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> (A.Acc (A.Array (sh A.:. Int) Double),
         A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double))
zipWithD' f c y =
  let
    (z, z') = A.unzip $ A.zipWith (prepareBinary f) c y
    (a',b') = A.unzip z'
    (a'', b'') = (diag a', diag b')
  in (z, b'')

mapD
  :: (A.Shape sh, A.Slice sh) =>
     UnaryD
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> (A.Acc (A.Array (sh A.:. Int) Double),
         A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double))
mapD f x =
  let
    (y, y') = A.unzip $ A.map (prepareUnary f) x
  in (y, diag y')

diag x =
  let
    sh = A.shape x
    n = A.indexHead sh
    diag' idx = A.cond (A.indexHead idx A.== (A.indexHead $ A.indexTail idx)) (x A.! A.indexTail idx) 0.0
  in A.generate (A.lift $ sh A.:. n) diag'

sumD x =
  let
    sh = A.shape x
    shTail = A.indexTail sh
    n = A.indexHead sh
  in (A.sum x,
      A.generate
      (A.lift $ shTail A.:. (1::Int) A.:. n)
      (\_ -> A.constant (1.0 :: Double)))

sumOfSquares x y =
  let
    (a,a') = zipWithD' subE x y
    (b,b') = mapD squareE a
    (c,c') = sumD b
  in (c, (compReverse b' . compReverse a' $ id) c')

-- Very simple optimization problem via gradient descent.
-- \min_{x \in \mathbb{R}^d} |x - y|^2
testOpt
  :: A.Acc (A.Array (A.Z A.:. Int) Double)
     -> A.Acc (A.Array (A.Z A.:. Int) Double)
     -> A.Acc (A.Array (A.Z A.:. Int) Double)
testOpt target init =
  let
    step a =
      let
        b' = snd $ sumOfSquares target a
        b'' = A.reshape (A.lift $ A.Z A.:. (A.indexHead $ A.shape b')) (transposeLastTwo b')
      in A.zipWith (-) a (A.map (*0.4) b'')
    done a =
      let
        err = fst $ sumOfSquares target a
      in A.map (\a' -> a' A.> 1e-12) err
  in A.awhile done step init

target = A.use $ A.fromList (A.Z A.:. (10::Int)) [0:: Double ..]
start = A.use $ A.fromList (A.Z A.:. (10::Int)) $ reverse [0::Double ..10]
