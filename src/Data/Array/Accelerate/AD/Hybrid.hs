{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Data.Array.Accelerate.AD.Hybrid where

import Data.Array.Accelerate.AD.Skeletons (matMul, idMat, runExp, swapLastTwo, transposeLastTwo, adFold1)

import qualified Data.Array.Accelerate as A
import Data.Array.Accelerate.Interpreter (run)

import Prelude

import Control.Category ((>>>),(<<<))
import Control.Monad.State

import GHC.Exts

scale a = \da -> da A.* a

newtype D sh sh' a b = D (A.Acc (A.Array sh a) -> (A.Acc (A.Array sh' b), A.Acc (A.Array (sh' A.:. Int) b)))

compForward x = (matMul x .)
compReverse x = (. flip matMul x)

m1 = A.use $ A.fromList (A.Z A.:. (2::Int) A.:. (10::Int)) [0::Double ..]
m2 = A.use $ A.fromList (A.Z A.:. (10::Int) A.:. (3::Int)) [0::Double ..]
m3 = A.use $ A.fromList (A.Z A.:. (3::Int) A.:. (50::Int)) [0::Double ..]
m4 = A.use $ A.fromList (A.Z A.:. (50::Int) A.:. (500::Int)) [0::Double ..]
m5 = A.use $ A.fromList (A.Z A.:. (500::Int) A.:. (1::Int)) [0::Double ..]

-- f' = A.use $ A.fromList (A.Z A.:. (2::Int) A.:. (10::Int)) [0::Double ..]
-- g' = A.use $ A.fromList (A.Z A.:. (10::Int) A.:. (3::Int)) [0::Double ..]
-- h' = A.use $ A.fromList (A.Z A.:. (3::Int) A.:. (50::Int)) [0::Double ..]
-- k' = A.use $ A.fromList (A.Z A.:. (50::Int) A.:. (100::Int)) [0::Double ..]

expE = \x -> let y = A.exp x in (y, scale y)

negateE = \x -> (A.negate x, scale $ A.negate x)

recipE = \x -> let y = A.recip x in (y, scale . negate $ y*y)

andDeriv f x = let
  (y, f') = f x
  in (y, f' x)

expr w = let
  (x, f') = negateE w
  (y, g') = squareE x
  (z, h') = expE y
  in (z, h' . g' . f')

-- negateS :: (Fractional a, Fractional b) => State (b, a -> b) ()
-- negateS = modify negates
--   where negates (x, f') = (negate x, scale (negate 1.0) . f')

-- squareS :: (Fractional a, Fractional b) => State (b, a -> b) ()
-- squareS = modify squares
--   where squares (x, f') = (x*x, scale (2*x) . f')

-- expS :: (Floating a, Floating b) => State (b, a -> b) ()
-- expS = modify exps
--   where exps (x, f') = let y = A.exp x in (y, scale y . f')

-- runD f x = flip execState (x, id) f

-- gaussian = do
--   squareS
--   negateS

type UnaryD = A.Exp Double -> (A.Exp Double, A.Exp Double -> A.Exp Double)
type BinaryD = A.Exp Double -> A.Exp Double -> (A.Exp Double, A.Exp (Double, Double) -> A.Exp (Double, Double))

prepareUnary
  :: UnaryD -> (A.Exp Double -> A.Exp (Double, Double))
prepareUnary f x = let (y, f') = f x in A.lift (y, f' 1.0)

prepareBinary
  :: BinaryD -> A.Exp Double -> A.Exp Double -> A.Exp (Double, (Double, Double))
prepareBinary f x y =
  let
    (z, z') = uncurry f (x,y)
  in A.lift (z, z' $ A.lift (1.0 :: A.Exp Double, 1.0 :: A.Exp Double))

logisticE x =
  let
    (n, n') = negateE x
    (e, e') = expE n
    inc x = (x+1, id)
    (e1, e1') = inc e
    (s, s') = recipE e1
  in (s, s' . e1' . e' . n')

squareE :: A.Exp Double -> (A.Exp Double, A.Exp Double -> A.Exp Double)
squareE = \x -> (x A.* x, scale (2.0 A.* x))

subE :: A.Exp Double -> A.Exp Double -> (A.Exp Double, A.Exp (Double, Double) -> A.Exp (Double, Double))
subE = \x y -> (A.lift $ x A.- y, \z -> let
                   (da, db) = A.unlift (z :: A.Exp (Double, Double))
                   in A.lift (da :: A.Exp Double, A.negate db :: A.Exp Double))

addE :: A.Exp Double -> A.Exp Double -> (A.Exp Double, A.Exp (Double, Double) -> A.Exp (Double, Double))
addE = \x y -> (A.lift $ x A.+ y, \z -> let
                   (da, db) = A.unlift (z :: A.Exp (Double, Double))
                   in A.lift (da :: A.Exp Double, db :: A.Exp Double))

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

stack x y =
  let
    n = A.indexHead $ A.shape x
    x' = A.reshape (A.lift $ A.shape x A.:. (1::Int)) x
    y' = A.reshape (A.lift $ A.shape y A.:. (1::Int)) y
  in x' A.++ y'

extend x = A.reshape (A.lift $ A.shape x A.:. (1::Int)) x
extendShape x = let sh = A.shape x in A.lift $ sh A.:. A.indexHead sh

zipWithD
  :: (A.Slice sh, A.Shape sh) =>
     BinaryD
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> (A.Acc (A.Array (sh A.:. Int) Double),
         (A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double), A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double)))
zipWithD f x y =
  let
    (z, z') = A.unzip $ A.zipWith (prepareBinary f) x y
    (a',b') = A.unzip z'
    (a'', b'') = (diag a', diag b')
  in (z, (a'', b''))

zipWithD'
  :: (A.Shape sh, A.Slice sh) => BinaryD
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

pair :: A.Exp Double -> A.Exp Double -> A.Exp (Double, Double)
pair a b = A.lift (a,b)

sumD x =
  let
    sh = A.shape x
    shTail = A.indexTail sh
    n = A.indexHead sh
  in (A.sum x, A.generate (A.lift $ shTail A.:. (1::Int) A.:. n) (const (1.0::A.Exp Double)))

vec1 = A.use $ A.fromList (A.Z A.:. (10::Int)) [0:: Double ..]
vec2 = A.use $ A.fromList (A.Z A.:. (10::Int)) $ reverse [0::Double ..10]
vec3 = A.use $ A.fromList (A.Z A.:. (10::Int)) $ repeat (1.0::Double)
vec4 = A.reshape (A.lift $ A.shape vec3 A.:. (1::Int)) vec3

-- ax + b
affineD
  :: (A.Slice sh, A.Shape sh, A.Z ~ sh) =>
     A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double)
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> A.Acc (A.Array (sh A.:. Int) Double)
     -> (A.Acc (A.Array (sh A.:. Int) Double),
         ((A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double) -> A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double))
          -> A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double) -> A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double),
          (A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double) -> A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double))
          -> A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double) -> A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double)))
affineD a b x =
  let
    (c,c') = matVecMulD a x
    (d,(d1',d2')) = zipWithD addE b c
  in (c, (compReverse d1' . compReverse c', compReverse d2' . compReverse c'))

idM :: (A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double) -> (A.Acc (A.Array ((sh A.:. Int) A.:. Int) Double)))
idM = id

neuralD (a1,b1) (a2,b2) x =
  let
    (x1,(x11',x12')) = affineD a1 b1 x
    (y,y') = mapD logisticE x1
    (x2,(x21',x22')) = affineD a2 b2 y
  in (x2, (x21' . compReverse y' . x11', x22' . compReverse y' . x21'))

matVecMul
  :: (Num (A.Exp a), A.Slice sh, A.Shape sh, A.Elt a) =>
     A.Acc (A.Array ((sh A.:. Int) A.:. Int) a)
     -> A.Acc (A.Array (sh A.:. Int) a)
     -> A.Acc (A.Array (sh A.:. Int) a)
matVecMul a b =
  let
    sh = A.shape b
    c' = A.reshape (A.lift $ sh A.:. (1::Int)) b
  in A.reshape (A.shape b) $ matMul a c'

matVecMulD a x = (matVecMul a x, a)

sumOfSquares x y =
  let
    (a,a') = zipWithD' subE x y
    (b,b') = mapD squareE a
    (c,c') = sumD b
  in (c, (compReverse b' . compReverse a' $ id) c')

testOpt target init =
  let
    step a =
      let
        b' = snd $ sumOfSquares target a
        b'' = A.reshape (A.lift $ A.Z A.:. (A.indexHead $ A.shape b')) (transposeLastTwo b')
      in A.zipWith (-) a (A.map (*0.1) b'')
    done a =
      let
        err = fst $ sumOfSquares a target
      in A.unit $ A.sqrt (A.the err) A.> 1e-12
  in A.awhile done step init
