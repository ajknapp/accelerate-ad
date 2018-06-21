{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns        #-}

module Data.Array.Accelerate.AD.Skeletons where

import GHC.Exts

import Data.Array.Accelerate.Array.Sugar        as A hiding ( shape, reshape )
import Data.Array.Accelerate.Classes            as A
import Data.Array.Accelerate.Language           as A
import Data.Array.Accelerate.Prelude            as A

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Trafo.Base

import Prelude                                  as P hiding ( last )

import Data.Array.Accelerate.AD.FromHOAS


import qualified Data.Array.Accelerate as A

primApp1 dict f u =
  PrimApp (f dict) u

primApp2 f t u v =
  PrimApp (f t) (Tuple (NilTup `SnocTup` u `SnocTup` v))

add  t u v = primApp2 PrimAdd  t u v
sub  t u v = primApp2 PrimSub  t u v
mul  t u v = primApp2 PrimMul  t u v
fdiv t u v = primApp2 PrimFDiv t u v
expE t u = primApp1 t PrimExpFloating u
negE t u = primApp1 t PrimNeg u
recipE t u = primApp1 t PrimRecip u
sinE t u = primApp1 t PrimSin u
cosE t u = primApp1 t PrimCos u
tanE t u = primApp1 t PrimTan u
asinE t u = primApp1 t PrimAsin u
acosE t u = primApp1 t PrimAcos u
atanE t u = primApp1 t PrimAtan u
sinhE t u = primApp1 t PrimSinh u
coshE t u = primApp1 t PrimCosh u
asinhE t u = primApp1 t PrimAsinh u
acoshE t u = primApp1 t PrimAcosh u
atanhE t u = primApp1 t PrimAtanh u
sqrtE t u = primApp1 t PrimSqrt u

s1 = SuccIdx
s2 = SuccIdx . s1
s3 = SuccIdx . s2
s4 = SuccIdx . s3

avar0 :: (Kit acc, Arrays a0) => acc (aenv, a0) a0
avar0 = inject $ Avar ZeroIdx

avar1 :: (Kit acc, Arrays a1) => acc ((aenv, a1), a0) a1
avar1 = inject $ Avar $ s1 ZeroIdx

avar2 :: (Kit acc, Arrays a2) => acc (((aenv, a2), a1), a0) a2
avar2 = inject $ Avar $ s2 ZeroIdx

avar3 :: (Kit acc, Arrays a3) => acc ((((aenv, a3), a2), a1), a0) a3
avar3 = inject $ Avar $ s3 ZeroIdx

-- infixr 0 $^
-- ($^) :: Kit acc => (acc aenv a -> t) -> PreOpenAcc acc aenv a -> t
-- ($^) f a = f $ inject a


{--
-- | Lifts a fold to a computation of the fold and its Frechet derivative.
--
adFold1
    :: (A.Num a, P.Num a, Slice sh, Shape sh, Elt a, Elt b)
    => (Exp b -> Exp b -> Exp b)            -- ^ original fold function
    -> (Exp b -> Exp b -> Exp a)            -- ^ derivative of f with respect to first argument
    -> (Exp b -> Exp b -> Exp a)            -- ^ derivative of f with respect to second argument
    -> Acc (Array (sh :. Int) b)            -- ^ original input array
    -> Acc (Array (sh :. Int :. Int) a)     -- ^ Frechet derivative of original input computed via chain rule
    -> Acc ( Array sh b
           , Array (sh :. Int :. Int) a)
adFold1 f f0 f1 x x' = lift ( ans, matMul ans' x')
  where
    fs      = A.scanl1 f x
    sh      = A.shape fs
    n       = A.indexHead sh
    ans     = A.slice fs (lift $ Any :. (n - 1))

    ans''   = A.zipWith (*) term1 term2
    shAns'' = A.shape ans''
    ans'    = A.reshape (lift $ shAns'' :. constant 1) ans''

    -- term2'  = reverseLast . A.scanl1 (*) . reverseLast $ A.zipWith f1 fs (A.tail x)
    -- ones    = A.replicate (A.lift $ A.indexTail sh :. A.constant (1::Int)) (A.unit $ A.constant 1)

    ones    = A.fill (A.lift $ A.indexTail sh :. A.constant 1) 1
    term2'  = A.scanr1 (*) $ A.zipWith f1 fs (A.tail x)

    term1   = ones   A.++ A.zipWith f0 fs (A.tail x)
    term2   = term2' A.++ ones

--}


lastA :: (Shape sh, Slice sh, Elt e) => A.Acc (Array (sh:.Int) e) -> A.Acc (Array sh e)
lastA xs =
  let n = A.indexHead (A.shape xs)
  in  A.slice xs (lift (Any :. (n-1)))

matMul
    :: (A.Num a, Shape sh, Slice sh)
    => A.Acc (Array (sh :. Int :. Int) a)
    -> A.Acc (Array (sh :. Int :. Int) a)
    -> A.Acc (Array (sh :. Int :. Int) a)
matMul arr brr
  = A.fold (+) 0
  $ A.zipWith (*) arrRepl brrRepl
  where
    rowsA   = A.indexHead . A.indexTail $ A.shape arr
    colsB   = A.indexHead $ A.shape brr
    arrRepl = A.replicate (lift $ Any :. colsB :. All) arr
    brrRepl = A.replicate (lift $ Any :. rowsA :. All :. All) (transposeLastTwo brr)


-- transposeLastTwo = transposeOn _1 _2
--
transposeLastTwo
    :: (Elt a, Shape sh, Slice sh)
    => A.Acc (Array (sh :. Int :. Int) a)
    -> A.Acc (Array (sh :. Int :. Int) a)
transposeLastTwo v = A.backpermute (trans' $ A.shape v) trans' v
  where
    trans' :: (Slice sh) => A.Exp (sh :. Int :. Int) -> A.Exp (sh :. Int :. Int)
    trans' s =
      let sh         = A.indexHead s
          shTail     = A.indexTail s
          sh'        = A.indexHead shTail
          shTailTail = A.indexTail shTail
      in
      lift $ shTailTail :. sh :. sh'


-- reverseLast = reverseOn _1
--
-- reverseLast
--     :: (Slice sh, Shape sh, Elt a)
--     => Acc (Array (sh :. Int) a)
--     -> Acc (Array (sh :. Int) a)
-- reverseLast v = A.backpermute (A.shape v) (revLast n) v
--   where
--     n = A.indexHead $ A.shape v

--     revLast :: (Slice sh) => Exp Int -> Exp (sh :. Int) -> Exp (sh :. Int)
--     revLast n' sh = A.lift $ sh' :. (n' A.- k A.- 1)
--       where
--         sh' = A.indexTail sh
--         k   = A.indexHead sh

