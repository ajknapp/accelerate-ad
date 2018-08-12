{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Array.Accelerate.AD.CCC where

import qualified Data.Array.Accelerate as A
import           Data.Array.Accelerate.Interpreter
import           Data.Array.Accelerate.Trafo (convertAfun)
import qualified Prelude as P

import           GHC.Exts

class    Yes1 a
instance Yes1 a

class    (c a, d a) => (c :&: d) a
instance (c a, d a) => (c :&: d) a

class Category k where
  type Ok k :: * -> Constraint
  type Ok k = Yes1
  id :: k a a
  (.) :: k b c -> k a b -> k a c

instance Category (->) where
  id = P.id
  (.) = (P..)

class Category k => Monoidal k where
  (%) :: (Ok2 k b d, Ok2 k a c) => a `k` b -> c `k` d -> (a,c) `k` (b,d)

instance Monoidal (->) where
  f % g = \(a,b) -> (f a, g b)

class Ok k a => NumCat k a where
  addC :: (a,a) `k` a
  subC :: (a,a) `k` a
  mulC :: (a,a) `k` a
  negateC :: a `k` a
  fromIntegerC :: P.Integer -> a `k` a

class Ok k a => FloatCat k a where
  expC :: a `k` a
  recipC :: a `k` a

instance P.Num a => NumCat (->) a where
  addC = P.uncurry (P.+)
  subC = P.uncurry (P.-)
  mulC = P.uncurry (P.*)
  negateC = P.negate
  fromIntegerC k = P.const (P.fromInteger k)

instance P.Floating a => FloatCat (->) a where
  expC = P.exp
  recipC = P.recip

newtype D k a b = D (a -> (b, a `k` b))

linearD :: (a -> b) -> k a b -> D k a b
linearD f f' = D (\a -> (f a, f'))

instance Category k => Category (D k) where
  type Ok (D k) = Ok k :&: Additive
  id = linearD id id
  D g . D f = D P.$ \a -> let
    (b,f') = f a
    (c,g') = g b
    in (c, g' . f')

type Ok2 k a b = (Ok k a, Ok k b)

class Category k => Cartesian k where
  exl :: Ok2 k a b => (a,b) `k` a
  exr :: Ok2 k a b => (a,b) `k` b
  dup :: Ok k a => a `k` (a,a)

class Category k => Cocartesian k where
  inl :: Ok2 k a b => a `k` (a,b)
  inr :: Ok2 k a b => b `k` (a,b)
  jam :: Ok k a => (a,a) `k` a

newtype a -+> b = AdditiveFun (a -> b)

instance Cartesian (->) where
  exl = P.fst
  exr = P.snd
  dup = \x -> (x,x)

instance (Cartesian k) => Cartesian (D k) where
  exl = linearD exl exl
  exr = linearD exr exr
  dup = linearD dup dup

instance Cocartesian k => Cocartesian (D k) where
  inl = linearD (\a -> (a,zero)) inl
  inr = linearD (\b -> (zero,b)) inr
  jam = linearD (\(a,b) -> add a b) jam

class Additive a where
  zero :: a
  add :: a -> a -> a

instance P.Num a => Additive a where
  zero = P.fromInteger 0
  add = (P.+)

instance Category (-+>) where
  type Ok (-+>) = Additive
  id = AdditiveFun id
  AdditiveFun g . AdditiveFun f = AdditiveFun (g . f)

instance Monoidal k => Monoidal (D k) where
  D f % D g = D P.$ \(a,b) -> let
    (c,f') = f a
    (d,g') = g b
    in ((c,d), f'%g')

instance Cartesian (-+>) where
  exl = AdditiveFun exl
  exr = AdditiveFun exr
  dup = AdditiveFun dup

instance Cocartesian (-+>) where
  inl = AdditiveFun (\a -> (a, zero))
  inr = AdditiveFun (\b -> (zero, b))
  jam = AdditiveFun (\(a,b) -> add a b)

instance Monoidal (-+>) where
  AdditiveFun f % AdditiveFun g = AdditiveFun (f%g)

instance (Additive a, P.Num a) => NumCat (-+>) a where
  addC = AdditiveFun addC
  subC = AdditiveFun subC
  mulC = AdditiveFun mulC
  negateC = AdditiveFun negateC
  fromIntegerC k = AdditiveFun (fromIntegerC k)

delta :: (Monoidal k, Cartesian k, Ok k a, Ok2 k c d) => k a c -> k a d -> k a (c, d)
delta f g = (f%g) . dup

nabla :: (Cocartesian k, Monoidal k, Ok k a, Ok2 k c d) => k c a -> k d a -> k (c, d) a
nabla f g = jam . (f%g)

class Scalable k a where
  scale :: a -> (a `k` a)

instance P.Num a => Scalable (-+>) a where
  scale a = AdditiveFun (\da -> a P.* da)

instance (P.Num a, NumCat k a, Scalable k a, Cocartesian k, Monoidal k) => NumCat (D k) a where
  addC = linearD addC addC
  subC = linearD subC subC
  mulC = D (\(a,b) -> (a P.* b, scale b `nabla` scale a))
  negateC = linearD negateC negateC
  fromIntegerC k = D (\_ -> (P.fromInteger k, scale (P.fromInteger 0)))

instance (FloatCat k a, P.Floating a, Scalable k a, Cocartesian k, Monoidal k) => FloatCat (D k) a where
  expC = D (\a -> let x = P.exp a in (x, scale x))
  recipC = D (\a -> let x = 1 P./ a in (x, scale (x P.* x)))

instance {-# OVERLAPPING #-} (A.Elt a, A.Num a, A.Fractional a) => NumCat (->) (A.Exp a) where
  addC = P.uncurry (A.+)
  subC = P.uncurry (A.-)
  mulC = P.uncurry (A.*)
  negateC = P.negate
  fromIntegerC k = P.const (P.fromInteger k)

class (Ok k a, Ok l a, A.Elt a) => AccCat k l a where
  mapC :: (Ok l a, NumCat l a, A.Shape sh) => A.Exp a `l` A.Exp a -> A.Acc (A.Array sh a) `k` A.Acc (A.Array sh a)
  fold1C :: (Ok l a, NumCat l a, A.Shape sh) => (A.Exp a, A.Exp a) `l` A.Exp a -> A.Acc (A.Array (sh A.:. Int) a) `k` A.Acc (A.Array sh a)

instance (P.Num a, A.Elt a) => AccCat (->) (->) a where
  mapC = A.map
  fold1C f = let g = \x y -> f (x,y) in A.fold1 g

instance (P.Num a, A.Elt a) => AccCat (->) (-+>) a where
  mapC (AdditiveFun f) = mapC f
  fold1C (AdditiveFun f) = fold1C f

instance (P.Num a, A.Elt a) => AccCat (-+>) (->) a where
  mapC f = AdditiveFun (mapC f)
  fold1C f = AdditiveFun (fold1C f)

instance (P.Num a, A.Elt a) => AccCat (-+>) (-+>) a where
  mapC f = AdditiveFun (mapC f)
  fold1C f = AdditiveFun (fold1C f)

accGrad f x =
  let
    D g = f
    (y, Cont h) = g x
    AdditiveFun h' = h id
  in (y, h' x)

instance (Category k, AccCat k l a, NumCat l a, P.Fractional a, P.Fractional (A.Exp a), Scalable l a, Cocartesian l, Monoidal l) => AccCat (D k) (D l) a where
  mapC (D f) = D (\x -> let g = P.fst . f
                            h = P.snd . f
                        in (mapC g x, mapC (h 1.0)))

instance (Category k, AccCat k l a) => AccCat (Cont r k) l a where
  mapC f = Cont (. mapC f)
  fold1C f = Cont (. fold1C f)

exp1 :: (Monoidal k, Cartesian k, NumCat k a) => a `k` a
exp1 = mulC . dup . addC . dup

exp2 :: (Monoidal k, Cartesian k, NumCat k a) => (a,a) `k` a
exp2 = let sqr = mulC . dup in addC . (sqr % sqr)

exp3 :: (Monoidal k, Cartesian k, NumCat k a) => a `k` a
exp3 = let sqr = mulC . dup in mulC . (id%sqr) . dup

andDer f x =
  let
    D g = f
    (y, Cont h) = g x
    AdditiveFun h' = h id
  in (y, h' 1.0)

idMat :: A.Acc (A.Vector Double)
idMat = A.use P.$ A.fromList (A.Z A.:. (2::Int)) [0,1::Double]

andGradTup f x =
  let
    D g = f
    (y, Cont h) = g x
    AdditiveFun h' = h id
  in
    (y, (h' (1.0, 0.0), h' (0.0, 1.0)))

newtype Cont r k a b = Cont ((b `k` r) -> (a `k` r))

instance Category k => Category (Cont r k) where
  type Ok (Cont r k) = Ok k
  id = Cont id
  Cont f . Cont g = Cont (g . f)

join
  :: (Cocartesian k, Monoidal k, Ok k a, Ok k c, Ok k d) =>
     (k c a, k d a) -> k (c, d) a
join (f,g) = f `nabla` g

unjoin
  :: (Cocartesian k, Ok k a, Ok k b) => k (a, b) c -> (k a c, k b c)
unjoin h = (h . inl, h . inr)

instance (Monoidal k, Ok k r, Cocartesian k) => Monoidal (Cont r k) where
  Cont f % Cont g = Cont (join . (f%g) . unjoin)

instance (Cartesian k) => Cartesian (Cont r k) where
  exl = Cont (. exl)
  exr = Cont (. exr)
  dup = Cont (. dup)

instance (Cocartesian k, Ok k r, Monoidal k) => Cocartesian (Cont r k) where
  inl = Cont (exl . unjoin)
  inr = Cont (exr . unjoin)
  jam = Cont (join . dup)

instance (Category k, Scalable k s) => Scalable (Cont r k) s where
  scale s = Cont (. scale s)

instance (Category k, NumCat k a) => NumCat (Cont r k) a where
  addC = Cont (. addC)
  subC = Cont (. subC)
  mulC = Cont (. mulC)
  negateC = Cont (. negateC)
  fromIntegerC k = Cont (. fromIntegerC k)

newtype Dual k a b = Dual (b `k` a)

instance Category k => Category (Dual k) where
  type Ok (Dual k) = Ok k
  id = Dual id
  Dual f . Dual g = Dual (g . f)

instance Monoidal k => Monoidal (Dual k) where
  Dual f % Dual g = Dual (f%g)

instance Cartesian k => Cocartesian (Dual k) where
  inl = Dual exl
  inr = Dual exr
  jam = Dual dup

instance Cocartesian k => Cartesian (Dual k) where
  exl = Dual inl
  exr = Dual inr
  dup = Dual jam

instance Scalable k s => Scalable (Dual k) s where
  scale s = Dual (scale s)

-- NN implementation

square :: (Cartesian k, NumCat k a) => a `k` a
square = mulC . dup

sigmoid :: (Cartesian k, Monoidal k, NumCat k a, FloatCat k a) => a `k` a
sigmoid = recipC . addC . (fromIntegerC 1 % (expC . negateC)) . dup

-- sumOfSquaredError :: (A.Shape sh, AccCat k l a) => A.Acc (A.Array (sh A.:. Int) a) `k` A.Acc (A.Array sh a)
-- sumOfSquaredError = fold1C' addC' . mapC square'
--   where addC' = addC :: (A.Exp a, A.Exp a) `l` A.Exp a
--         fold1C' = fold1C :: (A.Exp a, A.Exp a) `l` A.Exp a -> A.Acc (A.Array (sh A.:. Int) a) `k` A.Acc (A.Array sh a)
--         square' = square :: A.Exp a `l` A.Exp a

-- id' = Frechet (\a -> (a, idMat P.$ A.shape ))
