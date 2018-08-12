{-# LANGUAGE DeriveFunctor #-}
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

module Data.Array.Accelerate.AD.ADVec where

import Data.Array.Accelerate.AST hiding (Acc)
import Data.Array.Accelerate.Array.Representation hiding (Shape, Slice)
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Trafo (convertFun, convertAfun, convertAcc, convertExp)
import Data.Array.Accelerate.Trafo.Base
import qualified Data.Array.Accelerate.Trafo.Fusion as F
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Trafo.Sharing hiding (convertFun, convertAfun, convertAcc, convertExp)
import Data.Array.Accelerate.Trafo.Normalise
import Data.Array.Accelerate.Trafo.Simplify
import Data.Array.Accelerate.Trafo.Substitution as Sub
import Data.Array.Accelerate.Type

import qualified Data.Array.Accelerate as A

import Data.Array.Accelerate.Interpreter

import Data.Array.Accelerate.AD.FromHOAS
import Data.Array.Accelerate.AD.Skeletons

foo :: A.Acc (Vector Double) -> A.Acc (Vector Double) -> A.Acc (Vector Double)
foo = A.zipWith (+)

vec = A.fromList (Z :. (10::Int)) [(0::Double)..]

runExp :: Elt e => A.Exp e -> e
runExp e = A.indexArray (run (A.unit e)) Z

addition :: A.Exp Double -> A.Exp Double -> A.Exp Double
addition x y = x + y

{-
adMap f f' x x' = pair (A.map f x) (matMul (A.reshape sh $ A.map f' x) x')
  where sh = A.lift $ A.shape x :. (1::Int)

adZipWith f f0 f1 x y = pair (A.zipWith f x y) $ (A.reshape sh0' f0s) A.++ (A.reshape sh1' f1s)
  where f0s = A.zipWith f0 x y
        sh0' = A.lift $ A.shape f0s :. (1::Int)
        f1s = A.zipWith f1 x y
        sh1' = A.lift $ A.shape f0s :. (1::Int)
-}

adMap
    :: forall acc aenv sh a b. (Kit acc, Shape sh, Slice sh, A.Elt a, A.Elt b)
    => PreFun     acc aenv (a -> b)
    ->            acc aenv (Array sh a, Array (sh :. Int) a) -- original input array
    -> PreOpenAcc acc aenv (Array sh b, Array (sh :. Int) b)
adMap f x
  = Alet x
  $^ Alet (weaken s1 . inject $ Aprj ZeroTupIdx x)
  $^ Alet (weaken s2 . inject $ Aprj (SuccTupIdx ZeroTupIdx) x)
  $^ Alet (inject $ Map (weaken s3 f) avar1)
  $^ Alet (inject $ Map (weaken s4 $ applyRewriteExp (flip diffPreOpenExp 0) f) avar1)
  $^ Atuple (NilAtup `SnocAtup` avar0 `SnocAtup` avar1)
-- adMap f x x'
--   = Alet x
--   $^ Alet (weaken s1 x')
--   $^ Alet (inject $ Map (weaken s2 $ applyRewriteExp (flip diffPreOpenExp 0) f) avar0)
--   $^ Alet (inject $ Map (weaken s3 f) avar2)
--   $^ Atuple (NilAtup `SnocAtup` avar0 `SnocAtup` avar1)

{-
-- | Lifts a fold to a computation of the fold and its Frechet derivative.
adFold
  :: (Num (A.Exp a), Num a, A.Slice sh, A.Shape sh, Elt a, Elt b) =>
     (A.Exp b -> A.Exp b -> A.Exp b) -- ^ original fold function
     -> (A.Exp b -> A.Exp b -> A.Exp a) -- ^ derivative of `f` with respect to first argument
     -> (A.Exp b -> A.Exp b -> A.Exp a) -- ^ derivative of `f` with respect to second argument
     -> A.Acc (Array (sh :. Int) b)     -- ^ original input array
     -> A.Acc (Array ((sh :. Int) :. Int) a) -- ^ Frechet derivative of original input
     -> A.Acc (Array sh b, Array ((sh :. Int) :. Int) a)
adFold f f0 f1 x x' = pair ans (matMul ans' x')
  where fs = A.scanl1 f x
        sh = A.shape fs
        n = A.indexHead sh
        ans = A.slice fs (A.lift $ A.Any :. (n - 1))
        ans'' = A.zipWith (A.*) term1 term2
        shAns'' = A.shape ans''
        ans' = A.reshape (A.lift $ shAns'' :. (1::Int)) ans''
        term1 = ones A.++ A.zipWith f0 fs (A.tail x)
        term2' = reverseLast . A.scanl1 (A.*) . reverseLast $ A.zipWith f1 fs (A.tail x)
        ones = A.replicate (A.lift $ A.indexTail sh :. A.constant (1::Int)) (A.unit $ A.constant 1)
        term2 = term2' A.++ ones
-}

adFold1
    :: forall acc aenv sh a. (Kit acc, Shape sh, Slice sh, A.Num a)
    => PreFun     acc aenv (a -> a -> a)
    ->            acc aenv (Array (sh:.Int)      a)   -- original input array
    ->            acc aenv (Array (sh:.Int:.Int) a)   -- Frechet derivative of input computed via chain rule
    -> PreOpenAcc acc aenv (Array sh a, Array (sh :. Int :. Int) a)
adFold1 f xs xs'
  =  Alet xs                                            -- TLM: may be unnecessary
  $^ Alet (weaken s1 xs')
  $^ Alet (inject $ Scanl1 (weaken s2 f) avar1)         -- fs
  $^ Alet (fromHOAS lastA avar0)                         -- ans
  $^ Alet (fromHOAS ans' avar3 avar2
                         (inject $ ZipWith (weaken s4 f0) avar1 (fromHOAS A.tail avar3))
                         (inject $ ZipWith (weaken s4 f1) avar1 (fromHOAS A.tail avar3)))
  $^ Atuple (NilAtup `SnocAtup` avar1 `SnocAtup` avar0)
  where
    -- compute derivatives wrt each argument, from before...
    f0 = applyRewriteExp (flip diffPreOpenExp 0) f
    f1 = applyRewriteExp (flip diffPreOpenExp 1) f

    ans' x x' x0 x1 =
      let
          -- we may want to replicate the definition of 'ones' at each use site
          -- to enable fusion
          sh    = A.indexTail (A.shape x)
          ones  = A.fill (A.lift (sh :. A.constant 1)) 1

          term1 = ones            A.++ x0
          term2 = A.scanr1 (*) x1 A.++ ones
          term3 = A.zipWith (*) term1 term2
          term4 = A.reshape (A.lift $ A.shape term3 :. A.constant 1) term3
          term5 = matMul term4 x'
      in
      term5


{-
matMul
  :: (Elt a, Num (A.Exp a), Shape sh, Slice sh) =>
     A.Acc (Array (sh :. Int :. Int) a)
     -> A.Acc (Array (sh :. Int :. Int) a)
     -> A.Acc (Array (sh :. Int :. Int) a)
matMul arr brr
  = A.fold (A.+) 0
  $ A.zipWith (A.*) arrRepl brrRepl
  where
    rowsA = A.indexHead . A.indexTail $ A.shape arr
    colsB = A.indexHead $ A.shape brr
    arrRepl             = A.replicate (A.lift $ Any   :. colsB :. All) arr
    brrRepl             = A.replicate (A.lift $ Any :. rowsA :. All   :. All) (transposeLastTwo brr)

transposeLastTwo :: (Elt a, Shape sh, Slice sh) => A.Acc (Array (sh :. Int :. Int) a) -> A.Acc (Array (sh :. Int :. Int) a)
transposeLastTwo v = A.backpermute (trans' $ A.shape v) trans' v
  where
    trans' :: (Slice sh) => A.Exp (sh :. Int :. Int) -> A.Exp (sh :. Int :. Int)
    trans' s = let
      sh = A.indexHead s
      shTail = A.indexTail s
      sh' = A.indexHead shTail
      shTailTail = A.indexTail shTail
      in A.lift $ shTailTail :. sh :. sh'

reverseLast
  :: (A.Slice sh, A.Shape sh, Elt a) =>
     A.Acc (Array (sh :. Int) a)
     -> A.Acc (Array (sh :. Int) a)
reverseLast v = A.backpermute (A.shape v) (revLast n) v
  where n = A.indexHead $ A.shape v
        revLast :: (Slice sh) => A.Exp Int -> A.Exp (sh :. Int) -> A.Exp (sh :. Int)
        revLast n' sh = A.lift $ sh' :. (n' A.- k A.- 1)
          where
            sh' = A.indexTail sh
            k = A.indexHead sh
-}

idMat
  :: (Elt a, Num a) =>
    A.Exp Int
     -> A.Acc (Array ((Z :. Int) :. Int) a)
idMat n = A.generate (A.lift $ Z :. n :. n) f
  where
    f idx = let
      idx2 = A.unindex2 idx
      in
      A.cond (A.fst idx2 A.== A.snd idx2) (A.constant 1) (A.constant 0)

pair :: (Arrays a, Arrays b) => A.Acc a -> A.Acc b -> A.Acc (a,b)
pair x y = A.lift (x,y)

dimension :: PreOpenFun OpenAcc () aenv f -> Int
dimension (Body _) = 0
dimension (Lam f) = 1 + dimension' f
  where
    dimension' g = go g 0

    go :: PreOpenFun OpenAcc (c,d) aenv' f' -> Int -> Int
    go (Lam g) k = go g (k+1)
    go (Body b) k = k

diffFun
    :: (Num a, Num b)
    => PreFun OpenAcc aenv (a -> b)
    -> Int
    -> PreFun OpenAcc aenv (a -> b)
diffFun (Lam (Body b)) i
  -- = simplify
  = Lam . Body
  -- $ rebuildE (subst (SuccIdx ZeroIdx) 0)
  -- $ rebuildE (subst ZeroIdx           1)
  $ diffPreOpenExp b i
  where
    subst :: (Elt s, Elt t) => Idx env s -> s -> Idx env t -> PreOpenExp OpenAcc env aenv t
    subst ix c this
      | Just Refl <- matchIdx ix this = Const (fromElt c)
      | otherwise                     = Var this


diffFun2
    :: (Num a, Num b)
    => PreFun OpenAcc aenv (a -> b -> c)
    -> Int
    -> PreFun OpenAcc aenv (a -> b -> c)
diffFun2 (Lam (Lam (Body b))) i
  -- = simplify
  = Lam . Lam . Body
  -- $ rebuildE (subst (SuccIdx ZeroIdx) 0)
  -- $ rebuildE (subst ZeroIdx           1)
  $ diffPreOpenExp b i
  where
    subst :: (Elt s, Elt t) => Idx env s -> s -> Idx env t -> PreOpenExp OpenAcc env aenv t
    subst ix c this
      | Just Refl <- matchIdx ix this = Const (fromElt c)
      | otherwise                     = Var this


diffOpenAcc :: OpenAcc aenv a -> OpenAcc aenv a
diffOpenAcc = cvtA
  where
    cvtT :: Atuple (OpenAcc aenv) t -> Atuple (OpenAcc aenv) t
    cvtT atup = case atup of
      NilAtup      -> NilAtup
      SnocAtup t a -> cvtT t `SnocAtup` cvtA a

    cvtA :: OpenAcc aenv a -> OpenAcc aenv a
    cvtA (OpenAcc pacc) = OpenAcc $ case pacc of
      Alet bnd body -> Alet (cvtA bnd) (cvtA body)
      Avar idx -> error "Avar"
      Atuple t -> Atuple $ cvtT t
      Aprj idx xs -> error "Aprj"
      Apply fs xs -> error "Apply"
      Aforeign f g xs -> error "Aforeign"
      Acond cnd xs ys -> error "Acond"
      Awhile cnd step xs -> error "Awhile"
      Use xs -> error "Use"
      Unit x -> error "Unit"
      Reshape sh xs -> error "Reshape"
      Generate sh f -> error "Generate"
      Transform sh shF f xs -> error "Transform"
      Replicate sl xs expr -> error "Replicate"
      Slice sl xs expr -> error "Slice"
      Map f a -> Map (applyRewriteExp (flip diffPreOpenExp 0) f) (cvtA a)
      ZipWith f xs ys -> error "ZipWith"
      Fold f e0 xs -> error "Fold"
      Fold1 f xs -> error "Fold1"
      FoldSeg f e0 xs segF -> error "FoldSeg"
      Fold1Seg f xs segF -> error "FoldSeg1"
      Scanl f e0 xs -> error "Scanl"
      Scanl' f e0 xs -> error "Scanl"
      Scanl1 f xs -> error "Scanl1"
      Scanr f e0 xs -> error "Scanr"
      Scanr' f e0 xs -> error "Scanr'"
      Scanr1 f xs -> error "Scanr1"
      Permute f xs g ys -> error "Permute"
      Backpermute sh shF xs -> error "Backpermute"
      Stencil f df xs -> error "Stencil"
      Stencil2 f g df dg xs -> error "Stencil2"

newtype DelayedOpenAcc' aenv t = DelayedOpenAcc' (DelayedOpenAcc aenv t)
undelayOpenAcc' (DelayedOpenAcc' a) = a

diffDelayedOpenAcc :: (Slice sh, Shape sh, Elt a, A.Num a, Num (A.Exp a)) => DelayedOpenAcc aenv (Array sh a) -> DelayedOpenAcc aenv (Array sh a, Array (sh :. Int) a)
diffDelayedOpenAcc a = cvtA a
  where
    -- cvtT :: Atuple (DelayedOpenAcc aenv) (Array sh' e) -> Atuple (DelayedOpenAcc aenv) (Array sh' e, Array (sh' :. Int) e)
    -- cvtT :: (Slice sh', Shape sh', Elt e) => Atuple (DelayedOpenAcc aenv) (Array sh' e) -> Atuple (DelayedOpenAcc aenv) (Array sh' e, Array (sh' :. Int) e)
    -- cvtT atup = case atup of
    --   NilAtup      -> NilAtup
    --   SnocAtup t a -> cvtT t `SnocAtup` cvtA a

    -- cvtA :: DelayedOpenAcc aenv t -> DelayedOpenAcc aenv t
    cvtA :: (Slice sh', Shape sh', Elt e) => DelayedOpenAcc aenv (Array sh' e) -> DelayedOpenAcc aenv (Array sh' e, Array (sh' :. Int) e)
    cvtA pacc = case pacc of
      -- Delayed e fn ix -> Manifest $ Atuple (NilAtup `SnocAtup` Delayed e fn ix `SnocAtup` Delayed (error "AH") (error "HA") ix)
      Manifest m -> Manifest $ case m of
        Alet bnd body -> Alet bnd (cvtA body)
        Avar idx -> error "Avar"
        -- Atuple t -> Atuple $ cvtT t
        Aprj idx xs -> error "Aprj"
        Apply fs xs -> error "Apply"
        Aforeign f g xs -> error "Aforeign"
        Acond cnd xs ys -> Acond cnd (cvtA xs) (cvtA ys)
        Awhile cnd step xs -> error "Awhile"
        Use xs -> error "Use"
        Unit x -> error "Unit"
        Reshape sh xs -> error "Reshape"
        Generate sh f -> error "Generate"
        Transform sh shF f xs -> error "Transform"
        Replicate sl xs expr -> error "Replicate"
        Slice sl xs expr -> error "Slice"
        Map f xs -> adMap f (cvtA xs) -- Map (applyRewriteExp (flip diffPreOpenExp 0) f) xs
        ZipWith f xs ys -> error "ZipWith"
        Fold f e0 xs -> error "Fold"
        Fold1 f xs -> error "Fold1"
        FoldSeg f e0 xs segF -> error "FoldSeg"
        Fold1Seg f xs segF -> error "FoldSeg1"
        Scanl f e0 xs -> error "Scanl"
        -- Scanl' f e0 xs -> error "Scanl"
        Scanl1 f xs -> error "Scanl1"
        Scanr f e0 xs -> error "Scanr"
        -- Scanr' f e0 xs -> error "Scanr'"
        Scanr1 f xs -> error "Scanr1"
        Permute f xs g ys -> error "Permute"
        Backpermute sh shF xs -> error "Backpermute"
        Stencil f xbnd xs -> error "Stencil"
        Stencil2 f xbnd xs ybnd ys -> error "Stencil2"

diffAfun
    :: (Num a, Shape sh, Elt a, Slice sh, Num (A.Exp a))
    => PreAfun DelayedOpenAcc (Array sh a -> Array sh a)
    -> PreAfun DelayedOpenAcc (Array sh a -> (Array sh a, Array (sh :. Int) a))
diffAfun (Alam (Abody b)) = Alam . Abody $ diffDelayedOpenAcc b

st1 :: A.Stencil3x3 Double -> A.Stencil3x3 Double -> A.Exp Double
st1 ((a,b,c),(d,e,f),(g,h,i)) _ = 2.0*h+b

st :: A.Stencil3 Double -> A.Exp Double
st (a,b,c) = a-2.0*b+c

-- analogous to function from first blog post
--
diffPreOpenExp
  :: forall acc env_ aenv t_.
  (AccClo acc ~ acc, Rebuildable acc) =>
     PreOpenExp acc env_ aenv t_
    -> Int
    -> PreOpenExp acc env_ aenv t_
diffPreOpenExp e i = cvtE e
  where
    cvtE :: PreOpenExp acc env aenv e -> PreOpenExp acc env aenv e
    cvtE = \case
      Let bnd body        -> Let (cvtE bnd) (cvtE body)
      Var v               -> delta (idxToInt v) i
      Foreign asm f expr  -> error "Foreign functions aren't differentiable."
      Tuple t             -> Tuple (cvtT t)
      Prj ix expr         -> Prj ix (cvtE expr)
      IndexNil            -> error "IndexNil"
      IndexCons idx idxs  -> error "IndexCons"
      IndexHead idx       -> error "IndexHead"
      IndexTail idx       -> error "IndexTail"
      IndexAny            -> error "IndexAny"
      IndexSlice sl slexp expr -> error "IndexSlice"
      IndexFull sl slex expr -> error "IndexFull"
      ToIndex idx jdx     -> error "ToIndex"
      FromIndex idx jdx   -> error "FromIndex"
      Cond cnd x y        -> error "Cond"
      While cnd f xs      -> error "While"
      Const{}             -> delta 0 1 -- zero
      PrimConst{}         -> delta 0 1 -- zero
      PrimApp f x         -> primApp f x
      Index xs idx        -> error "Index"
      LinearIndex xs idx  -> error "LinearIndex"
      Shape xs            -> Shape xs
      ShapeSize expr      -> error "ShapeSize"
      Intersect expr1 expr2 -> error "Intersect"
      Union expr1 expr2   -> error "Union"
      Undef               -> Undef
      Coerce expr         -> Coerce expr

    cvtT :: Tuple (PreOpenExp acc env aenv) e -> Tuple (PreOpenExp acc env aenv) e
    cvtT NilTup        = NilTup
    cvtT (SnocTup t e) = cvtT t `SnocTup` cvtE e

    -- This is kind of a hack? We can traverse the representation of any type
    -- down to primitive values in order to get a zero.
    --
    delta :: forall env c. Elt c => Int -> Int -> PreOpenExp acc env aenv c
    delta i' j' = Const $ go (eltType (undefined::c))
      where
        go :: TupleType a -> a
        go TypeRunit         = ()
        go (TypeRpair ta tb) = (go ta, go tb)
        go (TypeRscalar t)   = scalar t

        scalar :: ScalarType a -> a
        scalar (SingleScalarType t) = single t
        scalar (VectorScalarType t) = vector t

        vector :: VectorType a -> a
        vector (Vector2Type t) = let x = single t in V2 x x

        single :: SingleType a -> a
        single (NumSingleType    t) = num t
        single (NonNumSingleType t) = nonnum t

        num :: NumType a -> a
        num (IntegralNumType t) | IntegralDict <- integralDict t = if i' == j' then 1 else 0
        num (FloatingNumType t) | FloatingDict <- floatingDict t = if i' == j' then 1 else 0

        nonnum :: NonNumType a -> a
        nonnum = undefined -- uh..?

    -- let_ :: (Elt a, Elt b)
    --      => PreOpenExp acc env'     aenv a
    --      -> PreOpenExp acc (env',a) aenv b
    --      -> PreOpenExp acc env'     aenv b
    -- let_ bnd body
    --   | Var{} <- bnd = inline body bnd
    --   | otherwise    = Let bnd body

    untup :: PreOpenExp acc env aenv (a,b) -> (PreOpenExp acc env aenv a, PreOpenExp acc env aenv b)
    untup (Tuple (SnocTup (SnocTup NilTup a) b)) = (a, b)

    primApp :: (Elt a, Elt r) => PrimFun (a -> r) -> PreOpenExp acc env aenv a -> PreOpenExp acc env aenv r
    primApp (PrimAdd t) (untup -> (u,v))
      = Let (cvtE u)
      $ Let (weakenE SuccIdx $ cvtE v)
      $ add t var0 var1

    primApp (PrimSub t) (untup -> (u,v))
      = Let (cvtE u)
      $ Let (weakenE SuccIdx $ cvtE v)
      $ sub t (cvtE var1) (cvtE var0)

    primApp (PrimMul t) (untup -> (u,v))
      = Let (cvtE u)
      $ Let (weakenE SuccIdx . cvtE $ v)
      $ Let (weakenE SuccIdx . weakenE SuccIdx $ u)
      $ Let (weakenE SuccIdx . weakenE SuccIdx . weakenE SuccIdx $ v)
      $ add t (mul t var3 var0) (mul t var1 var2)

    primApp (PrimNeg t) u
      = Let (cvtE u)
      $ negE t var0

    primApp (PrimAbs t) u
      = Let (cvtE u)
      $ (Cond
             (PrimApp
                (PrimGt $ NumSingleType t)
                (Tuple
                   (SnocTup
                      (SnocTup NilTup (Var ZeroIdx))
                      zero)))
             (Var ZeroIdx)
             (PrimApp
                (PrimNeg t)
                (Var ZeroIdx)))
      where zero = delta 0 1

    primApp (PrimSig _) _ = delta 0 1 -- zero

    primApp (PrimFDiv t) (untup -> (u,v))
      = Let (cvtE u)
      $ Let (weakenE SuccIdx . cvtE $ v)
      $ Let (weakenE SuccIdx . weakenE SuccIdx $ u)
      $ Let (weakenE SuccIdx . weakenE SuccIdx . weakenE SuccIdx $ v)
      $ fdiv t (sub f (mul f var3 var0) (mul f var2 var1)) (mul f var0 var0)
      where
        f = FloatingNumType t

    primApp (PrimRecip t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ negE f (mul f var0 (recipE t $ mul f var1 var1))
      where f = FloatingNumType t

    primApp (PrimSin t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (cosE t var0) var1
      where f = FloatingNumType t

    primApp (PrimCos t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (negE f $ sinE t var0) var1
      where f = FloatingNumType t

    primApp (PrimTan t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ Let (cosE t var0)
      $ mul f (recipE t $ mul f var0 var0) var2
      where f = FloatingNumType t

    primApp (PrimAsin t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (recipE t (sqrtE t $
                  sub f one
                  (mul f var0 var0)))
        var1
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimAcos t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (recipE t (sqrtE t $
                  sub f one (mul f var0 var0)))
        (negE f var1)
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimAtan t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f
        (recipE t (add f one (mul f var0 var0)))
        var1
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimSinh t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (coshE t var0) var1
      where f = FloatingNumType t

    primApp (PrimCosh t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (sinhE t var0) var1
      where f = FloatingNumType t

    primApp (PrimTanh t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (add f one
               (mul f var0 var0))
        var1
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimAsinh t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (recipE t (sqrtE t (add f one (mul f var0 var0)))) var1
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimAcosh t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (recipE t (sqrtE t (mul f
                                  (add f var0 one)
                                  (sub f var0 one))))
        var1
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimAtanh t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (recipE t (sub f (mul f var0 var0) one)) (negE f var1)
      where f = FloatingNumType t
            one = delta 0 0

    primApp (PrimExpFloating t) u
      = Let (cvtE u)
      $ Let (weakenE SuccIdx u)
      $ mul f (expE t var0) (var1)
      where
        f = FloatingNumType t

var0 :: Elt s => PreOpenExp acc (env,s) aenv s
var0 = Var ZeroIdx

var1 :: Elt s => PreOpenExp acc ((env,s),t) aenv s
var1 = Var (SuccIdx ZeroIdx)

var2 :: Elt s => PreOpenExp acc (((env,s),t),u) aenv s
var2 = Var (SuccIdx . SuccIdx $ ZeroIdx)

var3 :: Elt s => PreOpenExp acc ((((env,s),t),u),v) aenv s
var3 = Var (SuccIdx . SuccIdx . SuccIdx $ ZeroIdx)

applyRewriteExp
    :: (forall env' t'. PreOpenExp acc env' aenv t' -> PreOpenExp acc env' aenv t')
    -> PreOpenFun acc env aenv t
    -> PreOpenFun acc env aenv t
applyRewriteExp k (Body b) = Body (k b)
applyRewriteExp k (Lam f)  = Lam (applyRewriteExp k f)

applyRewriteAcc
    :: (forall aenv' t'. OpenAcc aenv' t' -> OpenAcc aenv' t')
    -> PreOpenAfun OpenAcc aenv t
    -> PreOpenAfun OpenAcc aenv t
applyRewriteAcc k (Abody b) = Abody (k b)
applyRewriteAcc k (Alam f)  = Alam (applyRewriteAcc k f)

-- applyRewriteAccDelay
--     :: (Arrays s, Arrays t) =>
--     (forall aenv' t' s'. DelayedOpenAcc aenv' t' -> DelayedOpenAcc aenv' s')
--     -> PreOpenAfun DelayedOpenAcc aenv t
--     -> PreOpenAfun DelayedOpenAcc aenv s
-- applyRewriteAccDelay k (Abody b) = Abody (k b)
-- applyRewriteAccDelay k (Alam f)  = Alam (_foo)


t1 :: Fun () (Int -> Float -> Float)
t1 = convertFun t1'

t1' :: A.Exp Int -> A.Exp Float -> A.Exp Float
t1' v u = u A.^ v

t2 :: Fun () (Float -> Float -> Float)
t2 = convertFun t2'

t2' :: A.Exp Float -> A.Exp Float -> A.Exp Float
t2' v u = v*v*v + u

t3' :: A.Exp Float -> A.Exp Float
t3' x = exp . exp . exp $ exp x

t3 :: Fun () (Float -> Float)
t3 = convertFun t3'
