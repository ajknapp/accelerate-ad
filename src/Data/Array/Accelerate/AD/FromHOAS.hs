{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}

module Data.Array.Accelerate.AD.FromHOAS ( fromHOAS, ($^) ) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Debug.Stats                            as Stats

import qualified Data.Array.Accelerate.Smart                        as S
import qualified Data.Array.Accelerate.Trafo.Sharing                as S

import Data.Proxy


-- Convenience function to convert a HOAS term into de Bruijn representation.
--
-- Requires AllowAmbiguousTypes.
--
fromHOAS
    :: forall acc aenv f. (FromHOAS f, Kit acc)
    => f
    -> AfunctionR acc aenv f
fromHOAS = fromHOAS' (Proxy :: Proxy f) . cvtAF
  where
    cvtAF :: f -> PreOpenAfun acc aenv (S.AfunctionR f)
    cvtAF = weaken open
          . fromOpenAfun
          . S.convertAfun True True True True

    open :: Idx () t -> Idx aenv t
    open = $internalError "fromHOAS" "unreachable"


-- Conversion from HOAS to de Bruijn form in such a way that it is easier to use
-- during the transform. The many arguments and fundeps are necessary because of
-- overlap.
--
type family AfunctionR (acc :: * -> * -> *) aenv f
type instance AfunctionR acc aenv (S.Acc a)      = acc aenv a
type instance AfunctionR acc aenv (S.Acc a -> r) = acc aenv a -> AfunctionR acc aenv r

class S.Afunction f => FromHOAS f where
  fromHOAS' :: Kit acc
            => proxy f
            -> PreOpenAfun acc aenv (S.AfunctionR f)
            -> AfunctionR  acc aenv f

instance Arrays a => FromHOAS (S.Acc a) where
  fromHOAS' _ (Abody a) = a
  fromHOAS' _ _         = $internalError "fromHOAS" "inconsistent valuation"

instance (Arrays a, FromHOAS b) => FromHOAS (S.Acc a -> b) where
  fromHOAS' _ = as
    where
      as :: Kit acc => PreOpenAfun acc aenv (a -> S.AfunctionR b) -> acc aenv a -> AfunctionR acc aenv b
      as (Alam f) = \a -> fromHOAS' (Proxy :: Proxy b) (rebindIndex f ZeroIdx `inlineA` extract a)
      as _        = $internalError "fromHOAS" "inconsistent valuation"

-- | Replace all occurrences of the first variable with the given array
-- expression. The environment shrinks.
--
inlineA :: Rebuildable f => f (aenv,s) t -> PreOpenAcc (AccClo f) aenv s -> f aenv t
inlineA f g = Stats.substitution "inlineA" $ rebuildA (subAtop g) f

rebindIndex
    :: (Kit acc, Arrays a)
    => PreOpenAfun acc aenv f
    -> Idx aenv a
    -> PreOpenAfun acc aenv f
rebindIndex (Alam  f) a   = Alam $ rebindIndex f (SuccIdx a)
rebindIndex (Abody b) idx
  =  Abody
  $^ Alet (inject $ Avar idx)
  $  weaken (this idx) b
  where
    this :: Idx aenv a -> Idx aenv s -> Idx (aenv,a) s
    this ix ix'
      | Just Refl <- matchIdx ix ix' = ZeroIdx
      | otherwise                    = SuccIdx ix'

infixr 0 $^
($^) :: Kit acc => (acc aenv a -> t) -> PreOpenAcc acc aenv a -> t
($^) f a = f $ inject a

