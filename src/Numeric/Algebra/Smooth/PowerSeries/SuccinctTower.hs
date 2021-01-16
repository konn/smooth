{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall -Wincomplete-patterns #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Numeric.Algebra.Smooth.PowerSeries.SuccinctTower where

import qualified AlgebraicPrelude as AP
import Control.Lens.Indexed (FunctorWithIndex (imap))
import Control.Monad (join)
import Data.Coerce
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Singletons (sing)
import Data.Singletons.TypeLits (SNat, withKnownNat)
import qualified Data.Sized as SV
import Data.Sized.Builtin (pattern Nil, pattern (:<))
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Natural.Class
  ( IsPeano (succNonCyclic),
    PNum (type (+)),
    pattern Succ,
    pattern Zero,
  )
import Data.Type.Ordinal
import Data.Void (absurd)
import Debug.Trace (trace)
import GHC.TypeNats (KnownNat, Nat, type (<=))
import qualified Numeric.Algebra as NA
import Numeric.Algebra.Smooth.Classes
import Numeric.Algebra.Smooth.Types
import Numeric.Natural (Natural)

data SSeries (n :: Nat) a where
  NullSeries :: SSeries n a
  ZSeries :: !a -> SSeries 0 a
  SSeries :: !a -> SSeries (n + 1) a -> SSeries n a -> SSeries (n + 1) a

deriving instance Functor (SSeries n)

deriving instance Show a => Show (SSeries n a)

deriving instance Eq a => Eq (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Additive (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.LeftModule Natural (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.RightModule Natural (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Monoidal (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.LeftModule Integer (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.RightModule Integer (SSeries n a)

instance
  (KnownNat n, Num a, Fractional a) =>
  NA.RightModule (AP.WrapFractional Double) (SSeries n a)
  where
  (*.) = coerce $ flip (flip (*) . realToFrac @Double @(SSeries n a))

instance
  (KnownNat n, Num a, Fractional a) =>
  NA.LeftModule (AP.WrapFractional Double) (SSeries n a)
  where
  (.*) = coerce $ (*) . realToFrac @Double @(SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Group (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Multiplicative (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Commutative (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Abelian (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Semiring (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Rig (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Unital (SSeries n a)

deriving via
  (AP.WrapNum (SSeries n a))
  instance
    (KnownNat n, Num a) =>
    NA.Ring (SSeries n a)

constSS :: forall n a. (KnownNat n, Num a) => a -> SSeries n a
constSS a =
  case sing @n of
    Zero -> ZSeries a
    Succ (n :: SNat m) -> withKnownNat n $ SSeries a NullSeries (constSS @m a)
    _ -> error "Could not happen"

extractCoe :: Num a => SSeries n a -> a
extractCoe NullSeries = 0
extractCoe (ZSeries a) = a
extractCoe (SSeries a _ _) = a

instance (Num a, KnownNat n) => Num (SSeries n a) where
  fromInteger 0 = NullSeries
  fromInteger n = constSS $ fromInteger n
  abs NullSeries = NullSeries
  abs (ZSeries a) = ZSeries $ abs a
  abs (SSeries a da dus) =
    SSeries (abs a) (signum da) (abs dus)
  signum NullSeries = NullSeries
  signum (ZSeries a) = ZSeries $ signum a
  signum (SSeries a _ dus) = SSeries (signum a) NullSeries (signum dus)
  NullSeries + r = r
  l + NullSeries = l
  ZSeries a + ZSeries b = ZSeries (a + b)
  SSeries a da dus + SSeries b db dvs =
    SSeries (a + b) (da + db) (dus + dvs)
  _ + _ = absurd $ succNonCyclic (sing @n) Refl
  NullSeries - a = negate a
  a - NullSeries = a
  ZSeries a - ZSeries b = ZSeries (a - b)
  SSeries a da dus - SSeries b db dvs =
    SSeries (a + b) (da + db) (dus + dvs)
  _ - _ = absurd $ succNonCyclic (sing @n) Refl
  negate NullSeries = NullSeries
  negate (ZSeries a) = ZSeries $ negate a
  negate (SSeries a da dus) =
    SSeries (negate a) (negate da) (negate dus)
  NullSeries * _ = NullSeries
  _ * NullSeries = NullSeries
  ZSeries a * ZSeries b = ZSeries $ a * b
  l@(SSeries a da dus) * r@(SSeries b db dvs) =
    SSeries (a * b) (l * db + da * r) (dus * dvs)
  _ * _ = absurd $ succNonCyclic (sing @n) Refl

instance (KnownNat n, Fractional a) => Fractional (SSeries n a) where
  fromRational 0 = NullSeries
  fromRational n = constSS $ fromRational n
  recip NullSeries = constSS (recip 0)
  recip (ZSeries a) = ZSeries $ recip a
  recip l@(SSeries a da dus) =
    SSeries (recip a) (- da * recip (l * l)) (recip dus)
  a / b = a * recip b

liftSSeries ::
  (KnownNat n, Floating a) =>
  (forall x. Floating x => x -> x) ->
  (forall x. Floating x => x -> x) ->
  Maybe (SSeries n a) ->
  SSeries n a ->
  SSeries n a
{-# INLINE liftSSeries #-}
liftSSeries f df mIfZero = \case
  NullSeries -> fromMaybe (constSS (f 0.0)) mIfZero
  ZSeries a -> ZSeries (f a)
  x@(SSeries a da dus) ->
    SSeries (f a) (da * df x) (f dus)

instance (KnownNat n, Floating a) => Floating (SSeries n a) where
  pi = constSS pi
  exp = liftSSeries exp exp (Just 1.0)
  {-# INLINE exp #-}
  log = liftSSeries log recip Nothing
  {-# INLINE log #-}
  sin = liftSSeries sin cos (Just NullSeries)
  {-# INLINE sin #-}
  cos = liftSSeries cos (negate . sin) (Just 1.0)
  {-# INLINE cos #-}
  tan = liftSSeries tan (recip . join (*) . cos) (Just NullSeries)
  {-# INLINE tan #-}
  asin = liftSSeries asin (recip . sqrt . (1 -) . join (*)) (Just NullSeries)
  {-# INLINE asin #-}
  acos = liftSSeries acos (negate . recip . sqrt . (1 -) . join (*)) Nothing
  {-# INLINE acos #-}
  atan = liftSSeries atan (recip . (+ 1) . join (*)) (Just NullSeries)
  {-# INLINE atan #-}
  sinh = liftSSeries sinh cosh (Just NullSeries)
  {-# INLINE sinh #-}
  cosh = liftSSeries cosh sinh (Just 1.0)
  {-# INLINE cosh #-}
  tanh = liftSSeries tanh (join (*) . recip . cosh) (Just NullSeries)
  asinh = liftSSeries asinh (recip . sqrt . (1 +) . join (*)) (Just NullSeries)
  acosh = liftSSeries acosh (recip . sqrt . (1 +) . join (*)) Nothing
  atanh = liftSSeries atanh (recip . (1 -) . join (*)) (Just NullSeries)

asNth :: (KnownNat n, Num a) => Ordinal n -> a -> SSeries n a
asNth (OLt (k :: SNat k)) a = withKnownNat k $ asNth' @k a

-- | inject a coefficient as an @n@th variable.
asNth' ::
  forall k n a.
  (KnownNat k, KnownNat n, (k + 1) <= n, Num a) =>
  a ->
  SSeries n a
asNth' a = go (sing @k) (sing @n)
  where
    go ::
      forall l m.
      (KnownNat l, KnownNat m, (l + 1) <= m) =>
      SNat l ->
      SNat m ->
      SSeries m a
    go Zero (Succ _) = SSeries a (SSeries 1 NullSeries (constSS 1)) (constSS a)
    go (Succ n) (Succ m) =
      SSeries a NullSeries (go n m)
    go _ _ = error "impossible"

allDerivs ::
  (KnownNat n, Num a) =>
  (Vec n (SSeries n a) -> SSeries n a) ->
  Vec n a ->
  SSeries n a
allDerivs f =
  f . imap asNth

instance (KnownNat n, Floating a) => SmoothRing (SSeries n a) where
  liftSmooth = ($)

cutoff :: forall n a. (Show a, KnownNat n) => UVec n Word -> SSeries n a -> Map (UVec n Word) a
cutoff = go (SV.replicate' 0)
  where
    go ::
      forall m.
      KnownNat m =>
      UVec m Word ->
      UVec m Word ->
      SSeries m a ->
      Map (UVec m Word) a
    go _ _ NullSeries = Map.empty
    go _ _ (ZSeries a) = Map.singleton Nil a
    go Nil _ SSeries {} = absurd $ succNonCyclic (sing @m) Refl
    go _ Nil SSeries {} = absurd $ succNonCyclic (sing @m) Refl
    go pow@((!n) :< rest) ((!ub) :< ubs) (SSeries x dx dus)
      | n == ub =
        Map.insert pow x $ Map.mapKeysMonotonic (n :<) (go rest ubs dus)
      | otherwise =
        Map.insert pow x $
          go (n + 1 :< rest) (ub :< ubs) dx
            `Map.union` Map.mapKeysMonotonic (n :<) (go rest ubs dus)

-- >>> allDerivs (\(x SV.:< y SV.:< SV.NilR) -> x ^ 2 * y) (3 SV.:< 2 SV.:< SV.NilR)
-- SSeries 18 (SSeries 12 (SSeries 4 NullSeries (SSeries 4 (SSeries 2 NullSeries (ZSeries 2)) (ZSeries 4))) (SSeries 12 (SSeries 6 NullSeries (ZSeries 6)) (ZSeries 12))) (SSeries 18 (SSeries 9 NullSeries (ZSeries 9)) (ZSeries 18))
