{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wincomplete-patterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Numeric.Algebra.Smooth.PowerSeries.SuccinctTower where

import qualified AlgebraicPrelude as AP
import Control.Lens.Indexed (FunctorWithIndex (imap), ifoldMapBy)
import Control.Monad (join)
import Data.Coerce
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Sized (pattern Nil, pattern (:<))
import qualified Data.Sized as SV
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Natural
import Data.Type.Natural.Lemma.Arithmetic (succNonCyclic)
import Data.Type.Ordinal
import Data.Void (absurd)
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
  case sNat @n of
    Zero -> ZSeries a
    Succ (n :: SNat m) -> withKnownNat n $ SSeries a NullSeries (constSS @m a)

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
  ZSeries {} + SSeries {} = absurd $ succNonCyclic (sNat @n) Refl
  SSeries {} + ZSeries {} = absurd $ succNonCyclic (sNat @n) Refl

  NullSeries - a = negate a
  a - NullSeries = a
  ZSeries a - ZSeries b = ZSeries (a - b)
  SSeries a da dus - SSeries b db dvs =
    SSeries (a - b) (da - db) (dus - dvs)
  ZSeries {} - SSeries {} = absurd $ succNonCyclic (sNat @n) Refl
  SSeries {} - ZSeries {} = absurd $ succNonCyclic (sNat @n) Refl

  negate NullSeries = NullSeries
  negate (ZSeries a) = ZSeries $ negate a
  negate (SSeries a da dus) =
    SSeries (negate a) (negate da) (negate dus)
  NullSeries * _ = NullSeries
  _ * NullSeries = NullSeries
  ZSeries a * ZSeries b = ZSeries $ a * b
  l@(SSeries a da dus) * r@(SSeries b db dvs) =
    SSeries (a * b) (l * db + da * r) (dus * dvs)
  ZSeries {} * SSeries {} = absurd $ succNonCyclic (sNat @n) Refl
  SSeries {} * ZSeries {} = absurd $ succNonCyclic (sNat @n) Refl

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
  SSeries n a ->
  SSeries n a
{-# INLINE liftSSeries #-}
liftSSeries f df = \case
  NullSeries -> f (constSS 0.0)
  ZSeries a -> ZSeries (f a)
  x@(SSeries a da dus) ->
    SSeries (f a) (da * df x) (liftSSeries f df dus)

newtype SmoothFun c k = SmoothFun {runSmooth :: forall x. c x => Vec k x -> x}

{-
>>> inp1 = towerFromMap $ Map.fromList [(i :< j :< Nil, 2^i * 3^j :: Double) | i <- [0..2], j <- [0..4], even j]

>>> inp1
SSeries 1.0 (SSeries 2.0 (SSeries 4.0 NullSeries (SSeries 4.0 (SSeries 0.0 (SSeries 36.0 (SSeries 0.0 (SSeries 324.0 NullSeries (ZSeries 324.0)) NullSeries) (ZSeries 36.0)) NullSeries) (ZSeries 4.0))) (SSeries 2.0 (SSeries 0.0 (SSeries 18.0 (SSeries 0.0 (SSeries 162.0 NullSeries (ZSeries 162.0)) NullSeries) (ZSeries 18.0)) NullSeries) (ZSeries 2.0))) (SSeries 1.0 (SSeries 0.0 (SSeries 9.0 (SSeries 0.0 (SSeries 81.0 NullSeries (ZSeries 81.0)) NullSeries) (ZSeries 9.0)) NullSeries) (ZSeries 1.0))

>>> liftNAry @Floating (\(x :< y :< Nil) -> x * y) (SmoothFun (\(x :< y :< Nil) -> y) :< SmoothFun (\(x :< y :< Nil) -> x) :< Nil) (inp1 :< inp1 :< Nil)

-}

liftNAry ::
  forall c n a m.
  ( KnownNat n
  , KnownNat m
  , Num a
  , c a
  , forall x k. (KnownNat k, c x) => c (SSeries k x)
  ) =>
  -- | @f@, a @m@-ary function
  (forall x. c x => Vec m x -> x) ->
  -- | partial derivatives of @f@, with @i@th element
  -- is a first-order derivative w.r.t. @i@th variable.
  Vec m (SmoothFun c m) ->
  Vec m (SSeries n a) ->
  SSeries n a
liftNAry = go @n
  where
    go ::
      forall l.
      (KnownNat l) =>
      (forall x. c x => Vec m x -> x) ->
      Vec m (SmoothFun c m) ->
      Vec m (SSeries l a) ->
      SSeries l a
    go f _ Nil = constSS $ f Nil
    go f dfs xss =
      case sNat @l of
        Zero -> ZSeries $ f $ unwrapZSeries <$> xss
        Succ (k :: SNat k) ->
          withKnownNat k $
            SSeries
              (f $ constTerm <$> xss)
              ( sum $
                  SV.zipWithSame
                    ( \fi gi ->
                        topDiffed gi * runSmooth fi xss
                    )
                    dfs
                    xss
              )
              (go f dfs $ diffOther <$> xss)

constTerm :: (KnownNat n, Num a) => SSeries n a -> a
{-# INLINE constTerm #-}
constTerm = \case
  NullSeries -> 0
  ZSeries a -> a
  SSeries a _ _ -> a

topDiffed :: SSeries (n + 1) a -> SSeries (n + 1) a
topDiffed = \case
  NullSeries -> NullSeries
  SSeries _ df _ -> df
  ZSeries {} -> absurd $ succNonCyclic (sNat @0) Refl

diffOther :: SSeries (n + 1) a -> SSeries n a
diffOther = \case
  NullSeries -> NullSeries
  SSeries _ _ f -> f
  ZSeries {} -> absurd $ succNonCyclic (sNat @0) Refl

unwrapZSeries :: Num a => SSeries 0 a -> a
unwrapZSeries NullSeries = 0
unwrapZSeries (ZSeries a) = a
unwrapZSeries SSeries {} =
  absurd $ succNonCyclic (sNat @0) Refl

instance (KnownNat n, Floating a) => Floating (SSeries n a) where
  pi = constSS pi
  exp = liftSSeries exp exp
  {-# INLINE exp #-}
  log = liftSSeries log recip
  {-# INLINE log #-}
  sin = liftSSeries sin cos
  {-# INLINE sin #-}
  cos = liftSSeries cos (negate . sin)
  {-# INLINE cos #-}
  tan = liftSSeries tan (recip . join (*) . cos)
  {-# INLINE tan #-}
  asin = liftSSeries asin (recip . sqrt . (1 -) . join (*))
  {-# INLINE asin #-}
  acos = liftSSeries acos (negate . recip . sqrt . (1 -) . join (*))
  {-# INLINE acos #-}
  atan = liftSSeries atan (recip . (+ 1) . join (*))
  {-# INLINE atan #-}
  sinh = liftSSeries sinh cosh
  {-# INLINE sinh #-}
  cosh = liftSSeries cosh sinh
  {-# INLINE cosh #-}
  tanh = liftSSeries tanh (join (*) . recip . cosh)
  asinh = liftSSeries asinh (recip . sqrt . (1 +) . join (*))
  acosh = liftSSeries acosh (recip . sqrt . (1 +) . join (*))
  atanh = liftSSeries atanh (recip . (1 -) . join (*))

asNth :: (KnownNat n, Num a) => Ordinal n -> a -> SSeries n a
asNth (OLt (k :: SNat k)) a = withKnownNat k $ asNth' @k a

-- | inject a coefficient as an @n@th variable.
asNth' ::
  forall k n a.
  (KnownNat k, KnownNat n, (k + 1) <= n, Num a) =>
  a ->
  SSeries n a
asNth' a = go (sNat @k) (sNat @n)
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

cutoff :: forall n a. (KnownNat n) => UVec n Word -> SSeries n a -> Map (UVec n Word) a
cutoff = go 0
  where
    go ::
      forall m.
      KnownNat m =>
      Word ->
      UVec m Word ->
      SSeries m a ->
      Map (UVec m Word) a
    go _ _ NullSeries = Map.empty
    go _ _ (ZSeries a) = Map.singleton Nil a
    go !n ((!ub) :< ubs) (SSeries x dx dus)
      | n == ub =
        Map.insert pow x $ Map.mapKeysMonotonic (n :<) (go 0 ubs dus)
      | otherwise =
        Map.insert pow x $
          go (n + 1) (ub :< ubs) dx
            `Map.union` Map.mapKeysMonotonic (n :<) (go 0 ubs dus)
      where
        pow = n :< SV.replicate' 0
    go _ Nil SSeries {} = absurd $ succNonCyclic (sNat @1) Refl

-- >>> allDerivs (\(x SV.:< y SV.:< SV.Nil) -> x ^ 2 * y) (3 SV.:< 2 SV.:< SV.Nil)
-- SSeries 18 (SSeries 12 (SSeries 4 NullSeries (SSeries 4 (SSeries 2 NullSeries (ZSeries 2)) (ZSeries 4))) (SSeries 12 (SSeries 6 NullSeries (ZSeries 6)) (ZSeries 12))) (SSeries 18 (SSeries 9 NullSeries (ZSeries 9)) (ZSeries 18))

-- >>> towerFromMap $ Map.fromList [(i :< j :< Nil, 2^i * 3^j) | i <- [0..2], j <- [0..4], even j]
-- SSeries 1 (SSeries 2 (SSeries 4 NullSeries (SSeries 4 (SSeries 0 (SSeries 36 (SSeries 0 (SSeries 324 NullSeries (ZSeries 324)) NullSeries) (ZSeries 36)) NullSeries) (ZSeries 4))) (SSeries 2 (SSeries 0 (SSeries 18 (SSeries 0 (SSeries 162 NullSeries (ZSeries 162)) NullSeries) (ZSeries 18)) NullSeries) (ZSeries 2))) (SSeries 1 (SSeries 0 (SSeries 9 (SSeries 0 (SSeries 81 NullSeries (ZSeries 81)) NullSeries) (ZSeries 9)) NullSeries) (ZSeries 1))

towerFromMap ::
  forall n a.
  (KnownNat n, Num a) =>
  Map (UVec n Word) a ->
  SSeries n a
towerFromMap =
  go 0
    <$> ifoldMapBy (SV.zipWith max) (SV.replicate' 0) const
    <*> id
  where
    go ::
      forall m.
      KnownNat m =>
      -- | Current power
      Word ->
      -- | Upperbounds of power
      UVec m Word ->
      -- | Coefficient dictionary
      Map (UVec m Word) a ->
      SSeries m a
    go !_ Nil dic = maybe NullSeries ZSeries $ Map.lookup Nil dic
    go !x ubss@(ub :< ubs) dic =
      let pow = (x :< SV.replicate' 0)
          cont
            | x == ub = NullSeries
            | otherwise = go (x + 1) ubss dic
          subDic =
            Map.mapKeysMonotonic SV.tail $
              fst $
                Map.split (x + 1 :< SV.replicate' 0) $
                  if x > 0
                    then
                      let (_, eq, gt) = Map.splitLookup pow dic
                       in maybe id (Map.insert pow) eq gt
                    else dic
       in SSeries (fromMaybe 0 $ Map.lookup pow dic) cont $
            go 0 ubs subDic
