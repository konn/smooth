{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Numeric.Algebra.Smooth.Classes where

import qualified AlgebraicPrelude as AP
import Data.Sized (pattern Nil, pattern (:<))
import qualified Data.Sized as SV
import GHC.TypeNats
import qualified Numeric.Algebra as NA
import Numeric.Algebra.Smooth.Types

{- | \(C^\infty\)-ring, or <https://ncatlab.org/nlab/show/smooth+algebra smooth algebra>.

An \(\mathbb{R}\)-algebra \(W\) is called a /\(C^\infty\)-ring/,
or /smooth algebra/,
if for any smooth function \(f: \mathbb{R}^n \to \mathbb{R}\),
there is a lifted function \(W(f): W^n \to W\) which is compatible
with finite products.

In this package, we regard the notion of /smooth/ is captured by @'Floating'@ type-class: any function composed of 'Floating' functions would be regarded as /smooth/.
But this is not particularly true: even @'recip'@ and\/or @('/')@ are NOT smooth at \(x = 0\)!
Although such function with partial smooth domain must be treated carefully in theory, but in many cases, their (higher-order) value in a (smooth) domain could be safely computed with our machinery in general.

Typlical example is a ring of formal power series \(\mathbb{R}[\![\mathbf{X}]\!]\), implemented as 'Numeric.Algebra.Smooth.PowerSeries.Series' (unary) or
'Numeric.Algebra.Smooth.PowerSeries.PowerSeries' (multivariate).

Another important subclass of \(C^\infty\)-ring is @'Numeric.Algebra.Smooth.Weil.Weil'@ algebras.
Such algebras could be regarded as a real line with an additional infinitesimal strucure.
One typical example of Weil algebra is the ring \(\mathbb{R}[X]/X^2\) of @'Numeric.Algebra.Smooth.Dual.Dual'@ numbers and their products.
This ring is widely used to implement "forward mode" automatic differentiation.
-}
class
  ( NA.Module (AP.WrapFractional Double) w
  , NA.Ring w
  , NA.Commutative w
  ) =>
  SmoothRing w
  where
  liftSmooth ::
    KnownNat n =>
    (forall a. (Floating a) => Vec n a -> a) ->
    Vec n w ->
    w

liftUnary ::
  (SmoothRing w) =>
  (forall a. Floating a => a -> a) ->
  w ->
  w
liftUnary f = liftSmooth (f . SV.head) . SV.singleton

liftBinary ::
  forall w.
  (SmoothRing w) =>
  (forall a. Floating a => a -> a -> a) ->
  w ->
  w ->
  w
{-# INLINE liftBinary #-}
liftBinary f =
  \a b -> liftSmooth @w @2 (\(x :< (y :< (Nil :: Vec 0 a) :: Vec 1 a)) -> f x y) $ a :< b :< Nil
