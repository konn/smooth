{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-type-defaults -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}

module Main where

import Algebra.Prelude.Core as AP hiding ((*), (+), (-), (/), (^))
import Algebra.Ring.Polynomial.Class (PrettyCoeff)
import Algebra.Ring.Polynomial.Univariate hiding (cutoff)
import AlgebraicPrelude (WrapNum (..))
import Data.Reflection
import Data.Sized hiding (fmap, (!!))
import qualified Data.Sized as SV
import GHC.TypeLits (KnownSymbol)
import Numeric.Algebra.Smooth
import Numeric.Algebra.Smooth.Types (UVec, Vec)
import Numeric.Algebra.Smooth.Weil
import Symbolic
import Prelude ((*), (+), (-), (/), (^))
import qualified Prelude as P

-- * Examples of Higher-order derivatives

-- Let's calculate the derivatives of f x = exp x * sin x up to the fourth.

-- Here, f', f'2, ..., f'4 are _manually_ calculated derivative of @f@.
f, f', f'2, f'3, f'4 :: (Floating x) => x -> x
f x = exp x * sin x
f' x = exp x * sin x + exp x * cos x
f'2 x = 2 * exp x * cos x
f'3 x = 2 * (exp x * cos x - exp x * sin x)
f'4 x = -4 * f x

{-
Let's alcualte the differential coefficients at pi/6 up to fourth, manually.:

>>> AP.map ($ pi/6) [f, f', f'2, f'3, f'4]

Then we calculate it using multiple dual numbers (by Theorem 2):

>>> f (pi/6 + di 0 + di 1 + di 2 + di 3) :: Weil (Duals 4) Double

As stated in the paper, repeating dual numbers has bad time- and space-complexity (it grows exponentially!).
We can use R[X]/(X^{n+1}) instead (Lemma 2):

>>> f (pi/6 + di 0) :: Weil (DOrder 4) Double

Note that R[X]/(X^{n+1}) gives the @k@ th coefficient modulo \(1/k!\).

The 'diffUpTo' function indeed using this approach:

>>> diffUpTo 4 f $ pi/6
-}

-- * Symbolic Computation and Autoamtic differentiation

{-
As our implementation is polymorphic enough, we can "recover" symbolic differentiation by feeding 'Symbolic' type into automatic differentiation!

>>> normalise <$> diffUpTo 4 f #x
-}

-- * Partial derivatives.

{-
Let's calculate the partial derivatives up to second-order w.r.t. x and the first w.r.t. y.

We can use the smooth structure of R[X]/(X^3) ⨂ R[Y]/(Y^2).
-}
δ1 :: (Eq a, Floating a) => Weil (DOrder 3 |*| DOrder 2) a
δ1 = di 0

δ2 :: (Eq a, Floating a) => Weil (DOrder 3 |*| DOrder 2) a
δ2 = di 1

-- >>> import Data.Reflection
-- >>> reflect $ Proxy @(DOrder 4 |*| DOrder 3)

f2 :: Floating r => r -> r -> r
f2 x y = sin x * cos y

-- >>> f2 #x #y :: Symbolic

-- >>> normalise <$> f2 (#x + δ1) (#y + δ2)

-- * Counterexample detection

-- R[X]/(X^3 - 1) must be rejected, as it is a finite-dimensional algebra, but not Weil.

{-
>>> isWeil (toIdeal [var 0 ^3 - 1 :: Polynomial _ 1])
-}

-- Nothing means "it is not a Weil algebra!" so it rejects its input as expected!

-- Another exmaple: R[x,y]/(x^3-y), which is not finite-dimensional at all!

-- >>> isWeil (toIdeal [var 0 ^3 - var 1 :: Polynomial _ 2])

-- Rejected as expected!

-- * General Weil algebra computation

-- Let's gather Weil settings for R[e] = R[X]/(X^4).

idealX4 :: Ideal (Polynomial AP.Rational 1)
idealX4 = toIdeal [var 0 ^ 4]

{-
Let's calculate its Weil setting (Algorithm 1):

>>> isWeil idealX4

It's indeed a Weil algebra!
It has e^0 (=1), e^1, e^2, e^3 as its basis with of maximum degree three.
The 'table' field gives its mulitplication table (trivial in this case, though).

Let's see if this behaves correctly.
-}

ε :: (Eq a, Floating a) => Weil (DOrder 4) a
ε = di 0

{-
>>> normalise <$> cos (#x + ε)

It indeed gives differential coefficients up to the third (modulo factorial)!
-}

-- Let's see more complex, genral case:
-- R[e,d] = R[x, y]/(x^2 - y, y^2)

red :: Ideal (Polynomial AP.Rational 2)
red = toIdeal [x ^ 2 - y ^ 3, y ^ 4]
  where
    [x, y] = vars

-- >>> isWeil red

-- Indeed it is Weil.
--
-- What if we feed  π/4 + d0 + d1 to sin?

-- >>> withWeil @Double red (sin ((pi/4) + di 0 + di 1))

-- We can also feed symbolic types:

-- >>> withWeil red (normalise <$> sin (#x + di 0 + di 1))

main :: IO ()
main = return ()

errdegs :: UVec 2 Word
errdegs = 3 :< 4 :< Nil

errInps :: Vec 2 Double
errInps = 3 :< 18 :< Nil

interped :: Floating x => x -> x -> x
interped x y =
  atan (0.8 * (y ^ 2 * cos x))

thef :: forall x. Floating x => Vec 2 x -> x
thef (x :< (y :< (Nil :: Vec 0 x) :: Vec 1 x)) = interped x y

type family Duals n where
  Duals 1 = D1
  Duals n = D1 |*| Duals (n - 1)

d0, d1, d2 :: (Eq x, Floating x) => Weil (Duals 3) x
[d0, d1, d2] = P.map di [0 ..]

{-
>>> (sin (pi/6), cos (pi/6), -sin(pi/6), -cos(pi/6))

>>> sin (pi/6 + d0 + d1 + d2) :: Weil (Duals 3) Double

>>> normalise <$> sin (injCoeWeil x + d0 + d1 + d2)
 -}

eps :: (Eq a, Floating a) => Weil (DOrder 4) a
eps = di 0

{-
>>> (sin (pi/6), cos (pi/6), -sin(pi/6)/2, -cos(pi/6)/6)
(0.49999999999999994,0.8660254037844387,-0.24999999999999997,-0.14433756729740646)

>>> normalise <$> sin (#x + eps)
((-1.0) * cos x / 6.0) d(0)^3 + ((- (sin x)) / 2.0) d(0)^2 + (cos x) d(0) + (sin x)
-}

eps1, eps2 :: (Eq x, Floating x) => Weil (DOrder 3 |*| DOrder 2) x
[eps1, eps2] = P.map di [0 ..]

fun :: (Eq x, Floating x) => x -> x -> x
fun x y = exp (2 * x) * sin y

-- >>> fun (2 + eps1) (pi/6 + eps2) :: Weil (DOrder 3 |*| DOrder 2) Double

-- >>> normalise <$> fun (#x + eps1) (#y + eps2)
-- (4.0 * exp (2.0 * x) / 2.0 * cos y) d(0)^2 d(1) + (4.0 * exp (2.0 * x) / 2.0 * sin y) d(0)^2 + (2.0 * exp (2.0 * x) * cos y) d(0) d(1) + (2.0 * exp (2.0 * x) * sin y) d(0) + (exp (2.0 * x) * cos y) d(1) + (exp (2.0 * x) * sin y)

{-
>>> diffUpTo 9 atan x
-}

{-
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Numeric.Algebra.Smooth.PowerSeries.SuccinctTower
>>> import Numeric.Algebra.Smooth
>>> normalise <$> cutoff (2 :< 3 :< Nil) (allDerivs (\vec -> sin (SV.head vec) * exp (SV.last vec * SV.head vec)) (#x :< #y :< Nil))
fromList [([0,0],sin x * exp (y * x)),([0,1],sin x * x * exp (y * x)),([0,2],sin x * x * x * exp (y * x)),([0,3],sin x * x * x * x * exp (y * x)),([1,0],sin x * y * exp (y * x) + cos x * exp (y * x)),([1,1],sin x * (y * x * exp (y * x) + exp (y * x)) + cos x * x * exp (y * x)),([1,2],sin x * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + cos x * x * x * exp (y * x)),([1,3],sin x * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + cos x * x * x * x * exp (y * x)),([2,0],sin x * y * y * exp (y * x) + cos x * y * exp (y * x) + cos x * y * exp (y * x) + (- (sin x)) * exp (y * x)),([2,1],sin x * (y * (y * x * exp (y * x) + exp (y * x)) + y * exp (y * x)) + cos x * (y * x * exp (y * x) + exp (y * x)) + cos x * (y * x * exp (y * x) + exp (y * x)) + (- (sin x)) * x * exp (y * x)),([2,2],sin x * (y * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + y * x * exp (y * x) + exp (y * x) + y * x * exp (y * x) + exp (y * x)) + cos x * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + cos x * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + (- (sin x)) * x * x * exp (y * x)),([2,3],sin x * (y * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x) + y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x) + y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + cos x * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + cos x * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + (- (sin x)) * x * x * x * exp (y * x))]
-}

instance
  ( c ~ Symbolic
  , Reifies i (WeilSettings n m)
  , KnownNat n
  , KnownNat m
  , KnownSymbol sym
  ) =>
  IsLabel sym (Weil i c)
  where
  fromLabel = injCoeWeil $ fromLabel @sym @Symbolic
  {-# INLINE fromLabel #-}
