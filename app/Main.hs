{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Data.Sized hiding (fmap, (!!))
import qualified Data.Sized as SV
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
[0.8440458974822341,2.305976275841536,2.9238607567186037,1.2357689617541354,-3.3761835899289365]

Then we calculate it using multiple dual numbers (by Theorem 2):

>>> f (pi/6 + di 0 + di 1 + di 2 + di 3) :: Weil (Duals 4) Double
-3.3761835899289347 d(0) d(1) d(2) d(3) + 1.2357689617541352 d(0) d(1) d(2) + 1.2357689617541352 d(0) d(1) d(3) + 1.2357689617541352 d(0) d(2) d(3) + 1.2357689617541352 d(1) d(2) d(3) + 2.9238607567186037 d(0) d(1) + 2.9238607567186037 d(0) d(2) + 2.9238607567186037 d(1) d(2) + 2.9238607567186037 d(0) d(3) + 2.9238607567186037 d(1) d(3) + 2.9238607567186037 d(2) d(3) + 2.305976275841536 d(0) + 2.305976275841536 d(1) + 2.305976275841536 d(2) + 2.305976275841536 d(3) + 0.8440458974822341

As stated in the paper, repeating dual numbers has bad time- and space-complexity (it grows exponentially!).
We can use R[X]/(X^{n+1}) instead (Lemma 2):

>>> f (pi/6 + di 0) :: Weil (DOrder 4) Double
0.20596149362568922 d(0)^3 + 1.4619303783593018 d(0)^2 + 2.305976275841536 d(0) + 0.8440458974822341

Note that R[X]/(X^{n+1}) gives the @k@ th coefficient modulo \(1/k!\).

The 'diffUpTo' function indeed using this approach:

>>> diffUpTo 4 f $ pi/6
fromList [(0,0.8440458974822341),(1,2.305976275841536),(2,2.9238607567186037),(3,1.2357689617541352),(4,-3.3761835899289365)]
-}

-- * Symbolic Computation and Autoamtic differentiation

{-
As our implementation is polymorphic enough, we can "recover" symbolic differentiation by feeding 'Symbolic' type into automatic differentiation!

>>> normalise <$> diffUpTo 4 f x
fromList [(0,exp x * sin x),(1,exp x * cos x + exp x * sin x),(2,2.0 * (exp x * ((- (sin x)) / 2.0) + exp x * cos x + exp x / 2.0 * sin x)),(3,6.0 * (exp x * ((-1.0) * cos x / 6.0) + exp x * ((- (sin x)) / 2.0) + exp x / 2.0 * cos x + exp x / 6.0 * sin x)),(4,24.0 * (exp x * ((-1.0) * (- (sin x)) / 24.0) + exp x * ((-1.0) * cos x / 6.0) + exp x / 2.0 * ((- (sin x)) / 2.0) + exp x / 6.0 * cos x + exp x / 24.0 * sin x))]
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
-- WeilSettings {weilBasis = [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2],[2,0],[2,1],[2,2],[3,0],[3,1],[3,2]], nonZeroVarMaxPowers = [3,2], weilMonomDic = fromList [([0,2],[0,0,1,0,0,0,0,0,0,0,0,0]),([1,1],[0,0,0,0,1,0,0,0,0,0,0,0]),([2,1],[0,0,0,0,0,0,0,1,0,0,0,0]),([3,0],[0,0,0,0,0,0,0,0,0,1,0,0]),([3,1],[0,0,0,0,0,0,0,0,0,0,1,0]),([1,0],[0,0,0,1,0,0,0,0,0,0,0,0]),([2,2],[0,0,0,0,0,0,0,0,1,0,0,0]),([2,0],[0,0,0,0,0,0,1,0,0,0,0,0]),([1,2],[0,0,0,0,0,1,0,0,0,0,0,0]),([0,1],[0,1,0,0,0,0,0,0,0,0,0,0]),([0,0],[1,0,0,0,0,0,0,0,0,0,0,0]),([3,2],[0,0,0,0,0,0,0,0,0,0,0,1])], table = fromList [((0,0),1),((2,6),X_0^2*X_1^2),((1,3),X_0*X_1),((0,1),X_1),((3,8),X_0^3*X_1^2),((0,2),X_1^2),((1,1),X_1^2),((0,3),X_0),((0,4),X_0*X_1),((1,7),X_0^2*X_1^2),((0,5),X_0*X_1^2),((2,3),X_0*X_1^2),((1,6),X_0^2*X_1),((0,6),X_0^2),((0,7),X_0^2*X_1),((1,4),X_0*X_1^2),((0,8),X_0^2*X_1^2),((4,4),X_0^2*X_1^2),((0,9),X_0^3),((1,10),X_0^3*X_1^2),((5,6),X_0^3*X_1^2),((0,10),X_0^3*X_1),((4,6),X_0^3*X_1),((1,9),X_0^3*X_1),((3,3),X_0^2),((0,11),X_0^3*X_1^2),((4,7),X_0^3*X_1^2),((3,5),X_0^2*X_1^2),((3,4),X_0^2*X_1),((3,7),X_0^3*X_1),((2,9),X_0^3*X_1^2),((3,6),X_0^3)]}

f2 :: Floating r => r -> r -> r
f2 x y = sin x * cos y

-- >>> f2 x y
-- sin x * cos y

-- >>> normalise <$> f2 (injCoeWeil x + δ1) (injCoeWeil y + δ2)
-- ((- (sin x)) / 2.0 * (- (sin y))) d(0)^2 d(1) + ((- (sin x)) / 2.0 * cos y) d(0)^2 + (cos x * (- (sin y))) d(0) d(1) + (cos x * cos y) d(0) + (sin x * (- (sin y))) d(1) + (sin x * cos y)

-- * Counterexample detection

-- R[X]/(X^3 - 1) must be rejected, as it is a finite-dimensional algebra, but not Weil.

{-
>>> isWeil (toIdeal [var 0 ^3 - 1 :: Polynomial _ 1])
Nothing
-}

-- Nothing means "it is not a Weil algebra!" so it rejects its input as expected!

-- Another exmaple: R[x,y]/(x^3-y), which is not finite-dimensional at all!

-- >>> isWeil (toIdeal [var 0 ^3 - var 1 :: Polynomial _ 2])
-- Nothing

-- Rejected as expected!

-- * General Weil algebra computation

-- Let's gather Weil settings for R[e] = R[X]/(X^4).

idealX4 :: Ideal (Polynomial AP.Rational 1)
idealX4 = toIdeal [var 0 ^ 4]

{-
Let's calculate its Weil setting (Algorithm 1):

>>> isWeil idealX4
Just (SomeWeil (WeilSettings {weilBasis = [[0],[1],[2],[3]], nonZeroVarMaxPowers = [3], weilMonomDic = fromList [([0],[1,0,0,0]),([1],[0,1,0,0]),([2],[0,0,1,0]),([3],[0,0,0,1])], table = fromList [((0,0),1),((0,1),X_0),((1,2),X_0^3),((0,2),X_0^2),((1,1),X_0^2),((0,3),X_0^3)]}))

It's indeed a Weil algebra!
It has e^0 (=1), e^1, e^2, e^3 as its basis with of maximum degree three.
The 'table' field gives its mulitplication table (trivial in this case, though).

Let's see if this behaves correctly.
-}

ε :: (Eq a, Floating a) => Weil (DOrder 4) a
ε = di 0

{-
>>> normalise <$> cos (injCoeWeil x + ε)
((-1.0) * (- (sin x)) / 6.0) d(0)^3 + ((-1.0) * cos x / 2.0) d(0)^2 + (- (sin x)) d(0) + (cos x)

It indeed gives differential coefficients up to the third (modulo factorial)!
-}

-- Let's see more complex, genral case:
-- R[e,d] = R[x, y]/(x^2 - y, y^2)

red :: Ideal (Polynomial AP.Rational 2)
red = toIdeal [x ^ 2 - y ^ 3, y ^ 4]
  where
    [x, y] = vars

-- >>> isWeil red
-- Just (SomeWeil (WeilSettings {weilBasis = [[0,0],[0,1],[1,0],[0,2],[1,1],[2,0],[1,2],[3,0]], nonZeroVarMaxPowers = [3,3], weilMonomDic = fromList [([0,2],[0,0,0,1,0,0,0,0]),([1,1],[0,0,0,0,1,0,0,0]),([3,0],[0,0,0,0,0,0,0,1]),([1,0],[0,0,1,0,0,0,0,0]),([0,3],[0,0,0,0,0,1,0,0]),([2,0],[0,0,0,0,0,1,0,0]),([1,2],[0,0,0,0,0,0,1,0]),([0,1],[0,1,0,0,0,0,0,0]),([0,0],[1,0,0,0,0,0,0,0]),([1,3],[0,0,0,0,0,0,0,1])], table = fromList [((0,0),1),((1,3),X_0^2),((0,1),X_1),((1,2),X_0*X_1),((0,2),X_0),((1,1),X_1^2),((0,3),X_1^2),((2,5),X_0^3),((0,4),X_0*X_1),((2,2),X_0^2),((0,5),X_0^2),((2,3),X_0*X_1^2),((1,6),X_0^3),((0,6),X_0*X_1^2),((0,7),X_0^3),((1,4),X_0*X_1^2),((3,4),X_0^3)]}))

-- Indeed it is Weil.
--
-- What if we feed  π/4 + d0 + d1 to sin?

-- >>> withWeil @Double red (sin ((pi/4) + di 0 + di 1))
-- Just (-2.7755575615628914e-17*X_0^3 - 0.3535533905932738*X_0*X_1^2 - 0.4714045207910317*X_0^2 - 0.7071067811865475*X_0*X_1 - 0.35355339059327373*X_1^2 + 0.7071067811865476*X_0 + 0.7071067811865476*X_1 + 0.7071067811865475)

-- We can also feed symbolic types:

-- >>> withWeil red (normalise <$> sin (injCoeWeil x + di 0 + di 1))
-- Just (((-1.0) * (- (sin x)) / 6.0 + (-1.0) * cos x / 6.0)*X_0^3 + ((-1.0) * cos x / 2.0)*X_0*X_1^2 + ((-1.0) * cos x / 6.0 + (- (sin x)) / 2.0)*X_0^2 + (- (sin x))*X_0*X_1 + ((- (sin x)) / 2.0)*X_1^2 + (cos x)*X_0 + (cos x)*X_1 + (sin x))

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
(0.49999999999999994,0.8660254037844387,-0.49999999999999994,-0.8660254037844387)

>>> sin (pi/6 + d0 + d1 + d2) :: Weil (Duals 3) Double
-0.8660254037844387 d(0) d(1) d(2) - 0.49999999999999994 d(0) d(1) - 0.49999999999999994 d(0) d(2) - 0.49999999999999994 d(1) d(2) + 0.8660254037844387 d(0) + 0.8660254037844387 d(1) + 0.8660254037844387 d(2) + 0.49999999999999994

>>> normalise <$> sin (injCoeWeil x + d0 + d1 + d2)
((-1.0) * cos x) d(0) d(1) d(2) + (- (sin x)) d(0) d(1) + (- (sin x)) d(0) d(2) + (- (sin x)) d(1) d(2) + (cos x) d(0) + (cos x) d(1) + (cos x) d(2) + (sin x)
 -}

eps :: (Eq a, Floating a) => Weil (DOrder 4) a
eps = di 0

{-
>>> (sin (pi/6), cos (pi/6), -sin(pi/6)/2, -cos(pi/6)/6)
(0.49999999999999994,0.8660254037844387,-0.24999999999999997,-0.14433756729740646)

>>> normalise <$> sin (injCoeWeil x + eps)
((-1.0) * cos x / 6.0) d(0)^3 + ((- (sin x)) / 2.0) d(0)^2 + (cos x) d(0) + (sin x)
-}

eps1, eps2 :: (Eq x, Floating x) => Weil (DOrder 3 |*| DOrder 2) x
[eps1, eps2] = P.map di [0 ..]

fun :: (Eq x, Floating x) => x -> x -> x
fun x y = exp (2 * x) * sin y

-- >>> fun (2 + eps1) (pi/6 + eps2) :: Weil (DOrder 3 |*| DOrder 2) Double
-- 94.5667698566742 d(0)^2 d(1) + 54.59815003314423 d(0)^2 + 94.5667698566742 d(0) d(1) + 54.59815003314423 d(0) + 47.2833849283371 d(1) + 27.299075016572115

-- >>> normalise <$> fun (injCoeWeil x + eps1) (injCoeWeil y + eps2)
-- (4.0 * exp (2.0 * x) / 2.0 * cos y) d(0)^2 d(1) + (4.0 * exp (2.0 * x) / 2.0 * sin y) d(0)^2 + (2.0 * exp (2.0 * x) * cos y) d(0) d(1) + (2.0 * exp (2.0 * x) * sin y) d(0) + (exp (2.0 * x) * cos y) d(1) + (exp (2.0 * x) * sin y)

{-
>>> diffUpTo 9 atan x
-}

{-
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Numeric.Algebra.Smooth.PowerSeries.SuccinctTower
>>> import Numeric.Algebra.Smooth
>>> normalise <$> cutoff (2 :< 3 :< Nil) (allDerivs (\vec -> sin (SV.head vec) * exp (SV.last vec * SV.head vec)) (x :< y :< Nil))
fromList [([0,0],sin x * exp (y * x)),([0,1],sin x * x * exp (y * x)),([0,2],sin x * x * x * exp (y * x)),([0,3],sin x * x * x * x * exp (y * x)),([1,0],sin x * y * exp (y * x) + cos x * exp (y * x)),([1,1],sin x * (y * x * exp (y * x) + exp (y * x)) + cos x * x * exp (y * x)),([1,2],sin x * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + cos x * x * x * exp (y * x)),([1,3],sin x * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + cos x * x * x * x * exp (y * x)),([2,0],sin x * y * y * exp (y * x) + cos x * y * exp (y * x) + cos x * y * exp (y * x) + (- (sin x)) * exp (y * x)),([2,1],sin x * (y * (y * x * exp (y * x) + exp (y * x)) + y * exp (y * x)) + cos x * (y * x * exp (y * x) + exp (y * x)) + cos x * (y * x * exp (y * x) + exp (y * x)) + (- (sin x)) * x * exp (y * x)),([2,2],sin x * (y * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + y * x * exp (y * x) + exp (y * x) + y * x * exp (y * x) + exp (y * x)) + cos x * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + cos x * (y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + (- (sin x)) * x * x * exp (y * x)),([2,3],sin x * (y * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x) + y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x) + y * x * x * exp (y * x) + x * exp (y * x) + x * exp (y * x)) + cos x * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + cos x * (y * x * x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x) + x * x * exp (y * x)) + (- (sin x)) * x * x * x * exp (y * x))]
 -}
