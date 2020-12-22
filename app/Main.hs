{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Algebra.Prelude.Core as AP hiding ((*), (+), (-), (/), (^))
import Algebra.Ring.Polynomial.Class (PrettyCoeff)
import Algebra.Ring.Polynomial.Univariate
import AlgebraicPrelude (WrapNum (..))
import Data.Sized.Builtin hiding (fmap)
import Numeric.Algebra.Smooth
import Numeric.Algebra.Smooth.Weil
import Symbolic
import Prelude ((*), (+), (-), (/), (^))

-- * 高階微分の例

-- f = exp x * sin x の4階までの微分係数を求めてみる。

f, f', f'2, f'3, f'4 :: (Floating x) => x -> x
f x = exp x * sin x
f' x = exp x * sin x + exp x * cos x
f'2 x = 2 * exp x * cos x
f'3 x = 2 * (exp x * cos x - exp x * sin x)
f'4 x = -4 * f x

-- まず pi/6 までの微分係数を計算しておく
-- >>> AP.map ($ pi/6) [f, f', f'2, f'3, f'4]
-- [0.8440458974822341,2.305976275841536,2.9238607567186037,1.2357689617541354,-3.3761835899289365]

-- >>> f (pi/6 + dn @0 + dn @1 + dn @2 + dn @3) :: Duals 4 Double
-- 0.8440458974822341 + 2.305976275841536 d(0) + 2.9238607567186037 d(0)d(1) + 1.2357689617541352 d(0)d(1)d(2) + (-3.376183589928937) d(0)d(1)d(2)d(3) + 1.2357689617541352 d(0)d(1)d(3) + 2.9238607567186037 d(0)d(2) + 1.2357689617541352 d(0)d(2)d(3) + 2.9238607567186037 d(0)d(3) + 2.305976275841536 d(1) + 2.9238607567186037 d(1)d(2) + 1.2357689617541352 d(1)d(2)d(3) + 2.9238607567186037 d(1)d(3) + 2.305976275841536 d(2) + 2.9238607567186037 d(2)d(3) + 2.305976275841536 d(3)

-- 上のD(2)^n を使って計算する関数が次：
-- >>> diffUpTo 4 f $ pi/6
-- fromList [(0,0.8440458974822341),(1,2.305976275841536),(2,2.9238607567186037),(3,1.2357689617541352),(4,-3.376183589928937)]

-- 記号微分を入れてみる
-- >>> normalise <$> diffUpTo 4 f x
-- fromList [(0,exp x * sin x),(1,exp x * cos x + exp x * sin x),(2,exp x * (- (sin x)) + exp x * cos x + exp x * cos x + exp x * sin x),(3,exp x * (- (cos x)) + exp x * (- (sin x)) + exp x * (- (sin x)) + exp x * cos x + exp x * (- (sin x)) + exp x * cos x + exp x * cos x + exp x * sin x),(4,exp x * sin x + exp x * (- (cos x)) + exp x * (- (cos x)) + exp x * (- (sin x)) + exp x * (- (cos x)) + exp x * (- (sin x)) + exp x * (- (sin x)) + exp x * cos x + exp x * (- (cos x)) + exp x * (- (sin x)) + exp x * (- (sin x)) + exp x * cos x + exp x * (- (sin x)) + exp x * cos x + exp x * cos x + exp x * sin x)]

-- * 一般の Weil代数

-- 試しに R[e] = R[X]/(X^4) の剰余環計算に必要な情報を集めてみる

idealX4 :: Ideal (Polynomial AP.Rational 1)
idealX4 = toIdeal [var 0 ^ 4]

-- >>> isWeil idealX4
-- Just (SomeWeil (WeilSettings {weilBasis = [[0],[1],[2],[3]], monomUpperBound = [3], weilMonomDic = fromList [([0],[1,0,0,0]),([1],[0,1,0,0]),([2],[0,0,1,0]),([3],[0,0,0,1])], table = fromList [((0,0),1),((0,1),X_0),((1,2),X_0^3),((0,2),X_0^2),((1,1),X_0^2),((0,3),X_0^3)]}))

-- 若干見づらいが、基底は e^0 (=1), e^1, e^2, e^3 で最大次数は (3),
-- そして乗算表が手に入っている（今回の場合は自明だけど……）

-- これを使って、3階微分までの値が計算出来るかを見てみよう。

ε :: (Eq a, Floating a) => Weil (DOrder 4) a
ε = di 0

-- >>> normalise <$> cos (injCoeWeil x + ε)
-- (sin x / 6.0) d(0)^3 + ((- (cos x)) / 2.0) d(0)^2 + (- (sin x)) d(0) + (cos x)

-- 確かに 3 階微分の値まで計算出来ている！

-- 今度は多変数関数の偏導関数を一挙に求めてみよう
-- x について2階、yについて1階まで求めてみる。

-- それには、R[X]/(X^3) ⨂ R[Y]/(Y^2) の冪零構造を使えばよい。

δ1 :: (Eq a, Floating a) => Weil (DOrder 3 |*| DOrder 2) a
δ1 = di 0

δ2 :: (Eq a, Floating a) => Weil (DOrder 3 |*| DOrder 2) a
δ2 = di 1

-- >>> import Data.Reflection
-- >>> reflect $ Proxy @(DOrder 4 |*| DOrder 3)
-- WeilSettings {weilBasis = [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2],[2,0],[2,1],[2,2],[3,0],[3,1],[3,2]], monomUpperBound = [3,2], weilMonomDic = fromList [([0,2],[0,0,1,0,0,0,0,0,0,0,0,0]),([1,1],[0,0,0,0,1,0,0,0,0,0,0,0]),([2,1],[0,0,0,0,0,0,0,1,0,0,0,0]),([3,0],[0,0,0,0,0,0,0,0,0,1,0,0]),([3,1],[0,0,0,0,0,0,0,0,0,0,1,0]),([1,0],[0,0,0,1,0,0,0,0,0,0,0,0]),([2,2],[0,0,0,0,0,0,0,0,1,0,0,0]),([2,0],[0,0,0,0,0,0,1,0,0,0,0,0]),([1,2],[0,0,0,0,0,1,0,0,0,0,0,0]),([0,1],[0,1,0,0,0,0,0,0,0,0,0,0]),([0,0],[1,0,0,0,0,0,0,0,0,0,0,0]),([3,2],[0,0,0,0,0,0,0,0,0,0,0,1])], table = fromList [((0,0),1),((2,6),X_0^2*X_1^2),((1,3),X_0*X_1),((0,1),X_1),((3,8),X_0^3*X_1^2),((0,2),X_1^2),((1,1),X_1^2),((0,3),X_0),((0,4),X_0*X_1),((1,7),X_0^2*X_1^2),((0,5),X_0*X_1^2),((2,3),X_0*X_1^2),((1,6),X_0^2*X_1),((0,6),X_0^2),((0,7),X_0^2*X_1),((1,4),X_0*X_1^2),((0,8),X_0^2*X_1^2),((4,4),X_0^2*X_1^2),((0,9),X_0^3),((1,10),X_0^3*X_1^2),((5,6),X_0^3*X_1^2),((0,10),X_0^3*X_1),((4,6),X_0^3*X_1),((1,9),X_0^3*X_1),((3,3),X_0^2),((0,11),X_0^3*X_1^2),((4,7),X_0^3*X_1^2),((3,5),X_0^2*X_1^2),((3,4),X_0^2*X_1),((3,7),X_0^3*X_1),((2,9),X_0^3*X_1^2),((3,6),X_0^3)]}

f2 :: Floating r => r -> r -> r
f2 x y = sin x * cos y

-- >>> f2 x y
-- sin x * cos y

-- >>> normalise <$> f2 (injCoeWeil x + δ1) (injCoeWeil y + δ2)
-- ((- (sin x)) / 2.0 * (- (sin y))) d(0)^2 d(1) + ((- (sin x)) / 2.0 * cos y) d(0)^2 + (cos x * (- (sin y))) d(0) d(1) + (cos x * cos y) d(0) + (sin x * (- (sin y))) d(1) + (sin x * cos y)

-- ** 反例のチェック

-- 有限次元代数だが、Weil 代数でない例を弾けるか見てみよう。
-- R[X]/(X^3 - 1) はどうだろうか。

-- >>> isWeil (toIdeal [var 0 ^3 - 1 :: Polynomial _ 1])
-- Nothing

-- 冪零ではないので、ちゃんと弾かれている。

-- 意味はパッとわからないが、ちゃんと Weil代数になる筈のやつを見てみよう。
-- R[e,d] = R[x, y]/(x^2 - y, y^2)

red :: Ideal (Polynomial AP.Rational 2)
red = toIdeal [x ^ 2 - y, y ^ 2]
  where
    [x, y] = vars

-- >>> isWeil red
-- Just (SomeWeil (WeilSettings {weilBasis = [[0,0],[0,1],[1,0],[1,1]], monomUpperBound = [1,1], weilMonomDic = fromList [([1,1],[0,0,0,1]),([1,0],[0,0,1,0]),([0,1],[0,1,0,0]),([0,0],[1,0,0,0])], table = fromList [((0,0),1),((0,1),X_1),((1,2),X_0*X_1),((0,2),X_0),((0,3),X_0*X_1),((2,2),X_1)]}))

-- Weil 環であることがわかった。では、この上で関数を計算させてみよう。
--
-- 上の f(x) = e^x sin x に π/4 + (全部の非自明な基底)喰わせるとどうなるか？

-- >>> reifyWeil red (\(Proxy :: Proxy s) -> show $ f ((pi/4) + AP.sum basisWeil :: Weil s Double) )
-- Just "2.01624925078897 d(0) d(1) + 4.555545505661757 d(0) + 3.285897378225364 d(1) + 5.82519363309815"

-- 記号を入れてみよう。f (x + d(0)) ？

-- >>> reifyWeil red (\(Proxy :: Proxy s) -> show $ normalise <$> f (x .* 1 + di 0 :: Weil s Symbolic) )
-- Just "(exp x * cos x + exp x * sin x) d(0) + (exp x * cos x) d(1) + (exp x * sin x)"

-- >>> normalise <$> f (injCoeWeil x + di 0) :: Weil (DOrder 4) Symbolic
-- (exp x * ((- (cos x)) / 6.0) + exp x * ((- (sin x)) / 2.0) + exp x / 2.0 * cos x + exp x / 6.0 * sin x) d(0)^3 + (exp x * ((- (sin x)) / 2.0) + exp x * cos x + exp x / 2.0 * sin x) d(0)^2 + (exp x * cos x + exp x * sin x) d(0) + (exp x * sin x)

main :: IO ()
main = return ()
