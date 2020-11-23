{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, GADTs         #-}
{-# LANGUAGE MonoLocalBinds, MultiParamTypeClasses, OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures, PolyKinds, ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving, TypeApplications, TypeOperators     #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where
import Algebra.Prelude.Core               as AP hiding ((*), (+), (-), (/), (^))
import Algebra.Ring.Polynomial.Class      (PrettyCoeff)
import Algebra.Ring.Polynomial.Univariate
import AlgebraicPrelude                   (WrapNum (..))
import Data.Sized.Builtin                 hiding (fmap)
import Numeric.Algebra.Smooth
import Numeric.Algebra.Smooth.Weil
import Prelude                            ((*), (+), (-), (/), (^))
import Symbolic

-- * 高階微分の例

f, f', f'2, f'3, f'4 :: (Floating x) => x -> x
f x = exp x * sin x
f'  x = exp x * sin x + exp x * cos x
f'2 x = 2 * exp x * cos x
f'3 x = 2 * (exp x * cos x - exp x * sin x)
f'4 x = -4 * f x

-- >>> f (pi/6 + dn @0 + dn @1 + dn @2 + dn @3) :: Duals 4 Double

-- >>> (f $ pi/6, f' $ pi/6, f'2 $ pi/6, f'3 $ pi/6, f'4 $ pi/6)

-- >>> diffUpTo 4 f $ pi/6

-- >>> normalise <$> diffUpTo 4 f x

-- 試しに三階微分まで見てみよう。

-- >>> fmap normalise $ f $ fromCoeff x + dn @0 + dn @1 + dn @2 :: Duals 3 Symbolic

-- * 一般の Weil代数

-- 試しに R[e] = R[X]/(X^3) の剰余環計算に必要な情報を集めてみる

-- >>> isWeil (toIdeal [var 0 ^ 3 :: Polynomial _ 1])

-- 若干見づらいが、基底は e^0 (=1), e^1, e^2 で最大次数は (2),
-- そして乗算表が手に入っている（今回の場合は自明だけど……）

-- 有限次元代数だが、Weil 代数でない例を弾けるか見てみよう。
-- R[X]/(X^3 - 1) はどうだろうか。

-- >>> isWeil (toIdeal [var 0 ^3 - 1 :: Polynomial _ 1])

-- 冪零ではないので、ちゃんと弾かれている。

-- 意味はパッとわからないが、ちゃんと Weil代数になる筈のやつを見てみよう。
-- R[e,d] = R[x, y]/(x^3 - y^2, y^3)

red :: Ideal (Polynomial AP.Rational 2)
red = toIdeal [x ^3 - y ^2, y ^ 3]
  where [x,y] = vars

-- >>> isWeil red

-- Weil 環であることがわかった。では、この上で関数を計算させてみよう。
--
-- 上の f(x) = e^x sin x に π/4 + (全部の非自明な基底)喰わせるとどうなるか？

-- >>> reifyWeil red (\(Proxy :: Proxy s) -> show $ f ((pi/4) + AP.sum basisWeil :: Weil s Double) )

-- 記号を入れてみよう。f (x + d(0)) ？

-- >>> reifyWeil red (\(Proxy :: Proxy s) -> show $ normalise <$> f (x .* 1 + di 0 :: Weil s Symbolic) )

-- >>> normalise <$> f (injCoeWeil x + di 0) :: Weil (DOrder 4) Symbolic
-- (exp x * ((- (cos x)) / 6.0) + exp x * ((- (sin x)) / 2.0) + exp x / 2.0 * cos x + exp x / 6.0 * sin x) d(0)^3 + (exp x * ((- (sin x)) / 2.0) + exp x * cos x + exp x / 2.0 * sin x) d(0)^2 + (exp x * cos x + exp x * sin x) d(0) + (exp x * sin x)

main :: IO ()
main = return ()
