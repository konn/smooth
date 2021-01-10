{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main where

import Algebra.Prelude.Core (Polynomial, SingI (sing), ordToNatural, toIdeal, var)
import qualified AlgebraicPrelude as AP
import Control.DeepSeq (force)
import Data.Foldable (forM_, sequenceA_)
import Data.Proxy (Proxy)
import Data.Reflection (Reifies)
import qualified Data.Sized as SV
import qualified Data.Vector as V
import GHC.TypeNats (KnownNat)
import Numeric.Algebra.Smooth.Weil
  ( DOrder,
    Weil (Weil),
    WeilSettings,
    liftSmoothAD,
    liftSmoothSeriesAD,
    reifyWeil,
    type (|*|),
  )
import Weigh (Weigh, func, mainWith, wgroup)

main :: IO ()
main = mainWith theBench

theBench :: Weigh ()
theBench = do
  benchFor @(DOrder 2) "DOrder 2"
  benchFor @(DOrder 3) "DOrder 3"
  benchFor @(DOrder 4) "DOrder 4"
  benchFor @(DOrder 3 |*| DOrder 4) "DOrder 3 |*| DOrder 4"
  sequenceA_ $
    reifyWeil
      (toIdeal [var 0 ^ 3 - var 1 ^ 2, var 1 ^ 3 :: Polynomial AP.Rational 2])
      $ \(_ :: Proxy w) ->
        benchFor @w "R[x,y]/(x^3 - y^2, y^3)"

benchFor ::
  forall w n m.
  (Reifies w (WeilSettings n m), KnownNat n, KnownNat m) =>
  String ->
  Weigh ()
benchFor title = wgroup title $
  forM_ inputs $ \(lab, inp0) -> do
    let !inp = force $ SV.singleton (Weil @w inp0)
    wgroup lab $ do
      wgroup "identity" $ do
        func "liftSmoothAD" (liftSmoothAD SV.head) inp
        func "liftSmoothSerisAD" (liftSmoothSeriesAD SV.head) inp
      wgroup "exp x" $ do
        func "liftSmoothAD" (liftSmoothAD (exp . SV.head)) inp
        func "liftSmoothSerisAD" (liftSmoothSeriesAD (exp . SV.head)) inp
      let f :: forall x. Floating x => x -> x
          f = \x -> sin x * exp (x ^ 2 + x)
      wgroup "sin x * exp (x^2 + x)" $ do
        func "liftSmoothAD" (liftSmoothAD (f . SV.head)) inp
        func "liftSmoothSerisAD" (liftSmoothSeriesAD (f . SV.head)) inp

      let !inp3 = force $ SV.replicate' $ SV.head inp
          g :: forall x. Floating x => SV.Sized V.Vector 3 x -> x
          g = \(x SV.:< y SV.:< z SV.:< SV.NilR) -> sin x * exp (y ^ 2 + z)
      wgroup "sin x * exp (y^2 + z)" $ do
        func "liftSmoothAD" (liftSmoothAD g) inp3
        func "liftSmoothSerisAD" (liftSmoothSeriesAD g) inp3
  where
    inputs :: [(String, SV.Sized V.Vector n Double)]
    inputs =
      [ ("sparse", SV.generate sing $ \o -> if o == 0 then 1 else 0.0)
      , ("x + d", SV.generate sing $ \o -> if o == 0 || o == 1 then 1 else 0.0)
      , ("dense", SV.generate sing $ \o -> fromIntegral (ordToNatural o) + 1)
      ]
