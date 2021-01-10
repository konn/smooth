{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main where

import Algebra.Prelude.Core (Polynomial, SingI (sing), ordToNatural, toIdeal, var)
import qualified AlgebraicPrelude as AP
import Control.Exception (evaluate)
import Data.Maybe (fromJust)
import Data.Proxy
import Data.Reflection
import qualified Data.Sized as SV
import qualified Data.Vector as V
import GHC.TypeNats (KnownNat)
import Gauge
import Numeric.Algebra.Smooth.Weil

main :: IO ()
main =
  defaultMain
    [ benchFor @(DOrder 2) "DOrder 2"
    , benchFor @(DOrder 3) "DOrder 3"
    , benchFor @(DOrder 4) "DOrder 4"
    , benchFor @(DOrder 3 |*| DOrder 4) "DOrder 3 |*| DOrder 4"
    , fromJust $
        reifyWeil
          (toIdeal [var 0 ^ 3 - var 1 ^ 2, var 1 ^ 3 :: Polynomial AP.Rational 2])
          $ \(_ :: Proxy w) ->
            benchFor @w "R[x,y]/(x^3 - y^2, y^3)"
    ]

benchFor ::
  forall w n m.
  (Reifies w (WeilSettings n m), KnownNat n, KnownNat m) =>
  String ->
  Benchmark
benchFor title =
  bgroup
    title
    [ env (evaluate $ SV.singleton (Weil @w input)) $ \inp ->
      bgroup
        lab
        [ bgroup
            "identity"
            [ bench "liftSmoothAD" $ nf (liftSmoothAD SV.head) inp
            , bench "liftSmoothSerisAD" $ nf (liftSmoothSeriesAD SV.head) inp
            ]
        , bgroup
            "exp x"
            [ bench "liftSmoothAD" $ nf (liftSmoothAD (exp . SV.head)) inp
            , bench "liftSmoothSerisAD" $ nf (liftSmoothSeriesAD (exp . SV.head)) inp
            ]
        , let f :: forall x. Floating x => x -> x
              f = \x -> sin x * exp (x ^ 2 + x)
           in bgroup
                "sin x * exp (x^2 + x)"
                [ bench "liftSmoothAD" $ nf (liftSmoothAD (f . SV.head)) inp
                , bench "liftSmoothSerisAD" $ nf (liftSmoothSeriesAD (f . SV.head)) inp
                ]
        , env (evaluate $ SV.replicate' $ SV.head inp) $ \inp3 ->
            let f :: forall x. Floating x => SV.Sized V.Vector 3 x -> x
                f = \(x SV.:< y SV.:< z SV.:< SV.NilR) -> sin x * exp (y ^ 2 + z)
             in bgroup
                  "sin x * exp (y^2 + z)"
                  [ bench "liftSmoothAD" $
                      nf
                        (liftSmoothAD f)
                        inp3
                  , bench "liftSmoothSerisAD" $
                      nf
                        (liftSmoothSeriesAD f)
                        inp3
                  ]
        ]
    | (lab, input) <-
        [ ("sparse", SV.generate sing $ \o -> if o == 0 then 1 else 0.0 :: Double)
        , ("x + d", SV.generate sing $ \o -> if o == 0 || o == 1 then 1 else 0.0 :: Double)
        , ("dense", SV.generate sing $ \o -> fromIntegral (ordToNatural o) + 1)
        ]
    ]
