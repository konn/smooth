{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main where

import qualified Data.Sized as SV
import Gauge
import qualified Numeric.AD as AD
import Numeric.Algebra.Smooth.PowerSeries.SuccinctTower (allDerivs, cutoff)
import qualified Numeric.Algebra.Smooth.Weil as Dn

main :: IO ()
main =
  defaultMain
    [ bgroup
        "identity"
        [ bgroup
          (show n)
          [ bench "AD" $ nf (take (n + 1) . AD.diffs id) (0.0 :: Double)
          , bench "Dn" $ nf (Dn.diffUpTo (fromIntegral n) id) (0.0 :: Double)
          , bench "STower" $ nf (cutoff (SV.singleton $ fromIntegral n) . allDerivs SV.head) (SV.singleton (0.0 :: Double))
          ]
        | n <- [0 .. 10]
        ]
    , bgroup
        "exp x"
        [ bgroup
          (show n)
          [ bench "AD" $ nf (take (n + 1) . AD.diffs exp) (0.0 :: Double)
          , bench "Dn" $ nf (Dn.diffUpTo (fromIntegral n) exp) (0.0 :: Double)
          , bench "STower" $ nf (cutoff (SV.singleton $ fromIntegral n) . allDerivs (exp . SV.head)) (SV.singleton (0.0 :: Double))
          ]
        | n <- [0 .. 10]
        ]
    , bgroup
        "sin x * exp (x^2 + x)"
        [ let f :: Floating x => x -> x
              f x = sin x * exp (x ^ 2 + x)
           in bgroup
                (show n)
                [ bench "AD" $ nf (take (n + 1) . AD.diffs f) (0.0 :: Double)
                , bench "Dn" $ nf (Dn.diffUpTo (fromIntegral n) f) (0.0 :: Double)
                , bench "STower" $ nf (cutoff (SV.singleton $ fromIntegral n) . allDerivs (f . SV.head)) (SV.singleton (0.0 :: Double))
                ]
        | n <- [0 .. 10]
        ]
    ]
