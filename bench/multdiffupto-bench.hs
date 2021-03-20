{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main where

import Data.Sized.Builtin (pattern Nil, pattern (:<))
import qualified Data.Sized.Builtin as SV
import Gauge
import qualified Numeric.AD as AD
import Numeric.Algebra.Smooth.PowerSeries (walkAlong)
import Numeric.Algebra.Smooth.PowerSeries.SuccinctTower (allDerivs, cutoff)
import Numeric.Algebra.Smooth.Types (Vec)

main :: IO ()
main =
  defaultMain
    [ bgroup
        "exp x"
        [ bgroup
          (show n)
          [ bench "AD" $ nf (walkAlong (SV.singleton n) . AD.grads (exp . SV.head)) (SV.singleton (0.0 :: Double))
          , bench "STower" $ nf (cutoff (SV.singleton $ fromIntegral n) . allDerivs (exp . SV.head)) (SV.singleton (0.0 :: Double))
          ]
        | n <- [0 .. 10]
        ]
    , bgroup
        "sin x * exp y^2"
        [ let f :: Floating x => Vec 2 x -> x
              f (x :< y :< Nil) = sin x * exp (y ^ 2)
           in bgroup
                (show degs)
                [ bench "AD" $ nf (walkAlong degs . AD.grads f) (SV.replicate' (0.0 :: Double))
                , bench "STower" $ nf (cutoff degs . allDerivs f) (SV.replicate' (0.0 :: Double))
                ]
        | degs <-
            [ 0 :< 1 :< Nil
            , 2 :< 0 :< Nil
            , 2 :< 1 :< Nil
            , 2 :< 2 :< Nil
            , 3 :< 4 :< Nil
            ]
        ]
    , bgroup
        "sin x * exp (y^2 + z)"
        [ let f :: Floating x => Vec 3 x -> x
              f (x :< y :< z :< Nil) = sin x * exp (y ^ 2 + z)
           in bgroup
                (show degs)
                [ bench "AD" $ nf (walkAlong degs . AD.grads f) (SV.replicate' (0.0 :: Double))
                , bench "STower" $ nf (cutoff degs . allDerivs f) (SV.replicate' (0.0 :: Double))
                ]
        | degs <-
            [ 0 :< 1 :< 2 :< Nil
            , 2 :< 0 :< 1 :< Nil
            , 2 :< 1 :< 0 :< Nil
            , 2 :< 2 :< 2 :< Nil
            , 3 :< 4 :< 5 :< Nil
            ]
        ]
    ]
