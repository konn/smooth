module Main where

import Gauge
import qualified Numeric.Algebra.Smooth.Dual as Duals
import qualified Numeric.Algebra.Smooth.Weil as Dn

main :: IO ()
main =
  defaultMain
    [ bgroup
        "identity"
        [ bgroup
          (show n)
          [ bench "Duals" $ nf (Duals.diffUpTo n id) (0.0 :: Double)
          , bench "Dn" $ nf (Dn.diffUpTo' n id) (0.0 :: Double)
          ]
        | n <- [0 .. 10]
        ]
    , bgroup
        "exp x"
        [ bgroup
          (show n)
          [ bench "Duals" $ nf (Duals.diffUpTo n exp) (0.0 :: Double)
          , bench "Dn" $ nf (Dn.diffUpTo' n exp) (0.0 :: Double)
          ]
        | n <- [0 .. 10]
        ]
    , bgroup
        "sin x * exp (x^2 + x)"
        [ bgroup
          (show n)
          [ bench "Duals" $ nf (Duals.diffUpTo n (\x -> sin x * exp (x ^ 2 + x))) (0.0 :: Double)
          , bench "Dn" $ nf (Dn.diffUpTo' n (\x -> sin x * exp (x ^ 2 + x))) (0.0 :: Double)
          ]
        | n <- [0 .. 10]
        ]
    ]
