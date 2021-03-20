{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main where

import Data.Foldable (forM_)
import qualified Data.Sized as SV
import Data.Sized.Builtin (pattern Nil, pattern (:<))
import qualified Numeric.AD as AD
import Numeric.Algebra.Smooth.PowerSeries (walkAlong)
import Numeric.Algebra.Smooth.PowerSeries.SuccinctTower (allDerivs, cutoff)
import Numeric.Algebra.Smooth.Types (Vec)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import Weigh (Weigh, func, reportGroup, weighResults, wgroup)

resultDir :: FilePath
resultDir = "bench-results"

benchName :: FilePath
benchName = "multDiffUpTo-heap.txt"

main :: IO ()
main = do
  (results, config) <- weighResults theBench
  let fmt = reportGroup config "multDiffUpTo Heap Profile" results
  createDirectoryIfMissing True resultDir
  writeFile (resultDir </> benchName) fmt

theBench :: Weigh ()
theBench = do
  wgroup "exp x" $ do
    forM_ [0 .. 10] $ \n ->
      wgroup (show n) $ do
        func "AD" (walkAlong (SV.singleton n) . AD.grads (exp . SV.head)) (SV.singleton (0.0 :: Double))
        func
          "STower"
          (cutoff (SV.singleton $ fromIntegral n) . allDerivs (exp . SV.head))
          (SV.singleton (0.0 :: Double))
  wgroup "sin x * exp y^2" $ do
    let f :: Floating x => Vec 2 x -> x
        f (x :< y :< Nil) = sin x * exp (y ^ 2)
    forM_
      [ 0 :< 1 :< Nil
      , 2 :< 0 :< Nil
      , 2 :< 1 :< Nil
      , 2 :< 2 :< Nil
      , 3 :< 4 :< Nil
      ]
      $ \degs -> do
        wgroup (show degs) $ do
          func "AD" (walkAlong degs . AD.grads f) (SV.replicate' (0.0 :: Double))
          func "STower" (cutoff degs . allDerivs f) (SV.replicate' (0.0 :: Double))
  wgroup "sin x * exp (y^2 + z)" $ do
    let f :: Floating x => Vec 3 x -> x
        f (x :< y :< z :< Nil) = sin x * exp (y ^ 2 + z)
    forM_
      [ 0 :< 1 :< 2 :< Nil
      , 2 :< 0 :< 1 :< Nil
      , 2 :< 1 :< 0 :< Nil
      , 2 :< 2 :< 2 :< Nil
      , 3 :< 4 :< 5 :< Nil
      ]
      $ \degs -> wgroup (show degs) $ do
        func "AD" (walkAlong degs . AD.grads f) (SV.replicate' (0.0 :: Double))
        func "STower" (cutoff degs . allDerivs f) (SV.replicate' (0.0 :: Double))
