{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Numeric.Algebra.Smooth.PowerSeries.SuccinctTowerSpec where

import qualified Data.Foldable as F
import Data.Proxy
import Data.Semialign.Indexed
import Data.Sized (pattern Nil, pattern (:<))
import qualified Data.Sized as SV
import Data.These
import GHC.TypeNats
import Numeric.Algebra.Smooth.PowerSeries.SuccinctTower
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty)
import Utils

test_liftNAry :: TestTree
test_liftNAry =
  testGroup
    "liftNAry"
    [ testProperty "coincides on * (upto (3,...,3) th)" $
        \(SomeNat (_ :: Proxy n)) -> property $
          \(a :: SSeries n Double) b ->
            let expected = cutoff (SV.replicate' 3) (a * b)
                answer =
                  cutoff
                    (SV.replicate' 3)
                    $ liftNAry @Floating
                      (\(x :< y :< Nil) -> x * y)
                      ( SmoothFun
                          ( \(_ :< y :< Nil) ->
                              y
                          )
                          :< SmoothFun
                            ( \(x :< _ :< Nil) -> x
                            )
                          :< Nil
                      )
                      (a :< b :< Nil)
             in conjoin $
                  F.toList $
                    ialignWith
                      ( \i th -> counterexample (show i ++ "th") $ case th of
                          These x y -> x ==~ y
                          This x -> x ==~ 0
                          That y -> 0 ==~ y
                      )
                      expected
                      answer
    , testProperty "coincides on + (upto (3,...,3) th)" $
        \(SomeNat (_ :: Proxy n)) -> property $
          \(a :: SSeries n Double) b ->
            let expected = cutoff (SV.replicate' 3) (a + b)
                answer =
                  cutoff
                    (SV.replicate' 3)
                    $ liftNAry @Floating
                      (\(x :< y :< Nil) -> x + y)
                      ( SmoothFun
                          (const 1)
                          :< SmoothFun
                            (const 1)
                          :< Nil
                      )
                      (a :< b :< Nil)
             in conjoin $
                  F.toList $
                    ialignWith
                      ( \i th -> counterexample (show i ++ "th") $ case th of
                          These x y -> x ==~ y
                          This x -> x ==~ 0
                          That y -> 0 ==~ y
                      )
                      expected
                      answer
    , testProperty "coincides on x*exp y (upto (3,...,3) th)" $
        \(SomeNat (_ :: Proxy n)) -> property $
          \(a :: SSeries n Double) b ->
            let expected = cutoff (SV.replicate' 3) (a * exp b)
                answer =
                  cutoff
                    (SV.replicate' 3)
                    $ liftNAry @Floating
                      (\(x :< y :< Nil) -> x * exp y)
                      ( SmoothFun
                          (\(_ :< y :< Nil) -> exp y)
                          :< SmoothFun
                            (\(x :< y :< Nil) -> x * exp y)
                          :< Nil
                      )
                      (a :< b :< Nil)
             in conjoin $
                  F.toList $
                    ialignWith
                      ( \i th -> counterexample (show i ++ "th") $ case th of
                          These x y -> x ==~ y
                          This x -> x ==~ 0
                          That y -> 0 ==~ y
                      )
                      expected
                      answer
    ]
