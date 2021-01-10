{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Numeric.Algebra.Smooth.DualSpec where

import Data.Proxy
import Data.Sized.Builtin (pattern NilR, pattern (:<))
import qualified Data.Sized.Builtin as SV
import GHC.TypeNats
import qualified Numeric.AD as AD
import Numeric.Algebra.Smooth.Classes
import Numeric.Algebra.Smooth.Dual
import Numeric.Algebra.Smooth.Types
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck
import Utils

prop_liftSmooth_coincides_with_liftDual_on_sin :: Property
prop_liftSmooth_coincides_with_liftDual_on_sin =
  forAll arbitrary $ \d ->
    liftSmooth @(Dual Double) (sin . SV.head) (SV.singleton d)
      ==~ liftDual (sin . SV.head) (SV.singleton d)

prop_liftSmotoh_coincides_with_liftDual_on_complexBin :: Property
prop_liftSmotoh_coincides_with_liftDual_on_complexBin =
  forAll (arbitrary @(Vec 2 (Dual Double))) $ \args ->
    let f :: Floating x => Vec 2 x -> x
        f (x :< y :< NilR) = log (1 + y ^ 2) * sin (x ^ 2 + y * x)
     in liftSmooth @(Dual Double) f args
          ==~ liftDual f args

prop_liftSmooth_coincides_with_liftDual_on_complex :: Property
prop_liftSmooth_coincides_with_liftDual_on_complex =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (arbitrary @(TotalExpr n)) $ \(TotalExpr expr) ->
      forAll (arbitrary @(Vec n (Dual Double))) $ \ds ->
        let f :: Floating x => Vec n x -> x
            f = evalExpr expr
            dualAns = liftSmooth @(Dual Double) f ds
            smoothAns = liftDual f ds
         in dualAns ==~ smoothAns

prop_Dual_behaves_similarly_to_Forward_in_ad_package :: Property
prop_Dual_behaves_similarly_to_Forward_in_ad_package =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (arbitrary @(TotalExpr n)) $ \(TotalExpr expr) ->
      forAll (arbitrary @(Vec n (Dual Double))) $ \ds ->
        let f :: Floating x => Vec n x -> x
            f = evalExpr expr
            dualAns = liftSmooth @(Dual Double) f $ deKonst <$> ds
            smoothAns =
              uncurry Dual $ AD.du' f (dualToTup <$> ds)
         in dualAns ==~ smoothAns

test_multDiff :: TestTree
test_multDiff =
  testGroup
    "multDiff behaves similarly as ad package"
    [ testProperty "atan (0.8 * (y ^ 2 * cos x))" $ \a b ->
        let f :: Floating x => x -> x -> x
            f x y = atan (0.8 * (y ^ 2 * cos x))
         in SV.head
              ( multDiff
                  (3 :< 4 :< NilR)
                  (SV.singleton . (\(x SV.:< y SV.:< SV.NilR) -> f x y))
                  (a :< b :< NilR :: Vec 2 Double)
              )
              ==~ AD.diffs
                ( \y ->
                    AD.diffs
                      (\x -> f x (AD.auto y))
                      (AD.auto a)
                      !? 3
                )
                b
                !? 4
    , testProperty "n = 2" chkMultDiff
    ]

chkMultDiff :: Property
chkMultDiff =
  forAll (arbitrary @(TotalExpr 2)) $ \(TotalExpr expr) ->
    forAll (resize 4 $ arbitrary @(UVec 2 Word)) $ \degs dbls ->
      SV.head
        ( multDiff
            degs
            (SV.singleton . evalExpr expr)
            (dbls :: Vec 2 Double)
        )
        ==~ AD.diffs
          ( \y ->
              AD.diffs
                (\x -> evalExpr expr (x SV.:< AD.auto y SV.:< SV.NilR :: Vec 2 _))
                (AD.auto $ dbls SV.%!! 0)
                !? SV.head degs
          )
          (dbls SV.%!! 1)
          !? SV.last degs

deKonst :: Num a => Dual a -> Dual a
deKonst (Konst a) = Dual a 0
deKonst d = d

-- Counter examples for multDiff

errdegs :: UVec 2 Word
errdegs = 3 SV.:< 4 SV.:< SV.NilR

errInps :: Vec 2 Double
errInps = 3 SV.:< 18 SV.:< SV.NilR

theExpr :: Expr 2
theExpr =
  Atan (K 0.8 :* (Arg 1 :^ 2 :* Cos (Arg 0)))

interped :: Floating x => x -> x -> x
interped x y =
  atan (0.8 * (y ^ 2 * cos x))

thef :: Floating x => Vec 2 x -> x
thef = evalExpr theExpr

thef' :: Floating x => x -> x -> x
thef' x y = thef (x SV.:< y SV.:< SV.NilR)

{-
>>> import Numeric.AD
>>> diffs (\y -> diffs (\x -> interped x (auto y)) 3 !! 3) 18 !! 4
-3.2497003091202094e-6

prop> chkWeilProduct (sing @4) (sing @5) (TotalExpr theExpr) 3 18
*** Failed! Falsified (after 1 test):
Partial Derivative: [3,4]
-3.2497003091202306e-6 ~/= 3.6043377824171983e-3

>>> multDiff (3 SV.:< 4 SV.:< SV.NilR) (SV.singleton . thef) errInps
[3.6043377824171983e-3]

-}