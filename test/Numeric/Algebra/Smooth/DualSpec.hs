{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Numeric.Algebra.Smooth.DualSpec where

import Algebra.Internal (SingI (sing))
import Data.Coerce (coerce)
import qualified Data.Foldable as F
import qualified Data.Map as Map
import Data.Proxy
import Data.Semialign.Indexed
import Data.Sized (pattern Nil, pattern (:<))
import qualified Data.Sized as SV
import Data.These
import qualified Data.Vector as V
import GHC.TypeNats
import qualified Numeric.AD as AD
import Numeric.Algebra.Smooth.Classes
import Numeric.Algebra.Smooth.Dual
import Numeric.Algebra.Smooth.Types
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck
import Utils

prop_liftSmooth_coincides_with_sin :: Property
prop_liftSmooth_coincides_with_sin =
  forAll arbitrary $ \d ->
    liftSmooth @(Dual Double) (sin . SV.head) (SV.singleton d)
      ==~ sin d

prop_liftSmooth_coincides_with_pow :: NonZero Double -> Double -> Dual Double -> Property
prop_liftSmooth_coincides_with_pow (NonZero x) dx e =
  let d = Dual x dx
   in liftSmooth @(Dual Double) ((**) <$> SV.head <*> SV.last) (SV.unsafeFromList (sing @2) [d, e])
        ==~ d ** e

prop_liftSmooth_coincides_with_atan :: Property
prop_liftSmooth_coincides_with_atan =
  forAll arbitrary $ \d ->
    liftSmooth @(Dual Double) (atan . SV.head) (SV.singleton d)
      ==~ atan d

prop_liftSmooth_coincides_with_liftDual_on_recip :: Property
prop_liftSmooth_coincides_with_liftDual_on_recip =
  forAll arbitrary $ \(NonZero d) ->
    liftSmooth @(Dual Double) (recip . SV.head) (SV.singleton d)
      ==~ recip d

prop_liftSmotoh_coincides_with_complexBin :: Property
prop_liftSmotoh_coincides_with_complexBin =
  forAll (arbitrary @(Vec 2 (Dual Double))) $ \args ->
    let f :: Floating x => Vec 2 x -> x
        f (x :< y :< Nil) = log (1 + y ^ 2) * sin (x ^ 2 + y * x)
        f _ = error "Could not happen!"
     in liftSmooth @(Dual Double) f args
          ==~ f args

prop_liftSmooth_coincides_with_complex :: Property
prop_liftSmooth_coincides_with_complex =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (arbitrary @(TotalExpr n)) $ \(TotalExpr expr) ->
      forAll (arbitrary @(Vec n (Dual Double))) $ \ds ->
        let f :: Floating x => Vec n x -> x
            f = evalExpr expr
            dualAns = liftSmooth @(Dual Double) f ds
            smoothAns = f ds
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

deKonst :: Num a => Dual a -> Dual a
deKonst d = d
