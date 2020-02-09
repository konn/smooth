{-# LANGUAGE DataKinds, ExplicitNamespaces, PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications          #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
module Numeric.Algebra.Smooth.DualSpec where
import           Data.Proxy
import           Data.Sized.Builtin             (pattern (:<), pattern NilR)
import qualified Data.Sized.Builtin             as SV
import           GHC.TypeNats
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Dual
import           Numeric.Algebra.Smooth.Types
import           Test.QuickCheck
import           Utils

prop_liftSmooth_coincides_with_liftDual_on_sin :: Property
prop_liftSmooth_coincides_with_liftDual_on_sin =
  forAll arbitrary $ \d ->
      liftSmooth @(Dual Double) (sin . SV.head) (SV.singleton d)
        ==~
      liftDual (sin . SV.head) (SV.singleton d)

prop_liftSmotoh_coincides_with_liftDual_on_complexBin :: Property
prop_liftSmotoh_coincides_with_liftDual_on_complexBin =
  forAll (arbitrary @(Vec 2 (Dual Double))) $ \args ->
    let f :: Floating x => Vec 2 x -> x
        f (x :< y :< NilR) = log (1 + y^2) * sin (x ^ 2 + y*x)
    in liftSmooth @(Dual Double) f args
        ==~
       liftDual f args

prop_liftSmooth_coincides_with_liftDual_on_complex :: Property
prop_liftSmooth_coincides_with_liftDual_on_complex =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
  forAll (arbitrary @(Expr n)) $ \expr ->
  forAll (arbitrary @(Vec n (Dual Double))) $ \ds ->
    let f :: Floating x => Vec n x -> x
        f = evalExpr expr
        dualAns = liftSmooth @(Dual Double) f ds
        smoothAns = liftDual f ds
    in dualAns ==~ smoothAns

