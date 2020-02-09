{-# LANGUAGE DataKinds, ExplicitNamespaces, PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
module Numeric.Algebra.Smooth.WeilSpec where
import           Data.Proxy
import           Data.Sized.Builtin             (pattern (:<), pattern NilR,
                                                 (%!!))
import qualified Data.Sized.Builtin             as SV
import           GHC.TypeNats
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Dual
import           Numeric.Algebra.Smooth.Types
import           Numeric.Algebra.Smooth.Weil
import           Test.QuickCheck
import           Utils

prop_WeilD1_coincides_with_Dual_on_sin :: Property
prop_WeilD1_coincides_with_Dual_on_sin =
  forAll arbitrary $ \(x, dx) ->
    let l = weilToVector $ liftUnary @(Weil D1 Double) sin
            $ Weil (x :< dx :< NilR)
    in liftUnary @(Dual Double) sin (Dual x dx)
        ===
        Dual (l %!! 0) (l %!! 1)

prop_WeilD1_coincides_with_Dual_on_complexBin :: Property
prop_WeilD1_coincides_with_Dual_on_complexBin =
  forAll arbitrary $ \(a, da) (b, db) ->
    let f x y = log (1 + y^2) * sin (x ^ 2 + y*x)
        l = weilToVector $ liftBinary @(Weil D1 Double)
            f
            (Weil (a :< da :< NilR))
            (Weil (b :< db :< NilR))
    in liftBinary @(Dual Double) f (Dual a da) (Dual b db)
        ==~
        Dual (l %!! 0) (l %!! 1)

prop_WeilD1_coincides_with_Dual_on_complex :: Property
prop_WeilD1_coincides_with_Dual_on_complex =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
  forAll (arbitrary @(Expr n)) $ \expr ->
  forAll (arbitrary @(Vec n (Vec 2 Double))) $ \ds ->
    let f :: Floating x => Vec n x -> x
        f = evalExpr expr
        l = weilToVector $ liftSmooth
            @(Weil D1 Double)
            f
            (SV.map Weil ds)
        dualAns = liftSmooth @(Dual Double) f
          (SV.map (\(a :< da :< NilR) -> Dual a da) ds)
        weilAns = Dual (l %!! 0) (l %!! 1)
    in dualAns ==~ weilAns

prop_Weil_D1xD1_coincides_with_Duals_2 :: Property
prop_Weil_D1xD1_coincides_with_Duals_2 =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
  forAll (arbitrary @(Expr n)) $ \expr ->
  forAll (arbitrary @(Vec n (Duals 2 Double))) $ \ds ->
    let f :: Floating x => Vec n x -> x
        f = evalExpr expr
        l = weilToVector $ liftSmooth
            @(Weil (D1 |*| D1) Double)
            f
            (SV.map (Weil . runDuals) ds)
        dualsAns = liftSmooth @(Duals 2 Double) f
          ds
        weilAns = Duals l
    in dualsAns ==~ weilAns

prop_Weil_D1xD1xD1_coincides_with_Duals_3 :: Property
prop_Weil_D1xD1xD1_coincides_with_Duals_3 =
  forAll (resize 3 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
  forAll (resize 5 $ arbitrary @(Expr n)) $ \expr ->
  forAll (arbitrary @(Vec n (Duals 3 Double))) $ \ds ->
    let f :: Floating x => Vec n x -> x
        f = evalExpr expr
        l = weilToVector $ liftSmooth
            @(Weil (D1 |*| D1 |*| D1) Double)
            f
            (SV.map (Weil . runDuals) ds)
        dualsAns = liftSmooth @(Duals 3 Double) f
          ds
        weilAns = Duals l
    in dualsAns ==~ weilAns
