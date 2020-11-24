{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Numeric.Algebra.Smooth.WeilSpec where

import Data.Foldable as F
import qualified Data.Map as M
import Data.Proxy
import Data.Semialign.Indexed
import Data.Singletons.Prelude (sing)
import Data.Sized.Builtin
  ( (%!!),
    pattern NilR,
    pattern (:<),
  )
import qualified Data.Sized.Builtin as SV
import Data.These
import qualified Data.Vector as V
import GHC.Exts (proxy#)
import GHC.TypeNats
import Numeric.Algebra.Smooth
import Numeric.Algebra.Smooth.Classes ()
import Numeric.Algebra.Smooth.Dual ()
import Numeric.Algebra.Smooth.Types
import Numeric.Algebra.Smooth.Weil
import Test.QuickCheck
import Utils

prop_WeilD1_coincides_with_Dual_on_sin :: Property
prop_WeilD1_coincides_with_Dual_on_sin =
  forAll arbitrary $ \(x, dx) ->
    let l =
          weilToVector $
            liftUnary @(Weil D1 Double) sin $
              Weil (x :< dx :< NilR)
     in liftUnary @(Dual Double) sin (Dual x dx)
          === Dual (l %!! 0) (l %!! 1)

prop_WeilD1_coincides_with_Dual_on_complexBin :: Property
prop_WeilD1_coincides_with_Dual_on_complexBin =
  forAll arbitrary $ \(a, da) (b, db) ->
    let f x y = log (1 + y ^ 2) * sin (x ^ 2 + y * x)
        l =
          weilToVector $
            liftBinary @(Weil D1 Double)
              f
              (Weil (a :< da :< NilR))
              (Weil (b :< db :< NilR))
     in liftBinary @(Dual Double) f (Dual a da) (Dual b db)
          ==~ Dual (l %!! 0) (l %!! 1)

prop_WeilD1_coincides_with_Dual_on_complex :: Property
prop_WeilD1_coincides_with_Dual_on_complex =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (arbitrary @(TotalExpr n)) $ \(TotalExpr expr) ->
      forAll (arbitrary @(Vec n (Vec 2 Double))) $ \ds ->
        let f :: Floating x => Vec n x -> x
            f = evalExpr expr
            l =
              weilToVector $
                liftSmooth
                  @(Weil D1 Double)
                  f
                  (SV.map Weil ds)
            dualAns =
              liftSmooth @(Dual Double)
                f
                (SV.map (\(a :< da :< NilR) -> Dual a da) ds)
            weilAns = Dual (l %!! 0) (l %!! 1)
         in dualAns ==~ weilAns

prop_Weil_D1xD1_coincides_with_Duals_2 :: Property
prop_Weil_D1xD1_coincides_with_Duals_2 =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (arbitrary @(TotalExpr n)) $ \(TotalExpr expr) ->
      forAll (arbitrary @(Vec n (Duals 2 Double))) $ \ds ->
        let f :: Floating x => Vec n x -> x
            f = evalExpr expr
            l =
              weilToVector $
                liftSmooth
                  @(Weil (D1 |*| D1) Double)
                  f
                  (SV.map (Weil . runDuals) ds)
            dualsAns =
              liftSmooth @(Duals 2 Double)
                f
                ds
            weilAns = Duals l
         in dualsAns ==~ weilAns

prop_Weil_D1xD1xD1_coincides_with_Duals_3 :: Property
prop_Weil_D1xD1xD1_coincides_with_Duals_3 =
  forAll (resize 3 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (resize 5 $ arbitrary @(TotalExpr n)) $ \(TotalExpr expr) ->
      forAll (arbitrary @(Vec n (Duals 3 Double))) $ \ds ->
        let f :: Floating x => Vec n x -> x
            f = evalExpr expr
            l =
              weilToVector $
                liftSmooth
                  @(Weil (D1 |*| D1 |*| D1) Double)
                  f
                  (SV.map (Weil . runDuals) ds)
            dualsAns =
              liftSmooth @(Duals 3 Double)
                f
                ds
            weilAns = Duals l
         in dualsAns ==~ weilAns

prop_Weil_Cubic_computes_upto_2nd_derivative_for_sin :: Property
prop_Weil_Cubic_computes_upto_2nd_derivative_for_sin =
  forAll (arbitrary @Double) $ \a ->
    let [fa, f'a, f''adiv2] =
          F.toList $
            weilToVector $
              liftUnary @(Weil Cubic Double)
                sin
                (Weil $ a :< 1 :< 0 :< NilR)
     in fa ==~ sin a
          .&&. f'a ==~ cos a
          .&&. f''adiv2 ==~ -0.5 * sin a

prop_Weil_Cubic_computes_upto_2nd_derivative :: Property
prop_Weil_Cubic_computes_upto_2nd_derivative =
  forAll (arbitrary @(TotalExpr 1)) $ \(TotalExpr expr) ->
    forAll (arbitrary @Double) $ \a ->
      let [fa, f'a, f''adiv2] =
            F.toList $
              weilToVector $
                liftSmooth @(Weil Cubic Double)
                  (evalExpr expr)
                  ( SV.singleton $ Weil $ a :< 1 :< 0 :< NilR ::
                      Vec 1 (Weil Cubic Double)
                  )
       in fa ==~ evalExpr expr (SV.singleton a :: Vec 1 Double)
            .&&. f'a ==~ diff1 (evalExpr expr . SV.singleton @V.Vector) a
            .&&. f''adiv2 ==~ diff1 (diff1 (evalExpr expr . SV.singleton @V.Vector)) a / 2

data SmoothFunc where
  SmoothFunc :: (forall x. Floating x => x -> x) -> SmoothFunc

diff1' :: SmoothFunc -> SmoothFunc
diff1' (SmoothFunc f) = SmoothFunc (diff1 f)

prop_Weil_DOrder_n_computes_upto_n_minus_1st_derivative :: Property
prop_Weil_DOrder_n_computes_upto_n_minus_1st_derivative =
  forAll (resize 5 arbitrary) $ \(SomeNat (_ :: Proxy n)) ->
    forAll (arbitrary @(TotalExpr 1)) $ \(TotalExpr expr) ->
      forAll (arbitrary @Double) $ \a ->
        let f :: Floating x => x -> x
            f = evalExpr expr . SV.singleton @V.Vector
            ds =
              V.imap
                (\i (SmoothFunc g) -> g a / fromIntegral (product [1 .. i]))
                $ V.iterateN
                  (fromIntegral $ natVal' @n proxy# + 1)
                  diff1'
                  (SmoothFunc f)
            ans =
              V.fromList $
                F.toList $
                  weilToVector $
                    liftUnary @(Weil (DOrder (n + 1)) Double)
                      f
                      ( Weil $
                          SV.generate sing $
                            \i ->
                              if i == 0
                                then a
                                else
                                  if i == 1
                                    then 1
                                    else 0
                      )
         in counterexample
              "non-zero result count mismatch"
              (V.length ds === V.length ans)
              .&&. conjoin
                (zipWith (==~) (F.toList ds) (F.toList ans))

prop_diffUpTo'_equivalent_to_diffUpTo :: Property
prop_diffUpTo'_equivalent_to_diffUpTo =
  forAll (resize 5 arbitrary) $ \n ->
    forAll (arbitrary @(TotalExpr 1)) $ \(TotalExpr expr) ->
      forAll (arbitrary @Double) $ \a ->
        let f :: Floating x => x -> x
            f = evalExpr expr . SV.singleton @V.Vector
            teacher = M.filter (/= 0) (diffUpTo n f a)
            tested = M.filter (/= 0) (diffUpTo' n f a)
         in conjoin $
              F.toList $
                ialignWith
                  ( \k -> \case
                      (This d) ->
                        counterexample
                          ( "diffUpTo has non-zero coeff " <> show d
                              <> " with power "
                              <> show k
                              <> "but diffUpTo' doesn't"
                          )
                          False
                      (That d) ->
                        counterexample
                          ( "diffUpTo' has non-zero coeff " <> show d
                              <> " with power "
                              <> show k
                              <> "but diffUpTo doesn't"
                          )
                          False
                      (These d d7) -> d ==~ d7
                  )
                  teacher
                  tested
