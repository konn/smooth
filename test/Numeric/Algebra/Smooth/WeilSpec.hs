{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Algebra.Prelude.Core (IsPolynomial (terms', var), Polynomial, SNat, toIdeal, withKnownNat)
import qualified Algebra.Prelude.Core as AP
import AlgebraicPrelude (WrapFractional (WrapFractional))
import Control.Lens (alaf)
import Data.Foldable as F
import qualified Data.Map as M
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Data.MonoTraversable
import Data.Monoid (Product (Product))
import Data.Proxy
import Data.Reflection
import Data.Semialign.Indexed
import Data.Singletons.Prelude (sing)
import Data.Sized
  ( (%!!),
    pattern Nil,
    pattern (:<),
  )
import qualified Data.Sized as SV
import Data.These
import qualified Data.Vector as V
import GHC.Exts (proxy#)
import GHC.TypeNats
import qualified Numeric.AD as AD
import Numeric.Algebra.Smooth
import Numeric.Algebra.Smooth.Classes ()
import Numeric.Algebra.Smooth.Dual ()
import Numeric.Algebra.Smooth.PowerSeries (factorial, walkAlong)
import Numeric.Algebra.Smooth.Types
import Numeric.Algebra.Smooth.Weil
import Test.QuickCheck
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Utils

prop_WeilD1_coincides_with_Dual_on_sin :: Property
prop_WeilD1_coincides_with_Dual_on_sin =
  forAll arbitrary $ \(x, dx) ->
    let l =
          weilToVector $
            liftUnary @(Weil D1 Double) sin $
              Weil (x :< dx :< Nil)
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
              (Weil (a :< da :< Nil))
              (Weil (b :< db :< Nil))
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
                (SV.map (\(a :< da :< Nil) -> Dual a da) ds)
            weilAns = Dual (l %!! 0) (l %!! 1)
         in dualAns ==~ weilAns

prop_Weil_Cubic_computes_upto_2nd_derivative_for_sin :: Property
prop_Weil_Cubic_computes_upto_2nd_derivative_for_sin =
  forAll (arbitrary @Double) $ \a ->
    let [fa, f'a, f''adiv2] =
          F.toList $
            weilToVector $
              liftUnary @(Weil Cubic Double)
                sin
                (Weil $ a :< 1 :< 0 :< Nil)
     in fa ==~ sin a
          .&&. f'a ==~ cos a
          .&&. f''adiv2 ==~ -0.5 * sin a

prop_Weil_Cubic_computes_upto_2nd_derivative :: Property
prop_Weil_Cubic_computes_upto_2nd_derivative =
  forAll (arbitrary @(TotalExpr 1)) $ \(TotalExpr expr) ->
    forAll (arbitrary @Double) $ \a ->
      let f :: Floating x => x -> x
          f x = evalExpr expr (SV.singleton @V.Vector x)
          faAns : f'aAns : f''aAns : _ = AD.diffs0 f a
          [fa, f'a, f''adiv2] =
            F.toList $
              weilToVector $
                liftSmooth @(Weil Cubic Double)
                  (evalExpr expr)
                  ( SV.singleton $ Weil $ a :< 1 :< 0 :< Nil ::
                      Vec 1 (Weil Cubic Double)
                  )
       in fa ==~ faAns
            .&&. f'a ==~ f'aAns
            .&&. f''adiv2 ==~ (f''aAns / 2)

data SmoothFunc where
  SmoothFunc :: (forall x. Floating x => x -> x) -> SmoothFunc

diff1' :: SmoothFunc -> SmoothFunc
diff1' (SmoothFunc f) = SmoothFunc (AD.diff f)

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

prop_diffUpTo_equivalent_to_diffs :: Property
prop_diffUpTo_equivalent_to_diffs =
  forAll (resize 5 arbitrary) $ \n ->
    forAll (arbitrary @(TotalExpr 1)) $ \(TotalExpr expr) ->
      forAll (arbitrary @Double) $ \a ->
        let f :: Floating x => x -> x
            f = evalExpr expr . SV.singleton @V.Vector
            teacher = M.filter (/= 0) $ M.fromList $ zip [0 .. n] $ AD.diffs f a
            tested = M.filter (/= 0) (diffUpTo n f a)
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

test_WeilProduct :: TestTree
test_WeilProduct =
  testGroup
    "Weil (Dn |*| Dk)"
    [ testProperty "D2 |*| D3" $ chkWeilProduct (sing @2) (sing @3)
    , testProperty "D3 |*| D2" $ chkWeilProduct (sing @3) (sing @2)
    , testProperty "D2 |*| D4" $ chkWeilProduct (sing @2) (sing @4)
    , testProperty "D4 |*| D5" $ chkWeilProduct (sing @4) (sing @5)
    , testProperty "D4 |*| D5 (regression)" $ chkWeilProduct (sing @4) (sing @5) (TotalExpr theExpr)
    , testProperty "D2 |*| D3 |*| D4" $ \(TotalExpr expr :: TotalExpr 3) (x :: Double) y z ->
        let f :: forall x. Floating x => Vec 3 x -> x
            f = evalExpr expr
            table = AD.grads f (x :< y :< z :< Nil)
            expected :: Map (UVec 3 Int) Double
            expected =
              M.fromList
                [ (SV.map fromIntegral deg, walkAlong deg table)
                | deg <-
                    otraverse (enumFromTo 0) $
                      SV.unsafeFromList' @_ @_ @3 [1, 2, 3]
                ]
            result =
              M.mapMaybe
                ( \(WrapFractional d) ->
                    if d == 0 then Nothing else Just d
                )
                $ terms' $
                  weilToPoly $
                    liftSmooth
                      @(Weil (DOrder 2 |*| DOrder 3 |*| DOrder 4) Double)
                      f
                      (injCoeWeil x + di 0 :< injCoeWeil y + di 1 :< injCoeWeil z + di 2 :< Nil)
         in conjoin $
              toList $
                ialignWith
                  ( \k th ->
                      counterexample ("Partial Derivative: " <> show k) $
                        case th of
                          (This d) -> d ==~ 0
                          (That d) -> 0 ==~ d
                          (These d d') ->
                            fromIntegral
                              (alaf Product ofoldMap (factorial . fromIntegral) k)
                              * d ==~ d'
                  )
                  result
                  expected
    ]

chkWeilProduct :: SNat n -> SNat m -> TotalExpr 2 -> Double -> Double -> Property
chkWeilProduct
  (sn :: SNat n)
  (sm :: SNat m)
  (TotalExpr expr :: TotalExpr 2)
  (x :: Double)
  y =
    withKnownNat sn $
      withKnownNat sm $
        let n = fromIntegral $ natVal sn
            m = fromIntegral $ natVal sm
            f :: forall x. Floating x => Vec 2 x -> x
            f = evalExpr expr
            expected :: Map (UVec 2 Int) Double
            expected =
              M.fromList
                [ ( fromIntegral n0 :< fromIntegral m0 :< Nil
                  , AD.diffs
                      ( \b ->
                          AD.diffs
                            (\a -> f $ a :< AD.auto b :< Nil)
                            (AD.auto x)
                            !? n0
                      )
                      (AD.auto y)
                      !? m0
                  )
                | n0 <- [0 .. n -1]
                , m0 <- [0 .. m -1]
                ]
            result =
              M.mapMaybe
                ( \(WrapFractional d) ->
                    if d == 0 then Nothing else Just d
                )
                $ terms' $
                  weilToPoly $
                    liftSmooth
                      @(Weil (DOrder n |*| DOrder m) Double)
                      f
                      (injCoeWeil x + di 0 :< injCoeWeil y + di 1 :< Nil)
         in conjoin $
              toList $
                ialignWith
                  ( \k th ->
                      counterexample ("Partial Derivative: " <> show k) $
                        case th of
                          (This d) -> d ==~ 0
                          (That d) -> 0 ==~ d
                          (These d d') ->
                            fromIntegral
                              (alaf Product ofoldMap (factorial . fromIntegral) k)
                              * d ==~ d'
                  )
                  result
                  expected

test_liftSmoothEquiv :: TestTree
test_liftSmoothEquiv =
  testGroup
    "lifting operators"
    [ testGroup
      (name ++ " is equivalent to liftSmoothSeries")
      [ testGroup
          "D1"
          [ testProperty "unary" $ compareToSmoothSeries @D1 @1 lifter
          , testProperty "binary" $ compareToSmoothSeries @D1 @2 lifter
          , testProperty "ternary" $ compareToSmoothSeries @D1 @3 lifter
          ]
      , testGroup
          "D2"
          [ testProperty "unary" $ compareToSmoothSeries @D2 @1 lifter
          , testProperty "binary" $ compareToSmoothSeries @D2 @2 lifter
          , testProperty "ternary" $ compareToSmoothSeries @D2 @3 lifter
          ]
      , testGroup
          "DOrder 4"
          [ testProperty "unary" $ compareToSmoothSeries @(DOrder 4) @1 lifter
          , testProperty "binary" $ compareToSmoothSeries @(DOrder 4) @2 lifter
          , testProperty "ternary" $ compareToSmoothSeries @(DOrder 4) @3 lifter
          ]
      , testGroup
          "DOrder 3 |*| DOrder 4"
          [ testProperty "unary" $ compareToSmoothSeries @(DOrder 3 |*| DOrder 4) @1 lifter
          , testProperty "binary" $ compareToSmoothSeries @(DOrder 3 |*| DOrder 4) @2 lifter
          , testProperty "ternary" $ compareToSmoothSeries @(DOrder 3 |*| DOrder 4) @3 lifter
          ]
      , testGroup "R[x,y]/(x^3-y^2,y^3)" $
          fromJust $
            reifyWeil
              (toIdeal [var 0 ^ 3 - var 1 ^ 2, var 1 ^ 3 :: Polynomial AP.Rational 2])
              $ \(_ :: Proxy w) ->
                [ testProperty "unary" $ compareToSmoothSeries @w @1 lifter
                , testProperty "binary" $
                    forAll (resize 3 arbitrary) $ compareToSmoothSeries @w @2 lifter
                ]
      ]
    | (name, lifter) <-
        [ ("liftSmoothSeriesAD", WeilLifter liftSmoothSeriesAD)
        , ("liftSmoothSuccinctTower", WeilLifter liftSmoothSuccinctTower)
        ]
    ]

newtype WeilLifter = WeilLifter
  { runWeilLifter ::
      forall k w' n' m'.
      (KnownNat k, KnownNat n', KnownNat m', Reifies w' (WeilSettings n' m')) =>
      (forall x. Floating x => Vec k x -> x) ->
      Vec k (Weil w' Double) ->
      Weil w' Double
  }

compareToSmoothSeries ::
  forall w k n m.
  (KnownNat n, KnownNat m, KnownNat k, Reifies w (WeilSettings n m)) =>
  WeilLifter ->
  TotalExpr k ->
  Vec k (Vec n Double) ->
  Property
compareToSmoothSeries lifter (TotalExpr expr) inps =
  let Weil finitary = liftSmoothSeries @w (evalExpr expr) $ Weil <$> inps
      Weil series = runWeilLifter lifter @k @w (evalExpr expr) $ Weil <$> inps
   in finitary ==~ series

theExpr :: Expr 2
theExpr =
  Atan (K 0.8 :* (Arg 1 :^ 2 :* Cos (Arg 0)))

test_diffUpTo :: TestTree
test_diffUpTo =
  testGroup
    "diffUpTo behaves similarly to ad package's diffs"
    [ testProperty
        "randomised"
        $ forAll (resize 5 arbitrary) chkDiffUpTo
    , testProperty "regression (atan)" $
        chkDiffUpTo 9 $
          TotalExpr $ Atan (Arg 0)
    ]

chkDiffUpTo :: AP.Natural -> TotalExpr 1 -> Double -> Property
chkDiffUpTo n (TotalExpr expr) x =
  tabulate "degree" [show n] $
    let f :: Floating x => x -> x
        f = evalExpr expr . SV.singleton @V.Vector
        dual = diffUpTo (fromIntegral n) f (x :: Double)
        ad = M.fromAscList $ zip [0 ..] $ take (fromIntegral n + 1) $ AD.diffs f x
     in conjoin $
          F.toList $
            ialignWith
              ( \deg ->
                  counterexample (show deg ++ "th derivative") . \case
                    These l r -> l ==~ r
                    That r -> 0 ==~ r
                    This l -> l ==~ 0
              )
              dual
              ad
