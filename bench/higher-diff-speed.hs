{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Algebra.Prelude.Core (IsOrderedPolynomial (coeff, leadingMonomial), Polynomial, toNatural, toSomeSNat, vars)
import qualified AlgebraicPrelude as AP
import Data.Data
import Data.List (inits)
import qualified Data.Map.Strict as Map
import Data.Reflection
import Data.Type.Natural (SNat (Succ, Zero), SomeSNat (SomeSNat), withKnownNat)
import Data.Type.Ordinal (enumOrdinal)
import GHC.TypeNats (KnownNat, type (^))
import Gauge
import Numeric.Algebra.Smooth.Weil

main :: IO ()
main =
  defaultMain
    [ bgroup
      lab
      [ case toSomeSNat n of
        SomeSNat sn ->
          bgroup
            (show n)
            [ bench "tensors" $ nf (diffUpToTensor sn input) 1.0
            , bench "Dn" $ nf (diffUpToDn sn input) 1.0
            ]
      | n <- [1 .. 10]
      ]
    | (lab, MkSmooth input) <-
        [ ("identity", MkSmooth id)
        , ("exp x", MkSmooth exp)
        ,
          ( "x * exp (-x * x + x)"
          , MkSmooth $ \x ->
              x * exp (- x * x + x)
          )
        ]
    ]

data SomeDuals n where
  MkSomeDuals :: (KnownNat n, KnownNat (2 ^ n), Reifies w (WeilSettings (2 ^ n) n)) => Proxy w -> SomeDuals n

deriving instance Show (SomeDuals n)

someDuals :: SNat n -> SomeDuals n
someDuals Zero = error "error: SomeDuals 0"
someDuals (Succ Zero) = MkSomeDuals $ Proxy @D1
someDuals sn@(Succ n) = withKnownNat sn $
  case someDuals n of
    MkSomeDuals (_ :: Proxy w) ->
      MkSomeDuals $ Proxy @(w |*| D1)

diffUpToTensor :: forall n. SNat n -> (forall x. Floating x => x -> x) -> Double -> [Double]
diffUpToTensor Zero f x = [f x]
diffUpToTensor sn f x = case someDuals sn of
  MkSomeDuals (_ :: Proxy w) ->
    let ords = map (di @Double @w) $ enumOrdinal sn
        input = injCoeWeil x + sum ords
        terms = weilToPoly $ f input
     in [ AP.unwrapFractional $ coeff mon terms
        | vs <- inits $ vars @(Polynomial AP.Rational n)
        , let mon = leadingMonomial $ product vs
        ]

diffUpToDn ::
  (Floating a, Eq a) =>
  SNat n ->
  (forall x. Floating x => x -> x) ->
  Double ->
  [Double]
diffUpToDn sn f =
  map snd . Map.toAscList . diffUpTo (toNatural sn) f

newtype Smooth where
  MkSmooth :: (forall x. Floating x => x -> x) -> Smooth
