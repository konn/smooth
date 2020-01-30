{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications                       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth.PowerSeries where
import           Data.Singletons.Prelude
import qualified Data.Sized.Builtin                 as SV
import           Data.Type.Natural.Class.Arithmetic (ZeroOrSucc (..),
                                                     zeroOrSucc)
import           GHC.TypeNats
import           Numeric.Algebra.Smooth.Types

-- | Unary formal power series, or Tower.
newtype Series k = Series { runSeries :: [k] }

newtype PowerSeries n k = Powers { getCoeff :: Vec n Word -> k }

monomsOfDeg
  :: forall n. KnownNat n => Word -> [Vec n Word]
monomsOfDeg 0 = [SV.replicate' 0]
monomsOfDeg n =
  case zeroOrSucc (sing @n) of
    IsZero                -> []
    IsSucc (sn :: Sing m) ->
      concat
      [ map (k SV.<|) $ monomsOfDeg @m (n - k)
      | k <- [0..n]
      ]

cutoff :: KnownNat n => Word -> PowerSeries n k -> [(Vec n Word, k)]
cutoff n = takeWhile ((<= n) . sum . fst) . terms

terms :: KnownNat n => PowerSeries n k -> [(Vec n Word, k)]
terms (Powers f) =
    [ (m, f m)
    | k <- [0..]
    , m <- monomsOfDeg k
    ]
