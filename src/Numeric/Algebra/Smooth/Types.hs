{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators                          #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth.Types (Vec(..)) where
import qualified AlgebraicPrelude   as AP
import           Data.Sized.Builtin (Sized)
import qualified Data.Sized.Builtin as SV
import           Data.Vector        (Vector)

type Vec n a = Sized Vector n a
