{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators                          #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth where
import qualified AlgebraicPrelude                   as AP
import           Control.Lens
import           Data.Singletons.Prelude            hiding (type (+), type (-))
import           Data.Sized.Builtin                 (Sized)
import qualified Data.Sized.Builtin                 as SV
import           Data.Type.Natural.Builtin
import           Data.Type.Natural.Class.Arithmetic
import           Data.Vector                        (Vector)
import           GHC.TypeNats
import           Numeric.Algebra                    (Additive, Algebra, (.*))
import qualified Numeric.Algebra                    as NA
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Dual
import           Numeric.Algebra.Smooth.Types
import           Numeric.Natural

diff1
  :: (forall a. Floating a => a -> a)
  -> Double -> Double
diff1 f = epsilon . liftUnary f . (`Dual` 1)
