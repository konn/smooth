{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators                          #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth
  ( diff1,
    module Numeric.Algebra.Smooth.Classes,
    module Numeric.Algebra.Smooth.Dual
  ) where
import qualified AlgebraicPrelude               as AP
import           Data.Sized.Builtin             (Sized)
import qualified Data.Sized.Builtin             as SV
import           Data.Vector                    (Vector)
import           Numeric.Algebra                (Additive, Algebra, (.*))
import qualified Numeric.Algebra                as NA
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Dual

diff1
  :: Floating b
  => (forall a. Floating a => a -> a)
  -> b -> b
diff1 f = epsilon . liftUnary f . (`Dual` 1)
