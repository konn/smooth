{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators                          #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth.Types (Vec, UVec, convVec) where
import qualified AlgebraicPrelude    as AP
import           Data.ListLike
import           Data.Sized.Builtin  (Sized)
import qualified Data.Sized.Builtin  as SV
import           Data.Vector         (Vector)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import           GHC.TypeNats        (KnownNat)

type Vec n a = Sized Vector n a
type UVec n a = Sized U.Vector n a

convVec
  :: (G.Vector v a, G.Vector u a, KnownNat n, ListLike (u a) a)
  => Sized v n a -> Sized u n a
convVec = SV.unsafeToSized' . G.convert . SV.unsized
