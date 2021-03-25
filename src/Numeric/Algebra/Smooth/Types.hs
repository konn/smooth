{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Numeric.Algebra.Smooth.Types (Vec, UVec, convVec) where

import Data.Sized (Sized)
import qualified Data.Sized as SV
import Data.Vector (Vector)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import GHC.TypeNats (KnownNat)

type Vec n a = Sized Vector n a

type UVec n a = Sized U.Vector n a

convVec ::
  forall u v n a.
  (G.Vector v a, G.Vector u a, KnownNat n, SV.DomC u a) =>
  Sized v n a ->
  Sized u n a
convVec = SV.unsafeToSized' . G.convert . SV.unsized
