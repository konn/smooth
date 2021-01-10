{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Numeric.Algebra.Smooth.Types (Vec, UVec, convVec) where

import Data.ListLike
import Data.Sized.Builtin (Sized)
import qualified Data.Sized.Builtin as SV
import Data.Vector (Vector)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import GHC.TypeNats (KnownNat)

type Vec n a = Sized Vector n a

type UVec n a = Sized U.Vector n a

convVec ::
  forall u v n a.
  (G.Vector v a, G.Vector u a, KnownNat n, ListLike (u a) a) =>
  Sized v n a ->
  Sized u n a
convVec = SV.unsafeToSized' . G.convert . SV.unsized
