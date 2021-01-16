{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Numeric.Algebra.Smooth.Dual where

import Data.Singletons.TypeLits
import qualified Data.Sized.Builtin as SV
import qualified Data.Vector as V
import Numeric.Algebra.Smooth.Types
import Numeric.Algebra.Smooth.Weil

{- | A ring \(\mathbb{R}[\epsilon] = \mathbb{R}[X]/X^2\) of dual numbers.
 Corresponding to the usual forward-mode automatic differentiation.
-}
type Dual = Weil D1

pattern Dual :: a -> a -> Dual a
pattern Dual {value, epsilon} = Weil (value SV.:< (epsilon SV.:< (SV.Nil :: Vec 0 a) :: Vec 1 a))

{-# COMPLETE Dual :: Weil #-}

monomIndices :: KnownNat n => Vec n Bool -> V.Vector Int
monomIndices =
  V.map fst . V.filter snd . V.indexed . SV.unsized
