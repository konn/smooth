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

module Numeric.Algebra.Smooth
  ( diff1,
    module Numeric.Algebra.Smooth.Classes,
    module Numeric.Algebra.Smooth.Dual,
  )
where

import Numeric.Algebra.Smooth.Classes
import Numeric.Algebra.Smooth.Dual

diff1 ::
  Floating b =>
  (forall a. Floating a => a -> a) ->
  b ->
  b
diff1 f = epsilon . liftUnary f . (`Dual` 1)
