{-# LANGUAGE DataKinds, DerivingVia, ExplicitNamespaces, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses              #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, TypeOperators                                  #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth.Classes where
import           Algebra.Ring.Polynomial
import           AlgebraicPrelude                   (WrapFractional)
import qualified AlgebraicPrelude                   as AP
import           Control.Lens                       hiding ((:<))
import           Data.Map                           (Map)
import           Data.Proxy
import           Data.Singletons.Prelude            hiding (type (+), type (-))
import           Data.Sized.Builtin                 (pattern (:<), pattern NilR)
import           Data.Sized.Builtin                 (Sized)
import qualified Data.Sized.Builtin                 as SV
import           Data.Type.Natural.Builtin
import           Data.Type.Natural.Class.Arithmetic
import           Data.Vector                        (Vector)
import           GHC.TypeNats
import           Numeric.Algebra                    (Additive, Algebra, (.*))
import qualified Numeric.Algebra                    as NA
import           Numeric.Algebra.Smooth.Types
import           Numeric.Natural

{- | \(C^\infty\)-ring, or <https://ncatlab.org/nlab/show/smooth+algebra smooth algebra>.

An \(\mathbb{R}\)-algebra, o \(W\) is called /\(C^\infty\)-ring/,
or /smooth algebra/,
if for any smooth function \(f: \mathbb{R}^n \to \mathbb{R}\),
there is a lifted function \(W(f): W^n \to W\) which is compatible
cartesian structure.
-}
class
  ( NA.Module (AP.WrapFractional Double) w,
    NA.Ring w, NA.Commutative w
  )
   => SmoothRing w where
  liftSmooth
    :: KnownNat n
    => (forall a. Floating a => Vec n a -> a)
    -> Vec n w -> w

liftUnary
  :: (SmoothRing w)
  => (forall a. Floating a => a -> a)
  -> w -> w
liftUnary f = liftSmooth (f . SV.head) . SV.singleton

liftBinary
  :: (SmoothRing w)
  => (forall a. Floating a => a -> a -> a)
  -> w -> w -> w
{-# INLINE liftBinary #-}
liftBinary f =
  \a b -> liftSmooth (\(x :< y :< NilR) -> f x y) $ a :< b :< NilR

