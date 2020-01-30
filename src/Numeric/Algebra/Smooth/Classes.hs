{-# LANGUAGE DataKinds, DerivingVia, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators            #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}module Numeric.Algebra.Smooth.Classes where
import           Algebra.Ring.Polynomial
import           AlgebraicPrelude                   (WrapFractional)
import qualified AlgebraicPrelude                   as AP
import           Control.Lens
import           Data.Map                           (Map)
import           Data.Proxy
import           Data.Singletons.Prelude            hiding (type (+), type (-))
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

{- | Weil algebra.

Weil algebra \(W\) is a \(R\)-algebra together with a unique maximal ideal \(\mathfrak{M}\), which is nipotent and \(W = \mathbb{R} \oplus \mathfrak{M}\) holds.

There are some good characterisation of Weil algebra; the following are equivalent:

  1. \(W\) is a Weil algebra,
  2. \(W\) is isomorphic to a quotient \(\mathbb{R}[X_1, \dots, X_n]/I\) of polynomial ring, and there exists \(k\) such that \(X_1^{k_1} \dots X_n^{k_n} \in I\) for all \(k_1 + \dots + k_n = k\),
  3. \(W\) is isomoprhic to a quotient \(\mathbb{R}[\![X_1, \dots, X_n]\!]/I\) of a ring of formal power series, such that \(I \supseteq (X_1, \dots, X_n)^k\) for some \(k\).
-}
class WeilAlgebra w where
  -- | The order of nilpotence
  type Order w :: Nat
  -- | Number of infintiesimals
  type WeilArity w :: Nat
  fromPoly :: Polynomial Double (WeilArity w) -> w
  toPoly :: w -> Polynomial Double (WeilArity w)

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
