{-# LANGUAGE DataKinds, GADTs, ParallelListComp, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeOperators      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth where
import           Control.Lens
import           Data.Singletons.Prelude            hiding (type (+), type (-))
import           Data.Sized.Builtin                 (Sized)
import qualified Data.Sized.Builtin                 as SV
import           Data.Type.Natural.Builtin
import           Data.Type.Natural.Class.Arithmetic
import           Data.Vector                        (Vector)
import           GHC.TypeNats

type Vec n a = Sized Vector n a

{- | \(C^\infty\)-ring, or <https://ncatlab.org/nlab/show/smooth+algebra smooth algebra>.

An \(\mathbb{R}\)-algebra, o \(W\) is called /\(C^\infty\)-ring/,
or /smooth algebra/,
if for any smooth function \(f: \mathbb{R}^n \to \mathbb{R}\),
there is a lifted function \(W(f): W^n \to W\) which is compatible
cartesian structure.
-}
class SmoothRing w where
  liftSmooth
    :: KnownNat n
    => (forall a. Floating a => Vec n a -> a)
    -> Vec n w -> w

liftUnary
  :: (SmoothRing w)
  => (forall a. Floating a => a -> a)
  -> w -> w
liftUnary f = liftSmooth (f . SV.head) . SV.singleton

diff1
  :: (forall a. Floating a => a -> a)
  -> Double -> Double
diff1 f = epsilon . liftUnary f . (`Dual` 1)

-- | A ring \(\mathbb{R}[\epsilon] = \mathbb{R}[X]/X^2\) of dual numbers.
-- Corresponding to the usual forward-mode automatic differentiation.
data Dual = Dual { value :: !Double, epsilon :: Double }

instance Show Dual where
  showsPrec d (Dual a 0) = showsPrec d a
  showsPrec d (Dual 0 e) = showParen (d > 10) $
    showsPrec 11 e . showString " ε"
  showsPrec d (Dual a b) = showParen (d > 10) $
    shows a . showString " + " . showsPrec 11 b . showString " ε"

instance Num Dual where
  fromInteger n = Dual (fromInteger n) 0
  Dual a da + Dual b db = Dual (a + b) (da + db)
  Dual a da - Dual b db = Dual (a - b) (da - db)
  negate (Dual a da) = Dual (negate a) (negate da)
  Dual a da * Dual b db = Dual (a * b) (a * db + da * b)
  abs (Dual a da) = Dual (abs a) (signum a)
  signum (Dual a da) = Dual (signum a) 0

instance Fractional Dual where
  fromRational = (`Dual` 0) . fromRational
  Dual x dx / Dual y dy = Dual (x / y) (dx / y - x * dy / (y * y))
  recip (Dual x dx) = Dual (recip x) (- dx / (x * x))

instance Floating Dual where
  pi = Dual pi 0
  exp (Dual a da) = Dual (exp a) (da * exp a)
  sin (Dual a da) = Dual (sin a) (da * cos a)
  cos (Dual a da) = Dual (cos a) (-da * sin a)
  tan (Dual a da) = Dual (tan a) (da / cos a ^^ 2)
  log (Dual a da) = Dual (log a) (da / a)
  asin (Dual a da) = Dual (asin a) (da / sqrt (1 - a ^^ 2))
  acos (Dual a da) = Dual (acos a) (da / (- sqrt (1 - a ^^ 2)))
  atan (Dual a da) = Dual (atan a) (da / (a^2 + 1))
  sinh (Dual a da) = Dual (sinh a) (da * cosh a)
  cosh (Dual a da) = Dual (cosh a) (da * sinh a)
  tanh (Dual a da) = Dual (tanh a) (da / cosh a ^^ 2)
  asinh (Dual a da) = Dual (asinh a) (da / sqrt (1 + a ^^ 2))
  acosh (Dual a da) = Dual (acosh a) (da / sqrt (a ^^ 2 - 1))
  atanh (Dual a da) = Dual (atanh a) (da / (1 - a ^^ 2))

instance SmoothRing Dual where
  liftSmooth f (ds :: Vec n Dual) =
    let reals = value <$> ds
        duals = epsilon <$> ds
        coes =
          imap
            (\i bi -> bi * epsilon
                (f $
                SV.unsafeFromList'
                [ Dual ai (if i == k then 1 else 0)
                | ai <- SV.toList reals
                | k <- [0..]
                ])
            )
          duals
        fa = f reals
    in Dual fa $ sum coes

-- | Unary formal power series, or Tower.
newtype Series k = Series { runSeries :: [k] }

newtype PowerSeries n k = Powers { getCoeff :: Vec n Word -> k }

monomsOfDeg
  :: forall n. KnownNat n => Word -> [Vec n Word]
monomsOfDeg 0 = [SV.replicate' 0]
monomsOfDeg n =
  case zeroOrSucc (sing @n) of
    IsZero                -> []
    IsSucc (sn :: Sing m) ->
      concat
      [ map (k SV.<|) $ monomsOfDeg @m (n - k)
      | k <- [0..n]
      ]

cutoff :: KnownNat n => Word -> PowerSeries n k -> [(Vec n Word, k)]
cutoff n = takeWhile ((<= n) . sum . fst) . terms

terms :: KnownNat n => PowerSeries n k -> [(Vec n Word, k)]
terms (Powers f) =
    [ (m, f m)
    | k <- [0..]
    , m <- monomsOfDeg k
    ]
