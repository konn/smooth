{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, DataKinds, DerivingVia #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, MagicHash     #-}
{-# LANGUAGE MultiParamTypeClasses, ParallelListComp, PolyKinds        #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeApplications         #-}
{-# LANGUAGE TypeOperators                                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth.Dual where
import qualified AlgebraicPrelude                   as AP
import           Control.Lens
import           Data.Bits
import           Data.Coerce
import           Data.List
import           Data.Maybe
import           Data.Singletons.Prelude            (Sing, sing)
import           Data.Sized.Builtin                 (Sized)
import qualified Data.Sized.Builtin                 as SV
import           Data.Tuple
import           Data.Type.Natural.Class.Arithmetic (ZeroOrSucc (..),
                                                     zeroOrSucc)
import           Data.Vector                        (Vector)
import qualified Data.Vector.Unboxed                as U
import           GHC.Exts
import           GHC.TypeNats
import           Numeric.Algebra                    (Additive, Algebra, (.*))
import qualified Numeric.Algebra                    as NA
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Types
import           Numeric.Natural

-- | A ring \(\mathbb{R}[\epsilon] = \mathbb{R}[X]/X^2\) of dual numbers.
-- Corresponding to the usual forward-mode automatic differentiation.
data Dual = Dual { value :: !Double, epsilon :: Double }
  deriving
    ( Additive, NA.Monoidal, NA.Group,
      NA.Abelian, NA.Rig, NA.Commutative,
      NA.Multiplicative, NA.Semiring,
      NA.Unital, NA.Ring,
      NA.LeftModule Natural, NA.RightModule Natural,
      NA.LeftModule Integer, NA.RightModule Integer
    ) via AP.WrapNum Dual

instance NA.RightModule (AP.WrapFractional Double) Dual where
  Dual a da *. AP.WrapFractional x = Dual (a * x) (da * x)

instance NA.LeftModule (AP.WrapFractional Double) Dual where
  AP.WrapFractional x .* Dual a da = Dual (x * a) (x * da)

instance Show Dual where
  showsPrec d (Dual a 0) = showsPrec d a
  showsPrec d (Dual 0 e) = showParen (d > 10) $
    showsPrec 11 e . showString " ε"
  showsPrec d (Dual a b) = showParen (d > 10) $
    shows a . showString " + " . showsPrec 11 b . showString " ε"

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

data DualNumBasis = R | D
  deriving (Read, Show, Eq, Ord)

instance Algebra (AP.WrapFractional Double) DualNumBasis where
  mult f = f' where
    fr = f R R
    fd = f R D + f D R
    f' R = fr
    f' D = fd

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

-- | \(n\)-ary product of 'Dual' numbers,
--   which does not have mutual relation between
--   each distinct infinitesimals.
newtype Duals (n :: Nat) =
  Duals { runDuals :: Sized U.Vector (2 ^ n) Double }
  deriving (Eq, Ord)
-- Oh, it's much harader than I expected
-- to write proper instance for @'Smooth' 'Duals'@!


instance KnownNat n => Num (Duals n) where
  fromInteger n = Duals
    $ SV.unsafeToSized'
    $ U.generate (fromIntegral $ natVal' @(2 ^ n) proxy#) $
    \i -> if i == 0 then fromInteger n else 0
  (+) = coerce $ SV.zipWithSame @U.Vector @_ @_ @_ @(2^n) (+)
  {-# INLINE (+) #-}
  (-) = coerce $ SV.zipWithSame @U.Vector @_ @_ @_ @(2^n) (-)
  {-# INLINE (-) #-}
  abs = coerce $ SV.map @U.Vector @Double @_ @(2^n) abs
  {-# INLINE abs #-}
  negate = coerce $ SV.map @U.Vector @Double @_ @(2^n) negate
  {-# INLINE negate #-}
  signum = coerce $ SV.map @U.Vector @Double @_ @(2^n) signum
  {-# INLINE signum #-}
  Duals l * Duals r =
    Duals
    $ SV.unsafeToSized'
    $ U.accum (+)
        (U.replicate (fromIntegral $ natVal' @(2 ^ n) proxy#) 0.0)
    $ catMaybes
      [multDuals (i, c) (j, d)
      | (i, c) <- U.toList $ U.indexed $ SV.unsized l
      , (j, d) <- U.toList $ U.indexed $ SV.unsized r
      ]

multDuals
  :: (Int, Double) -> (Int, Double) -> Maybe (Int, Double)
multDuals (i, c) (j, d)
  | i .&. j > 0 = Nothing
  | otherwise = Just (i .|. j, c * d)

di :: forall n k. (KnownNat n, KnownNat k, n + 1 <= k) => Duals k
di =
  let n = 2 ^ natVal' @n proxy#
  in Duals $ SV.unsafeToSized' $
  U.generate (2 ^ fromIntegral (natVal' @k proxy#)) $ \i ->
    if i == n then 1 else 0

bits :: Int -> [Int]
{-# INLINE bits #-}
bits = unfoldr $ \ !i ->
  if i == 0
    then Nothing
    else Just $ swap $ i `divMod` 2

instance KnownNat n => Show (Duals n) where
  showsPrec d (Duals bs) = showParen (d > 10) $
    let n = fromIntegral @_ @Int $ natVal' @n proxy#
        ps =  [ if null ids
                then showsPrec 10 c
                else showsPrec 11 c . showChar ' '
                    . foldr1 (\a b -> a . showChar ' ' . b) ids
              | (i, c) <- U.toList $ U.indexed $ SV.unsized bs
              , let ids = [ showString "d(" . shows k . showChar ')'
                          | (k, b) <- itoList $ bits i, b == 1
                          ]
              , c /= 0, c /= -0
              ]
    in if null ps
        then showString "0"
        else foldr1 (\a b -> a . showString " + " . b) ps

