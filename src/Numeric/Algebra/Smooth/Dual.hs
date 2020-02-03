{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, ConstraintKinds, DataKinds #-}
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, DerivingVia #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, MagicHash         #-}
{-# LANGUAGE MultiParamTypeClasses, NoStarIsType, ParallelListComp         #-}
{-# LANGUAGE PolyKinds, QuantifiedConstraints, RankNTypes                  #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeFamilies           #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                           #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Numeric.Algebra.Smooth.Dual where
import qualified AlgebraicPrelude                   as AP
import           Control.Lens
import           Data.Bits
import           Data.Coerce
import           Data.List
import qualified Data.Map                           as M
import           Data.Maybe
import           Data.Proxy
import           Data.Singletons.Prelude            (type (<), Sing, sing,
                                                     withSingI)
import           Data.Singletons.TypeLits
import           Data.Sized.Builtin                 (Sized)
import qualified Data.Sized.Builtin                 as SV
import           Data.Tuple
import qualified Data.Type.Natural                  as PN
import           Data.Type.Natural.Builtin          (ToPeano, sToPeano)
import           Data.Type.Natural.Class.Arithmetic hiding (PNum (..))
import           Data.Type.Natural.Class.Order      hiding (type (<=))
import           Data.Type.Ordinal.Builtin
import           Data.Vector                        (Vector)
import qualified Data.Vector                        as V
import qualified Data.Vector.Unboxed                as U
import           Data.Void
import           GHC.Exts
import           GHC.TypeNats
import           Numeric.Algebra                    (Additive, Algebra, (.*))
import qualified Numeric.Algebra                    as NA
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Types
import           Numeric.Natural
import           Proof.Propositional
import           Unsafe.Coerce

type Dual = Dual' Double

-- | A ring \(\mathbb{R}[\epsilon] = \mathbb{R}[X]/X^2\) of dual numbers.
-- Corresponding to the usual forward-mode automatic differentiation.
data Dual' a = Dual { value :: !a, epsilon :: a }
  deriving (Functor, Foldable, Traversable, Eq)
  deriving
    ( Additive, NA.Monoidal, NA.Group,
      NA.Abelian, NA.Rig, NA.Commutative,
      NA.Multiplicative, NA.Semiring,
      NA.Unital, NA.Ring,
      NA.LeftModule Natural, NA.RightModule Natural,
      NA.LeftModule Integer, NA.RightModule Integer
    ) via AP.WrapNum (Dual' a)

instance Fractional a => NA.RightModule (AP.WrapFractional Double) (Dual' a) where
  Dual a da *. AP.WrapFractional x = Dual (a * realToFrac x) (da * realToFrac x)

instance Fractional a => NA.LeftModule (AP.WrapFractional Double) (Dual' a) where
  AP.WrapFractional x .* Dual a da = Dual (realToFrac x * a) (realToFrac x * da)

instance (Show a, Num a, Eq a) => Show (Dual' a) where
  showsPrec d (Dual a 0) = showsPrec d a
  showsPrec d (Dual 0 e) = showParen (d > 10) $
    showsPrec 11 e . showString " ε"
  showsPrec d (Dual a b) = showParen (d > 10) $
    shows a . showString " + " . showsPrec 11 b . showString " ε"

instance Floating a => SmoothRing (Dual' a) where
  liftSmooth = id

liftDual
  :: (KnownNat n, Floating a)
  => (forall a. Floating a => Vec n a -> a)
  -> Vec n (Dual' a) -> Dual' a
liftDual f (ds :: Vec n (Dual' a)) =
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

data DualsumBasis = R | D
  deriving (Read, Show, Eq, Ord)

instance Algebra (AP.WrapFractional Double) DualsumBasis where
  mult f = f' where
    fr = f R R
    fd = f R D + f D R
    f' R = fr
    f' D = fd

instance Num a => Num (Dual' a) where
  fromInteger n = Dual (fromInteger n) 0
  Dual a da + Dual b db = Dual (a + b) (da + db)
  Dual a da - Dual b db = Dual (a - b) (da - db)
  negate (Dual a da) = Dual (negate a) (negate da)
  Dual a da * Dual b db = Dual (a * b) (a * db + da * b)
  abs (Dual a da) = Dual (abs a) (signum a)
  signum (Dual a da) = Dual (signum a) 0

instance Fractional a => Fractional (Dual' a) where
  fromRational = (`Dual` 0) . fromRational
  Dual x dx / Dual y dy = Dual (x / y) (dx / y - x * dy / (y * y))
  recip (Dual x dx) = Dual (recip x) (- dx / (x * x))

instance Floating a => Floating (Dual' a) where
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

monomIndices :: KnownNat n => Vec n Bool -> V.Vector Int
monomIndices =
  V.map fst . V.filter snd . V.indexed . SV.unsized

nthD :: (Num a, KnownNat n) => Ordinal n -> Duals n a
nthD (OLt (sn :: Sing k)) = withKnownNat sn $ dn @k

multDiff
  :: forall n m a. (KnownNat n, KnownNat m, Eq a, Floating a)
  => Vec n Word
  -> (forall x. Floating x => Vec n x -> Vec m x)
  -> Vec n a -> Vec m a
multDiff deg f xs = case someNatVal (fromIntegral $ sum deg) of
  SomeNat (_ :: Proxy k) -> withKnownNat (sing @k) $
    let ords = sliced deg $ map nthD $ enumOrdinal (sing @k)
        trms = SV.zipWithSame (\a b -> fromCoeff a + sum b) xs ords
    in SV.map
      ( fromMaybe 0.0
      . M.lookup (SV.replicate' @_ @k True)
      . components
      )
     $ f trms

instance (Floating a, KnownNat n) => SmoothRing (Duals n a) where
  liftSmooth = id


sliced :: KnownNat n => Vec n Word -> [a] -> Vec n [a]
sliced = loop
  where
    loop :: KnownNat k => Vec k Word -> [a] -> Vec k [a]
    loop SV.NilR xs = SV.empty
    loop (n SV.:< ns) xs =
      let (lf, rest) = splitAt (fromIntegral n) xs
      in lf SV.:< loop ns rest

instance (KnownNat n, Fractional a)
      => NA.RightModule (AP.WrapFractional Double) (Duals n a) where
  a *. AP.WrapFractional x = a * realToFrac x

instance (KnownNat n, Fractional a)
      => NA.LeftModule (AP.WrapFractional Double) (Duals n a) where
  AP.WrapFractional x .* a =
    realToFrac x * a

-- | \(n\)-ary product of 'Dual' numbers,
--   which does not have mutual relation between
--   each distinct infinitesimals.
newtype Duals n a = Duals { runDuals :: Vec (2 ^ n) a }
  deriving
    ( Additive, NA.Monoidal, NA.Group,
      NA.Abelian, NA.Rig, NA.Commutative,
      NA.Multiplicative, NA.Semiring,
      NA.Unital, NA.Ring,
      NA.LeftModule Natural, NA.RightModule Natural,
      NA.LeftModule Integer, NA.RightModule Integer
    ) via AP.WrapNum (Duals n a)

halve :: forall n a. KnownNat n => Vec (2 * n) a -> (Vec n a, Vec n a)
halve xs =
  let (ls, rs) = V.splitAt (fromIntegral $ natVal' @n proxy#) $ SV.unsized xs
  in (SV.unsafeToSized' ls, SV.unsafeToSized' rs)

liftUn
  :: forall c n a.
      ( KnownNat n,
        forall k x. (KnownNat k, c x) => c (Duals k x) ,
        forall x. c x => c (Dual' x),
        c a
      )
  => (forall x. c x => x -> x)
  -> Duals n a -> Duals n a
liftUn f (Duals xs) = case sing @n of
  Zero -> Duals $ SV.singleton $ f $ SV.head xs
  Succ (n :: Sing k) ->
    let (x, dx) = halve xs
        Dual (Duals x') (Duals dx') = f $ Dual (Duals @k x) (Duals @k dx)
    in Duals $ x' SV.++ dx'

liftBin
  :: forall c n a.
      ( KnownNat n,
        forall k x. (KnownNat k, c x) => c (Duals k x) ,
        forall x. c x => c (Dual' x),
        c a
      )
  => (forall x. c x => x -> x -> x)
  -> Duals n a -> Duals n a -> Duals n a
liftBin f (Duals xs) (Duals ys) = case sing @n of
  Zero -> Duals $ SV.singleton $ f (SV.head xs) (SV.head ys)
  Succ (n :: Sing k) ->
    let (x, dx) = halve xs
        (y, dy) = halve ys
        Dual (Duals x') (Duals dx') =
          f (Dual (Duals @k x) (Duals @k dx)) (Dual (Duals @k y) (Duals @k dy))
    in Duals $ x' SV.++ dx'

fromCoeff
  :: forall n a. (KnownNat n, Num a) => a -> Duals n a
fromCoeff = Duals . (SV.:< SV.replicate (sing @(2^n - 1)) 0)

instance (KnownNat n, Num a) => Num (Duals n a) where
  fromInteger = fromCoeff . fromInteger
  (+) = liftBin @Num (+)
  (*) = liftBin @Num (*)
  (-) = liftBin @Num (-)
  negate = liftUn @Num negate
  abs = liftUn @Num abs
  signum = liftUn @Num signum

instance (KnownNat n, Fractional a) => Fractional (Duals n a) where
  fromRational = fromCoeff . fromRational
  recip = liftUn @Fractional recip
  (/) = liftBin @Fractional (/)

instance (KnownNat n, Floating a) => Floating (Duals n a) where
  pi = fromCoeff pi
  {-# INLINE pi #-}
  exp = liftUn @Floating exp
  log = liftUn @Floating log
  sqrt = liftUn @Floating sqrt
  (**) = liftBin @Floating (**)
  logBase = liftBin @Floating logBase
  sin = liftUn @Floating sin
  cos = liftUn @Floating cos
  tan = liftUn @Floating tan
  asin = liftUn @Floating asin
  acos = liftUn @Floating acos
  atan = liftUn @Floating atan
  sinh = liftUn @Floating sinh
  cosh = liftUn @Floating cosh
  tanh = liftUn @Floating tanh
  asinh = liftUn @Floating asinh
  acosh = liftUn @Floating acosh
  atanh = liftUn @Floating atanh

components
  :: forall n a. (Eq a, Num a, KnownNat n)
  => Duals n a -> M.Map (Vec n Bool) a
components (Duals xs) =
  case sing @n of
    Zero ->
      let c = SV.head xs
      in if c == 0 then M.empty else M.singleton SV.empty c
    Succ (l :: Sing l) ->
      let (s, ds) = halve xs
      in M.mapKeys (False SV.:<) (components $ Duals s)
          `M.union`
         M.mapKeys (True SV.:<) (components $ Duals ds)
{-# INLINE components #-}

instance (KnownNat n, Num a, Eq a, Show a) => Show (Duals n a) where
  showsPrec d dn =
    let terms = M.toList $ M.mapKeys monomIndices $ components dn
    in if null terms
    then showString "0"
    else foldr1 (\a b -> a . showString " + " . b)
          [ if null trm
            then shows c
            else showsPrec 11 c . showChar ' '
               . showsTerm trm
          | (trm, c) <- terms
          ]
      where
        showsTerm = foldr ((.) . (\i -> showString "d(" . shows i . showChar ')')) id

dn :: forall k n a. (Num a, KnownNat k, KnownNat n, (k < n) ~ 'True) => Duals n a
dn =
  let n = fromIntegral $ natVal' @n proxy#
      k = fromIntegral $ natVal' @k proxy#
      l = 2 ^ (n - k - 1)
  in Duals $ SV.unsafeToSized' $ V.generate (2 ^ n) $ \i ->
      if i == l then 1 else 0

halveDs
  :: KnownNat n => Duals (n + 1) a -> Dual' (Duals n a)
halveDs =
  uncurry Dual . (both %~ Duals) . halve . runDuals
