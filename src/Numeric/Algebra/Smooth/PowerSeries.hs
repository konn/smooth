{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, ConstraintKinds, DataKinds #-}
{-# LANGUAGE DeriveGeneric, DerivingVia, FlexibleContexts                  #-}
{-# LANGUAGE FlexibleInstances, GADTs, LambdaCase, MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds, QuantifiedConstraints, RankNTypes                  #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications                         #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
module Numeric.Algebra.Smooth.PowerSeries where
import qualified AlgebraicPrelude                   as AP
import           Control.Lens
import           Data.Coerce
import           Data.Profunctor
import           Data.Singletons.Prelude
import qualified Data.Sized.Builtin                 as SV
import           Data.Type.Natural.Class.Arithmetic (ZeroOrSucc (..),
                                                     zeroOrSucc)
import           Data.Type.Ordinal.Builtin
import qualified Data.Vector                        as V
import           GHC.Conc
import           GHC.Generics
import           GHC.TypeNats
import qualified Numeric.Algebra                    as NA
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.Dual
import           Numeric.Algebra.Smooth.Types
import           Numeric.Natural

-- | Unary formal power series, or Tower.
newtype Series k = Series { runSeries :: [k] }
  deriving (Eq, Generic)
  deriving
    ( NA.Additive, NA.Monoidal, NA.Group,
      NA.Abelian, NA.Rig, NA.Commutative,
      NA.Multiplicative, NA.Semiring,
      NA.Unital, NA.Ring,
      NA.LeftModule Natural, NA.RightModule Natural,
      NA.LeftModule Integer, NA.RightModule Integer
    ) via AP.WrapNum (Series k)

convolve :: Num a => [a] -> [a] -> [a]
convolve = loop
  where
    loop ~(x : xs) ~(y : ys) =
      x * y :
        zipWith3
        (\a b c -> a `par` b `par` c `seq` (a + b + c)) (map (x*) ys) (map (y*) xs) (0 : loop xs ys)
{-# INLINE convolve #-}

formalDiff
  :: Num a => Series a -> Series a
formalDiff =
  Series . tail . imap (\i c -> fromIntegral i * c ) . runSeries

constTerm :: Series c -> c
constTerm = head . runSeries

nthDiffZero
  :: forall a n. (KnownNat n, Eq a, Floating a)
  => Word
  -> (forall x. Floating x => Vec n x -> x)
  -> Vec n (Series a) -> a
nthDiffZero 0 f vs = f $ SV.map constTerm vs
nthDiffZero n f vs =
  evalTree
    (foldr1 (.) (replicate (fromIntegral n) diffTree)
    $ DiffFun (SV.replicate' 0))
    f vs

instance (Floating a, Eq a)
      => NA.LeftModule (AP.WrapFractional Double) (Series a) where
  (.*) (AP.WrapFractional a) = coerce $ map @a (realToFrac a *)

instance (Floating a, Eq a)
      => NA.RightModule (AP.WrapFractional Double) (Series a) where
  Series xs *. AP.WrapFractional a = coerce $ map (* realToFrac a) xs

instance (Floating a, Eq a) => SmoothRing (Series a) where
  liftSmooth f vs = Series $ go 0 1.0 (DiffFun $ SV.replicate' 0)
    where
      go !n !r !trm = (evalTree trm f vs * fromRational r)
                  : go (n + 1) (r / (n + 1)) (diffTree trm)

diag :: (Num a, KnownNat n) => SV.Ordinal n -> Vec n a
diag i = SV.generate sing $ \j -> if i == j then 1 else 0

data Tree n a
  = Mul !(Tree n a) !(Tree n a)
  | Add !(Tree n a) !(Tree n a)
  | DiffArg !Word !(SV.Ordinal n)
  | DiffFun !(Vec n Word)
  | K !a
    deriving (Eq, Ord)

instance (KnownNat n, Show a) => Show (Tree n a) where
  showsPrec d (K a) = showsPrec d a
  showsPrec d (Mul l r) = showParen (d > 11) $
    showsPrec 11 l . showString " * " . showsPrec 11 r
  showsPrec d (Add l r) = showParen (d > 10) $
    showsPrec 10 l . showString " + " . showsPrec 10 r
  showsPrec _ (DiffArg 0 i) =
    showString "g_" . shows (fromEnum i)
  showsPrec _ (DiffArg 1 i) =
    showString "d g_" . shows (fromEnum i)
  showsPrec d (DiffArg k i) = showParen (d > 9) $
    showString "d^" . shows k . showString " g_" . shows (fromEnum i)
  showsPrec d (DiffFun pows)
    | all (== 0) pows = showChar 'f'
    | otherwise =
      let ps = SV.unsized pows
      in showString "D("
        . V.foldr1 (\a b -> a . showString ", " . b) (V.map shows ps)
        . showString ") f"

evalTree
  :: (Floating a, KnownNat n, Eq a)
  => Tree n a
  -> (forall x. Floating x => Vec n x -> x)
  -> Vec n (Series a)
  -> a
evalTree (Mul l r) f vs = evalTree l f vs * evalTree r f vs
evalTree (Add l r) f vs = evalTree l f vs + evalTree r f vs
evalTree (DiffArg k i) f vs =
  constTerm
  $ foldr (.) id (replicate (fromIntegral k) formalDiff)
  $ vs SV.%!! i
evalTree (DiffFun pows) f vs =
  SV.head $ multDiff pows (SV.singleton . f) $
  SV.map constTerm vs
evalTree (K a) _ _ = a

instance (Num a, Eq a) => Num (Tree n a) where
  fromInteger = K . fromInteger
  K 0 + x = x
  x + K 0 = x
  x + y   = Add x y
  K 1 * x = x
  x * K 1 = x
  K 0 * _ = K 0
  _ * K 0 = K 0
  x * y = Mul x y
  negate = Mul $ K ( -1)
  abs = error "No Abs for Tree"
  signum = error "No signum for Tree"

diffTree
  :: forall n a. (KnownNat n, Eq a, Num a)
  => Tree n a -> Tree n a
diffTree (Mul l r) =
  diffTree l * r + l * diffTree r
diffTree (Add l r) = diffTree l + diffTree r
diffTree (DiffArg k i) = DiffArg (k + 1) i
diffTree K{} = K 0
diffTree (DiffFun pow) =
  sum
    [ DiffFun (pow & ix i +~ 1) * DiffArg 1 i
    | i <- enumOrdinal sing
    ]

injectCoeSer :: Num a => a -> Series a
injectCoeSer = Series . (: repeat 0)

instance (Floating a, Eq a) => Num (Series a) where
  fromInteger = Series . (: repeat 0) . fromInteger
  (+) = coerce $ zipWith ((+) @a)
  (-) = coerce $ zipWith ((+) @a)
  (*) = coerce $ convolve @a
  negate = coerce $ map $ negate @a
  abs = liftSmooth (abs . SV.head) . SV.singleton
  signum = liftSmooth (signum . SV.head) . SV.singleton

instance (Eq a, Floating a) => Fractional (Series a) where
  fromRational = injectCoeSer . fromRational
  recip = liftSmooth (recip . SV.head) . SV.singleton

liftUnSeries
  :: (Floating a, Eq a)
  => (forall x. Floating x => x -> x)
  -> Series a -> Series a
liftUnSeries f = liftSmooth (f . SV.head) . SV.singleton

liftBinSeries
  :: (Floating a, Eq a)
  => (forall x. Floating x => x -> x-> x)
  -> Series a -> Series a -> Series a
liftBinSeries f = \x y ->
  liftSmooth (\xs -> f (xs SV.%!! 0) (xs SV.%!! 1)) (x SV.:< y SV.:< SV.NilR)

instance (Eq a, Floating a) => Floating (Series a) where
  log = liftUnSeries log
  logBase = liftBinSeries logBase
  exp = liftUnSeries exp
  (**) = liftBinSeries (**)

  pi = injectCoeSer pi
  sin = liftUnSeries sin
  cos = liftUnSeries cos
  tan = liftUnSeries tan
  asin = liftUnSeries asin
  acos = liftUnSeries acos
  atan = liftUnSeries atan

  sinh = liftUnSeries sinh
  cosh = liftUnSeries cosh
  tanh = liftUnSeries tanh
  asinh = liftUnSeries asinh
  acosh = liftUnSeries acosh
  atanh = liftUnSeries atanh

-- | Shows only first 10  terms.
instance (Show a, Num a, Eq a) => Show (Series a) where
  showsPrec d (Series ts) =
    let (trms, rest) = splitAt 10 $ ts ^.. ifolded.withIndex
    in if null trms
    then showString "0"
    else showParen (d > 10) $
      foldr1 (\a b -> a . showString " + " . b)
      [ showsPrec 11 c . if p == 0 then id else showString " X^" . shows p
      | (p, c) <- trms
      ]
      . if null rest then id else showString " + ..."

cutoffUn :: forall a. Int -> Series a -> Series a
cutoffUn = coerce . take @a

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
