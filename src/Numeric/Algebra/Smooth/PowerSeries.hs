{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Numeric.Algebra.Smooth.PowerSeries where

import Algebra.Ring.Polynomial (IsPolynomial)
import qualified Algebra.Ring.Polynomial as Pol
import qualified AlgebraicPrelude as AP
import Control.Comonad.Cofree
import qualified Control.Comonad.Cofree as Cof
import Control.Lens
  ( FoldableWithIndex (ifoldMap, ifolded),
    FunctorWithIndex (imap),
    Ixed (ix),
    alaf,
    withIndex,
    (&),
    (+~),
    (^..),
  )
import Control.Monad (guard)
import Data.Coerce (coerce)
import Data.ListLike (ListLike)
import Data.MonoTraversable
import Data.Monoid (Product (..))
import Data.Semialign (alignWith)
import qualified Data.Sequence as Seq
import Data.Singletons.Prelude (Sing, SingI (sing))
import qualified Data.Sized.Builtin as SV
import Data.These
import Data.Type.Natural.Class.Arithmetic
  ( ZeroOrSucc (..),
    zeroOrSucc,
  )
import Data.Type.Natural.Class.Order
import Data.Type.Ordinal.Builtin (Ordinal, enumOrdinal)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import GHC.Conc (par)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat)
import qualified Numeric.AD as AD
import qualified Numeric.Algebra as NA
import Numeric.Algebra.Smooth.Classes
  ( SmoothRing (..),
    liftBinary,
    liftUnary,
  )
import Numeric.Algebra.Smooth.Types (UVec, Vec, convVec)
import Numeric.Natural (Natural)
import Proof.Propositional (withWitness)

-- | Unary formal power series, or Tower.
newtype Series k = Series {runSeries :: [k]}
  deriving (Generic)
  deriving
    ( NA.Additive
    , NA.Monoidal
    , NA.Group
    , NA.Abelian
    , NA.Rig
    , NA.Commutative
    , NA.Multiplicative
    , NA.Semiring
    , NA.Unital
    , NA.Ring
    , NA.LeftModule Natural
    , NA.RightModule Natural
    , NA.LeftModule Integer
    , NA.RightModule Integer
    )
    via AP.WrapNum (Series k)

convolve :: Num a => [a] -> [a] -> [a]
convolve = loop
  where
    loop ~(x : xs) ~(y : ys) =
      x * y :
      zipWith3
        (\a b c -> a `par` b `par` c `seq` (a + b + c))
        (map (x *) ys)
        (map (y *) xs)
        (0 : loop xs ys)
{-# INLINE convolve #-}

formalDiff ::
  Num a => Series a -> Series a
formalDiff =
  Series . tail . imap (\i c -> fromIntegral i * c) . runSeries

formalNDiff ::
  forall n a.
  (KnownNat n, Num a) =>
  UVec n Word ->
  PowerSeries n a ->
  PowerSeries n a
formalNDiff pows (Powers f) = Powers $ \pows' ->
  fromIntegral (alaf Product ofoldMap factorial pows)
    * f (SV.zipWithSame (+) pows pows')

factorial :: Word -> Word
factorial = product . enumFromTo 1

constTerm :: Series c -> c
constTerm = head . runSeries

nthDiffZero ::
  forall a n.
  (KnownNat n, Eq a, Floating a) =>
  Word ->
  (forall x. Floating x => Vec n x -> x) ->
  Vec n (Series a) ->
  a
nthDiffZero 0 f vs = f $ SV.map constTerm vs
nthDiffZero n f vs =
  evalTree
    ( foldr1 (.) (replicate (fromIntegral n) diffTree) $
        DiffFun (SV.replicate' 0)
    )
    f
    vs

instance
  (Floating a, Eq a) =>
  NA.LeftModule (AP.WrapFractional Double) (Series a)
  where
  (.*) (AP.WrapFractional a) = coerce $ map @a (realToFrac a *)

instance
  (Floating a, Eq a) =>
  NA.RightModule (AP.WrapFractional Double) (Series a)
  where
  Series xs *. AP.WrapFractional a = coerce $ map (* realToFrac a) xs

instance
  (KnownNat n, Floating a, Eq a) =>
  NA.LeftModule (AP.WrapFractional Double) (PowerSeries n a)
  where
  (.*) (AP.WrapFractional a) = coerce $ fmap @((->) (UVec n Word)) @a (realToFrac a *)

instance
  (KnownNat n, Floating a, Eq a) =>
  NA.RightModule (AP.WrapFractional Double) (PowerSeries n a)
  where
  Powers f *. AP.WrapFractional a = Powers $ \x -> f x * realToFrac a

instance (Floating a, Eq a) => SmoothRing (Series a) where
  liftSmooth f vs = Series $ go 0 1.0 (DiffFun $ SV.replicate' 0)
    where
      go !n !r !trm =
        (evalTree trm f vs * fromRational r) :
        go (n + 1) (r / (n + 1)) (diffTree trm)

diag ::
  ( Num a
  , G.Vector v a
  , KnownNat n
  , ListLike (v a) a
  ) =>
  SV.Ordinal n ->
  SV.Sized v n a
diag i = SV.generate sing $ \j -> if i == j then 1 else 0

data MTree m n a
  = Mul !(MTree m n a) !(MTree m n a)
  | Add !(MTree m n a) !(MTree m n a)
  | DiffArg !(UVec m Word) !(SV.Ordinal n)
  | DiffFun !(UVec n Word)
  | K !a
  deriving (Eq, Ord)

type Tree = MTree 1

instance (KnownNat n, Show a) => Show (Tree n a) where
  showsPrec d (K a) = showsPrec d a
  showsPrec d (Mul l r) =
    showParen (d > 11) $
      showsPrec 11 l . showString " * " . showsPrec 11 r
  showsPrec d (Add l r) =
    showParen (d > 10) $
      showsPrec 10 l . showString " + " . showsPrec 10 r
  showsPrec _ (DiffArg (SV.head -> 0) i) =
    showString "g_" . shows (fromEnum i)
  showsPrec _ (DiffArg (SV.head -> 1) i) =
    showString "d g_" . shows (fromEnum i)
  showsPrec d (DiffArg (SV.head -> k) i) =
    showParen (d > 9) $
      showString "d^" . shows k . showString " g_" . shows (fromEnum i)
  showsPrec _ (DiffFun pows)
    | oall (== 0) pows = showChar 'f'
    | otherwise =
      let ps = SV.unsized pows
       in showString "D("
            . V.foldr1 (\a b -> a . showString ", " . b) (V.map shows $ V.convert ps)
            . showString ") f"

instance
  {-# OVERLAPPABLE #-}
  ( KnownNat m
  , KnownNat n
  , Show a
  ) =>
  Show (MTree m n a)
  where
  showsPrec d (K a) = showsPrec d a
  showsPrec d (Mul l r) =
    showParen (d > 11) $
      showsPrec 11 l . showString " * " . showsPrec 11 r
  showsPrec d (Add l r) =
    showParen (d > 10) $
      showsPrec 10 l . showString " + " . showsPrec 10 r
  showsPrec d (DiffArg ds i)
    | oall (== 0) ds = showString "g_" . shows (fromEnum i)
    | otherwise =
      showParen (d > 9) $
        let pow =
              V.imapMaybe
                ( \j p -> do
                    guard $ p /= 0
                    pure $
                      showString "d_" . shows j
                        . showChar '^'
                        . shows p
                )
                $ V.convert $ SV.unsized ds
         in foldr1 (\a b -> a . showString " " . b) pow
              . showString " g_"
              . shows (fromEnum i)
  showsPrec _ (DiffFun pows)
    | oall (== 0) pows = showChar 'f'
    | otherwise =
      let ps = SV.unsized pows
       in showString "D("
            . V.foldr1 (\a b -> a . showString ", " . b) (V.map shows $ V.convert ps)
            . showString ") f"

evalTree ::
  (Floating a, KnownNat n, Eq a) =>
  Tree n a ->
  (forall x. Floating x => Vec n x -> x) ->
  Vec n (Series a) ->
  a
evalTree (Mul l r) f vs = evalTree l f vs * evalTree r f vs
evalTree (Add l r) f vs = evalTree l f vs + evalTree r f vs
evalTree (DiffArg (SV.head -> k) i) _ vs =
  constTerm $
    foldr ($) (vs SV.%!! i) (replicate (fromIntegral k) formalDiff)
evalTree (DiffFun pows) f vs =
  walkAlong pows $
    AD.grads f $
      SV.map constTerm vs
evalTree (K a) _ _ = a

constPTerm :: KnownNat n => PowerSeries n a -> a
constPTerm = ($ SV.replicate' 0) . getCoeff

evalMTree ::
  (KnownNat m, KnownNat n, Floating a, Eq a) =>
  MTree m n a ->
  (forall x. Floating x => Vec n x -> x) ->
  Vec n (PowerSeries m a) ->
  a
evalMTree (Mul l r) f vs = evalMTree l f vs * evalMTree r f vs
evalMTree (Add l r) f vs = evalMTree l f vs + evalMTree r f vs
evalMTree (DiffArg pow i) _ vs =
  constPTerm $
    formalNDiff pow $
      vs SV.%!! i
evalMTree (DiffFun pows) f vs =
  walkAlong pows $
    AD.grads f $
      SV.map constPTerm vs
evalMTree (K a) _ _ = a

instance (Num a, Eq a) => Num (MTree m n a) where
  fromInteger = K . fromInteger
  K 0 + x = x
  x + K 0 = x
  x + y = Add x y
  K 1 * x = x
  x * K 1 = x
  K 0 * _ = K 0
  _ * K 0 = K 0
  x * y = Mul x y
  negate = Mul $ K (-1)
  abs = error "No Abs for Tree"
  signum = error "No signum for Tree"

diffTree ::
  (KnownNat n, Eq a, Num a) =>
  Tree n a ->
  Tree n a
diffTree = diffMTree 0

diffMTree ::
  forall m n a.
  (KnownNat m, KnownNat n, Eq a, Num a) =>
  Ordinal m ->
  MTree m n a ->
  MTree m n a
diffMTree o (Mul l r) =
  diffMTree o l * r + l * diffMTree o r
diffMTree o (Add l r) = diffMTree o l + diffMTree o r
diffMTree o (DiffArg k i) = DiffArg (k & ix o +~ 1) i
diffMTree _ K {} = K 0
diffMTree o (DiffFun pow) =
  sum
    [ DiffFun (pow & ix i +~ 1) * DiffArg (diag o) i
    | i <- enumOrdinal @n sing
    ]

injectCoeSer :: Num a => a -> Series a
injectCoeSer = Series . (: repeat 0)

injectCoePS :: Num k => k -> PowerSeries n k
injectCoePS a = Powers $ \x ->
  if oall (== 0) x
    then a
    else 0

instance (Floating a, Eq a) => Num (Series a) where
  fromInteger = Series . (: []) . fromInteger
  (+) = coerce $
    alignWith @[] @a $ \case
      These a b -> a + b
      This a -> a
      That a -> a
  (-) = coerce $
    alignWith @[] @a $
      \case These a b -> a - b; This a -> a; That a -> negate a
  (*) = coerce $ convolve @a
  negate = coerce $ map $ negate @a
  abs = liftSmooth (abs . SV.head) . SV.singleton
  signum = liftSmooth (signum . SV.head) . SV.singleton

instance (Eq a, Floating a) => Fractional (Series a) where
  fromRational = injectCoeSer . fromRational
  recip = liftSmooth (recip . SV.head) . SV.singleton

instance (Eq a, Floating a) => Floating (Series a) where
  log = liftUnary log
  logBase = liftBinary logBase
  exp = liftUnary exp
  (**) = liftBinary (**)

  pi = injectCoeSer pi
  sin = liftUnary sin
  cos = liftUnary cos
  tan = liftUnary tan
  asin = liftUnary asin
  acos = liftUnary acos
  atan = liftUnary atan

  sinh = liftUnary sinh
  cosh = liftUnary cosh
  tanh = liftUnary tanh
  asinh = liftUnary asinh
  acosh = liftUnary acosh
  atanh = liftUnary atanh

-- | Shows only first 10  terms.
instance (Show a, Num a, Eq a) => Show (Series a) where
  showsPrec d (Series ts) =
    let (trms, rest) = splitAt 10 $ ts ^.. ifolded . withIndex
     in if null trms
          then showString "0"
          else
            showParen (d > 10) $
              foldr1
                (\a b -> a . showString " + " . b)
                [ showsPrec 11 c . if p == 0 then id else showString " X^" . shows p
                | (p, c) <- trms
                ]
                . if null rest then id else showString " + ..."

cutoffUn :: forall a. Int -> Series a -> Series a
cutoffUn = coerce . take @a

-- TODO: Recursive representation based on complete binary tree
-- or something similar to Sparse from @ad@.
newtype PowerSeries n k = Powers {getCoeff :: UVec n Word -> k}
  deriving (Functor)
  deriving
    ( NA.Additive
    , NA.Monoidal
    , NA.Group
    , NA.Abelian
    , NA.Rig
    , NA.Commutative
    , NA.Multiplicative
    , NA.Semiring
    , NA.Unital
    , NA.Ring
    , NA.LeftModule Natural
    , NA.RightModule Natural
    , NA.LeftModule Integer
    , NA.RightModule Integer
    )
    via AP.WrapNum (PowerSeries n k)

monomsOfDeg ::
  forall n. KnownNat n => Word -> [UVec n Word]
monomsOfDeg 0 = [SV.replicate' 0]
monomsOfDeg n =
  case zeroOrSucc (sing @n) of
    IsZero -> []
    IsSucc (_ :: Sing m) ->
      concat
        [ map (k SV.<|) $ monomsOfDeg @m (n - k)
        | k <- [0 .. n]
        ]

cutoff :: KnownNat n => Word -> PowerSeries n k -> [(UVec n Word, k)]
cutoff n = takeWhile ((<= n) . osum . fst) . terms

cutoffMult :: KnownNat n => UVec n Word -> PowerSeries n k -> [(UVec n Word, k)]
cutoffMult mdeg (Powers f) =
  [ (m, f m)
  | m <- omapM (enumFromTo 0) mdeg
  ]

terms :: KnownNat n => PowerSeries n k -> [(UVec n Word, k)]
terms (Powers f) =
  [ (m, f m)
  | k <- [0 ..]
  , m <- monomsOfDeg k
  ]

instance (KnownNat n, Floating a, Eq a) => Num (PowerSeries n a) where
  fromInteger x = Powers $ \a ->
    if oall (== 0) a
      then fromInteger x
      else 0
  Powers f + Powers g = Powers $ \a -> f a + g a
  Powers f - Powers g = Powers $ \a -> f a - g a
  negate (Powers f) = Powers $ negate . f
  Powers f * Powers g = Powers $ \a ->
    sum
      [ f v * g (SV.zipWithSame (-) a v)
      | v <- otraverse (enumFromTo 0) a
      ]
  abs = liftSmooth (abs . SV.head) . SV.singleton
  signum = liftSmooth (signum . SV.head) . SV.singleton

instance
  (KnownNat n, Floating a, Eq a) =>
  Fractional (PowerSeries n a)
  where
  recip = liftUnary recip
  (/) = liftBinary (/)
  fromRational x = Powers $ \a ->
    if oall (== 0) a
      then fromRational x
      else 0

instance
  (KnownNat n, Floating a, Eq a) =>
  SmoothRing (PowerSeries n a)
  where
  liftSmooth f vs = Powers $ \degs ->
    evalMTree
      ( foldr
          ($)
          (DiffFun $ SV.replicate' 0)
          (fmap diffMTree (ifoldMap (flip $ Seq.replicate . fromIntegral) $ convertSized degs))
      )
      f
      vs
      / fromIntegral (alaf Product ofoldMap factorial degs)

convertSized :: (U.Unbox a, KnownNat n) => UVec n a -> Vec n a
convertSized = SV.unsafeToSized' . G.convert . SV.unsized

instance
  (Eq a, Floating a, KnownNat n) =>
  Floating (PowerSeries n a)
  where
  log = liftUnary log
  logBase = liftBinary logBase
  exp = liftUnary exp
  (**) = liftBinary (**)

  pi = injectCoePS pi
  sin = liftUnary sin
  cos = liftUnary cos
  tan = liftUnary tan
  asin = liftUnary asin
  acos = liftUnary acos
  atan = liftUnary atan

  sinh = liftUnary sinh
  cosh = liftUnary cosh
  tanh = liftUnary tanh
  asinh = liftUnary asinh
  acosh = liftUnary acosh
  atanh = liftUnary atanh

injPoly ::
  IsPolynomial r => r -> PowerSeries (Pol.Arity r) (Pol.Coefficient r)
injPoly p = Powers $ \a ->
  Pol.coeff' (convVec $ SV.map fromIntegral a) p

liftPSToPolysViaAD ::
  forall n k a.
  (KnownNat n, KnownNat k, Floating a, Real a) =>
  (forall x. Floating x => Vec k x -> x) ->
  Vec k (Pol.Polynomial a n) ->
  PowerSeries n a
liftPSToPolysViaAD f pols = Powers $ \mon ->
  walkAlong mon table / fromIntegral (alaf Product ofoldMap factorial mon)
  where
    table :: Cofree (SV.Sized V.Vector n) a
    table =
      AD.grads
        ( \xs ->
            f $
              SV.map
                ( AP.unwrapFractional
                    . Pol.eval (SV.map AP.WrapFractional xs)
                    . Pol.mapCoeff (AP.WrapFractional . realToFrac)
                )
                pols
        )
        $ SV.replicate' 0

walkAlong ::
  forall n a.
  (KnownNat n) =>
  UVec n Word ->
  Cofree (SV.Sized V.Vector n) a ->
  a
walkAlong SV.NilR (a Cof.:< SV.NilR) = a
walkAlong (0 SV.:< (rest :: UVec m Word)) (a :< deep) =
  withWitness
    (lneqZero $ sing @m)
    $ walkAlong
      rest
      (a Cof.:< SV.map (hoistCofree SV.tail) (SV.tail deep))
walkAlong (n SV.:< rest) (_ :< (diffed SV.:< _)) =
  walkAlong (n - 1 SV.:< rest) diffed
walkAlong _ _ = error "could not happen!"