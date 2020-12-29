{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Numeric.Algebra.Smooth.Dual where

import Algebra.Normed
import qualified AlgebraicPrelude as AP
import Control.Lens
import Data.Bits
import Data.Coerce
import Data.Foldable (fold)
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.MonoTraversable (osum)
import Data.Monoid (Sum (..))
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Singletons.Prelude
  ( Sing,
    sing,
    withSingI,
    type (<),
  )
import Data.Singletons.TypeLits
import Data.Sized.Builtin (Sized)
import qualified Data.Sized.Builtin as SV
import Data.Tuple
import qualified Data.Type.Natural as PN
import Data.Type.Natural.Builtin (ToPeano, sToPeano)
import Data.Type.Natural.Class.Arithmetic hiding (PNum (..))
import Data.Type.Natural.Class.Order hiding (type (<=))
import Data.Type.Ordinal.Builtin
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.Void
import GHC.Exts
import GHC.Generics
import GHC.TypeNats
import Numeric.Algebra (Additive, Algebra, (.*))
import qualified Numeric.Algebra as NA
import Numeric.Algebra.Smooth.Classes
import Numeric.Algebra.Smooth.Types
import Numeric.Natural
import Proof.Propositional
import Unsafe.Coerce

epsilon :: Num a => Dual a -> a
epsilon = \case
  Konst {} -> 0
  Dual {..} -> _epsilon

{- | A ring \(\mathbb{R}[\epsilon] = \mathbb{R}[X]/X^2\) of dual numbers.
 Corresponding to the usual forward-mode automatic differentiation.
-}
data Dual a
  = Dual {value :: !a, _epsilon :: a}
  | Konst {value :: !a}
  deriving (Functor, Foldable, Traversable, Eq, Generic)
  deriving
    ( Additive
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
    via AP.WrapNum (Dual a)

instance Fractional a => NA.RightModule (AP.WrapFractional Double) (Dual a) where
  Dual a da *. AP.WrapFractional x = Dual (a * realToFrac x) (da * realToFrac x)

instance Fractional a => NA.LeftModule (AP.WrapFractional Double) (Dual a) where
  AP.WrapFractional x .* Dual a da = Dual (realToFrac x * a) (realToFrac x * da)

instance (Show a, Num a, Eq a) => Show (Dual a) where
  showsPrec d (Konst n) = showsPrec d n
  showsPrec d (Dual a 0) = showsPrec d a
  showsPrec d (Dual 0 e) =
    showParen (d > 10) $
      showsPrec 11 e . showString " ε"
  showsPrec d (Dual a b) =
    showParen (d > 10) $
      shows a . showString " + " . showsPrec 11 b . showString " ε"

instance Floating a => SmoothRing (Dual a) where
  liftSmooth = id

liftDual ::
  (KnownNat n, Floating a) =>
  (forall a. Floating a => Vec n a -> a) ->
  Vec n (Dual a) ->
  Dual a
liftDual f (ds :: Vec n (Dual a)) =
  let reals = value <$> ds
      duals = epsilon <$> ds
      coes =
        imap
          ( \i bi ->
              bi
                * epsilon
                  ( f $
                      SV.unsafeFromList'
                        [ Dual ai (if i == k then 1 else 0)
                        | ai <- SV.toList reals
                        | k <- [0 ..]
                        ]
                  )
          )
          duals
      fa = f reals
   in Dual fa $ sum coes

data DualsumBasis = R | D
  deriving (Read, Show, Eq, Ord)

instance Algebra (AP.WrapFractional Double) DualsumBasis where
  mult f = f'
    where
      fr = f R R
      fd = f R D + f D R
      f' R = fr
      f' D = fd

instance Num a => Num (Dual a) where
  fromInteger = Konst . fromInteger
  Konst a + b = b {value = a + value b}
  a + Konst b = a {value = value a + b}
  Dual a da + Dual b db = Dual (a + b) (da + db)
  Konst a - Konst b = Konst (a - b)
  Konst a - Dual b db = Dual (a - b) (- db)
  Dual a da - Konst b = Dual (a - b) da
  Dual a da - Dual b db = Dual (a - b) (da - db)
  negate (Konst a) = Konst $ negate a
  negate (Dual a da) = Dual (negate a) (negate da)
  Konst a * Konst b = Konst (a * b)
  Konst a * Dual b db = Dual (a * b) (a * db)
  Dual a da * Konst b = Dual (a * b) (da * b)
  Dual a da * Dual b db = Dual (a * b) (a * db + da * b)
  abs (Konst a) = Konst (abs a)
  abs (Dual a da) = Dual (abs a) (signum a)
  signum (Konst a) = Konst $ signum a
  signum (Dual a da) = Dual (signum a) 0

instance Fractional a => Fractional (Dual a) where
  fromRational = Konst . fromRational
  Konst x / Konst y = Konst (x / y)
  Konst x / Dual y dy = Dual (x / y) (- x * dy / (y * y))
  Dual x dx / Konst y = Dual (x / y) (dx / y)
  Dual x dx / Dual y dy = Dual (x / y) (dx / y - x * dy / (y * y))
  recip = unDual recip (\x -> - recip (x * x))

unDual :: (Num a) => (a -> a) -> (a -> a) -> Dual a -> Dual a
{-# INLINE unDual #-}
unDual f df = \case
  Dual a da ->
    Dual (f a) (da * df a)
  Konst a -> Konst (f a)

instance (Floating a) => Floating (Dual a) where
  pi = Dual pi 0
  exp = unDual exp exp
  sin = unDual sin cos
  cos = unDual cos (negate . sin)
  tan = unDual tan (recip . cos . (^^ 2))
  log = unDual log recip
  asin = unDual asin (recip . sqrt . (1 -) . (^^ 2))
  acos = unDual acos (\a -> 1 / (- sqrt (1 - a ^^ 2)))
  atan = unDual atan (\a -> 1 / (a ^ 2 + 1))
  sinh = unDual sinh cosh
  cosh = unDual cosh sinh
  tanh = unDual tanh (\a -> 1 / cosh a ^^ 2)
  asinh = unDual asinh (\a -> recip $ sqrt (1 + a ^^ 2))
  acosh = unDual acosh (\a -> recip $ sqrt (a ^^ 2 - 1))
  atanh = unDual atanh (\a -> recip (1 - a ^^ 2))

monomIndices :: KnownNat n => Vec n Bool -> V.Vector Int
monomIndices =
  V.map fst . V.filter snd . V.indexed . SV.unsized

nthD :: (Num a, KnownNat n) => Ordinal n -> Duals n a
nthD (OLt (sn :: Sing k)) = withKnownNat sn $ dn @k

withPows ::
  forall n m a r.
  (KnownNat n, KnownNat m, Eq a, Floating a) =>
  (forall k. KnownNat k => UVec n Word -> Vec m (Duals k a) -> r) ->
  UVec n Word ->
  (forall x. (Eq x, Floating x) => Vec n x -> Vec m x) ->
  Vec n a ->
  r
withPows k deg f xs = case someNatVal (fromIntegral $ osum deg) of
  SomeNat (_ :: Proxy k) ->
    withKnownNat (sing @k) $
      let ords = sliced deg $ map nthD $ enumOrdinal (sing @k)
          trms = SV.zipWithSame (\a b -> fromCoeff a + sum b) xs ords
       in k deg $ f trms
{-# INLINE withPows #-}

multDiff ::
  (KnownNat n, KnownNat m, Eq a, Floating a) =>
  UVec n Word ->
  (forall x. Floating x => Vec n x -> Vec m x) ->
  Vec n a ->
  Vec m a
multDiff =
  withPows $
    const $
      SV.map
        (V.last . SV.unsized . runDuals)

{- | @'multDiffUpTo' ds f u@ retruns all partial differential
coefficients by \(\alpha \leq w\).

With Kock-Lawvere axiom of SIA, we have the following identity:

  \[
    f(x + d_1 + \dots + d_k) = \sum_{0 \leq i \leq k} f^{(i)}(x) \sigma^i_n(d_1, \dots, d_k),
  \]

where, \(d_i \in D\) and \(\sigma^k_n\) stands for the \(n\)-variate
elementary symmetric expression of degree \(k\).
This formula can be regarded as an infinitesimal version of Taylor expansion, because we have \(\sigma^k_n(d_1, \dots, d_n) = \frac{(d_1 + \dots + d_n)^k}{k!} \) for any \(d_i \in D\).

This extends to the multivariate case as well:

  \[
    \begin{aligned}
    &f(x_1 + d_{1,1} + \dots + d_{1,k_1}, \dots, x_m + d_{m,1} + \dots + d_{m,k_m})
    \\
    = &
      \sum_{
        \substack{\alpha = (\alpha_1, \dots, \alpha_m) \in \mathbb{N}^m\\
        0 \leq \alpha_i \leq k_i
        }}
        \mathop{D^{\alpha}}(f)(x_1, \dots, x_m) \cdot \sigma^{\alpha_1}_{k_1}(d_{1,1}, \dots, d_{1,k_1}) \dots \sigma^{\alpha_m}_{k_m}(d_{m,1}, \dots, d_{m,k_m}).
    \end{aligned}
  \]

Utilising these indentities, one can compute all derivatives upto degree \(\alpha\) simultaneously.

cf. 'multDiffUpTo''
-}
multDiffUpTo ::
  forall n m a.
  (KnownNat n, KnownNat m, Eq a, Floating a) =>
  UVec n Word ->
  (forall x. (Eq x, Floating x) => Vec n x -> Vec m x) ->
  Vec n a ->
  M.Map (Vec n Word) (Vec m a)
multDiffUpTo = withPows $ \pows (ds :: Vec m (Duals k a)) ->
  let vars =
        traverse (map Set.fromList . inits) $
          sliced pows $
            enumOrdinal @k sing
   in M.fromList
        [ ( SV.map (fromIntegral . Set.size) ps
          , SV.map ((SV.%!! toMonomialIdx (fold ps)) . runDuals) ds
          )
        | ps <- vars
        ]

-- | Unary variant of 'multDiffUpTo'
diffUpTo ::
  forall a.
  (Eq a, Floating a) =>
  Word ->
  (forall x. Floating x => x -> x) ->
  a ->
  M.Map Word a
diffUpTo n f x =
  M.map SV.head $
    M.mapKeysMonotonic SV.head $
      multDiffUpTo @1 @1
        (SV.singleton n)
        (\(a SV.:< SV.NilL) -> SV.singleton $ f a)
        (SV.singleton x)

toMonomialIdx ::
  forall n.
  KnownNat n =>
  Set (Ordinal n) ->
  Ordinal (2 ^ n)
toMonomialIdx ods =
  let n = fromIntegral $ natVal' @n proxy#
   in toEnum $ alaf Sum foldMap (\i -> 2 ^ (n - fromEnum i - 1)) ods

instance (Floating a, KnownNat n) => SmoothRing (Duals n a) where
  liftSmooth = id

sliced :: KnownNat n => UVec n Word -> [a] -> Vec n [a]
sliced = loop
  where
    loop :: KnownNat k => UVec k Word -> [a] -> Vec k [a]
    loop SV.NilR xs = SV.empty
    loop (n SV.:< ns) xs =
      let (lf, rest) = splitAt (fromIntegral n) xs
       in lf SV.:< loop ns rest

instance
  (KnownNat n, Fractional a) =>
  NA.RightModule (AP.WrapFractional Double) (Duals n a)
  where
  a *. AP.WrapFractional x = a * realToFrac x

instance
  (KnownNat n, Fractional a) =>
  NA.LeftModule (AP.WrapFractional Double) (Duals n a)
  where
  AP.WrapFractional x .* a =
    realToFrac x * a

{- | \(n\)-ary product of 'Dual numbers,
   which does not have mutual relation between
   each distinct infinitesimals.
-}
newtype Duals n a = Duals {runDuals :: Vec (2 ^ n) a}
  deriving (Foldable, Functor, Eq)
  deriving
    ( Additive
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
    via AP.WrapNum (Duals n a)

halve :: forall n a. KnownNat n => Vec (2 * n) a -> (Vec n a, Vec n a)
halve xs =
  let (ls, rs) = V.splitAt (fromIntegral $ natVal' @n proxy#) $ SV.unsized xs
   in (SV.unsafeToSized' ls, SV.unsafeToSized' rs)

liftUn ::
  forall c n a.
  ( KnownNat n
  , forall k x. (KnownNat k, c x, (k < n) ~ 'True) => c (Duals k x)
  , forall x. c x => c (Dual x)
  , c a
  ) =>
  (forall x. c x => x -> x) ->
  Duals n a ->
  Duals n a
liftUn f (Duals xs) = case sing @n of
  Zero -> Duals $ SV.singleton $ f $ SV.head xs
  Succ (n :: Sing k) ->
    let (x, dx) = halve xs
        Dual (Duals x') (Duals dx') = f $ Dual (Duals @k x) (Duals @k dx)
     in Duals $ x' SV.++ dx'

liftBin ::
  forall c n a.
  ( KnownNat n
  , forall k x. (KnownNat k, c x, (k < n) ~ 'True) => c (Duals k x)
  , forall x. c x => c (Dual x)
  , c a
  ) =>
  (forall x. c x => x -> x -> x) ->
  Duals n a ->
  Duals n a ->
  Duals n a
liftBin f (Duals xs) (Duals ys) = case sing @n of
  Zero -> Duals $ SV.singleton $ f (SV.head xs) (SV.head ys)
  Succ (n :: Sing k) ->
    let (x, dx) = halve xs
        (y, dy) = halve ys
        Dual (Duals x') (Duals dx') =
          f (Dual (Duals @k x) (Duals @k dx)) (Dual (Duals @k y) (Duals @k dy))
     in Duals $ x' SV.++ dx'

fromCoeff ::
  forall n a. (KnownNat n, Num a) => a -> Duals n a
fromCoeff = Duals . (SV.:< SV.replicate (sing @(2 ^ n - 1)) 0)

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

components ::
  forall n a.
  (Eq a, Num a, KnownNat n) =>
  Duals n a ->
  M.Map (Vec n Bool) a
components (Duals xs) =
  case sing @n of
    Zero ->
      let c = SV.head xs
       in if c == 0 then M.empty else M.singleton SV.empty c
    Succ (l :: Sing l) ->
      let (s, ds) = halve xs
       in M.mapKeys (False SV.:<) (components $ Duals s)
            `M.union` M.mapKeys (True SV.:<) (components $ Duals ds)
{-# INLINE components #-}

instance (KnownNat n, Num a, Eq a, Show a) => Show (Duals n a) where
  showsPrec d dn =
    let terms = M.toList $ M.mapKeys monomIndices $ components dn
     in if null terms
          then showString "0"
          else
            foldr1
              (\a b -> a . showString " + " . b)
              [ if null trm
                then shows c
                else
                  showsPrec 11 c . showChar ' '
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
   in Duals $
        SV.unsafeToSized' $
          V.generate (2 ^ n) $ \i ->
            if i == l then 1 else 0

halveDs ::
  KnownNat n => Duals (n + 1) a -> Dual (Duals n a)
halveDs =
  uncurry Dual . (both %~ Duals) . halve . runDuals

instance (Normed a, Floating a) => Normed (Dual a) where
  type Norm (Dual a) = Norm a
  norm (Dual a da) = norm $ sqrt $ a ^ 2 + da ^ 2
  liftNorm n = Dual (liftNorm n) 0

instance (Normed a, Floating a, KnownNat n) => Normed (Duals n a) where
  type Norm (Duals n a) = Norm a
  norm (Duals ds) = norm $ sqrt $ sum $ SV.map (^ 2) ds
  liftNorm = fromCoeff . liftNorm
