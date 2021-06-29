{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Numeric.Algebra.Smooth.Weil
  ( Weil (Weil),
    realPart,
    diffUpTo,
    weilToVector,
    WeilSettings,
    type (|*|),
    D1,
    D2,
    Cubic,
    DOrder,
    di,
    ei,
    basisWeil,
    toWeil,
    isWeil,
    injCoeWeil,
    reifyWeil,
    withWeil,
    weilToPoly,
    polyToWeil,

    -- * Various lifting functions
    liftSmoothSeries,
    liftSmoothSeriesAD,
    liftSmoothSuccinctTower,
  )
where

import Algebra.Algorithms.Groebner.Signature.Rules ()
import Algebra.Algorithms.ZeroDim (univPoly, vectorRep)
import Algebra.Ring.Ideal
  ( Ideal,
    toIdeal,
  )
import Algebra.Ring.Polynomial
import Algebra.Ring.Polynomial.Quotient
  ( modIdeal',
    quotRepr,
    reifyQuotient,
    standardMonomials',
  )
import Algebra.Scalar
import AlgebraicPrelude
import Control.DeepSeq
import Control.Lens
  ( alaf,
    ifoldMapBy,
    itoList,
    re,
    (^.),
  )
import Data.Coerce (coerce)
import qualified Data.Foldable as F
import qualified Data.HashMap.Lazy as LHM
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.MonoTraversable (MonoFoldable (ofoldMap), oany, otraverse)
import Data.Monoid (Product (Product))
import Data.Proxy (Proxy (..))
import qualified Data.Ratio as R
import Data.Reflection
  ( Reifies (..),
    reify,
  )
import Data.Sized
  ( pattern Nil,
    pattern (:<),
  )
import qualified Data.Sized as SV
import Data.Type.Natural
import Data.Type.Ordinal
import qualified Data.Vector as V
import GHC.Exts (proxy#)
import Math.NumberTheory.Factorial.Swing.Recursion (factorial)
import qualified Numeric.Algebra as NA
import Numeric.Algebra.Smooth.Classes
  ( SmoothRing (..),
    liftBinary,
    liftUnary,
  )
import Numeric.Algebra.Smooth.PowerSeries
  ( PowerSeries (Powers),
    cutoffMult,
    diag,
    injPoly,
    liftPSToPolysViaAD,
  )
import qualified Numeric.Algebra.Smooth.PowerSeries.SuccinctTower as Tower
import Numeric.Algebra.Smooth.Types
  ( UVec,
    Vec,
    convVec,
  )
import qualified Prelude as P

{- | Weil algebra.

Weil algebra \(W\) is a \(R\)-algebra together with a unique maximal ideal \(\mathfrak{M}\), which is nipotent and \(W = \mathbb{R} \oplus \mathfrak{M}\) holds.

There are some good characterisation of Weil algebra; the following are equivalent:

  1. \(W\) is a Weil algebra,
  2. \(W\) is isomorphic to a quotient \(\mathbb{R}[X_1, \dots, X_n]/I\) of polynomial ring, and there exists \(k\) such that \(X_1^{k_1} \dots X_n^{k_n} \in I\) for all \(k_1 + \dots + k_n = k\),
  3. \(W\) is isomoprhic to a quotient \(\mathbb{R}[\![X_1, \dots, X_n]\!]/I\) of a ring of formal power series, such that \(I \supseteq (X_1, \dots, X_n)^k\) for some \(k\).

Since \(\mathbb{R}[\![\mathbf{X}]\!]\) has a \(C^\infty\)-ring structure (via Taylor expansion at zero), and any ring-theoretic ideal \(I\) on \(\mathbb{R}[\![\mathbf{X}]\!]\) induces a congruence of \(C^\infty\)-ring, it followes that any Weil algebra has \(C^\infty\)-structure; i.e. is an instances of @'SmoothRing'@.

In particular, each equivalence class \(d_i = X_i + I\) of variables can be regarded as generalised nilpotent infinitesimals.
In this sense, the notion of Weil algebra can be thought as a formalisation of "real line with infinitesimals".
-}
newtype Weil s r = Weil_ (Vector r)
  deriving newtype (P.Functor, NFData, Eq)

pattern Weil ::
  forall s n m r.
  (Reifies s (WeilSettings n m), KnownNat n, KnownNat m) =>
  (Reifies s (WeilSettings n m), KnownNat n, KnownNat m) =>
  Vec n r ->
  Weil s r
pattern Weil v <-
  Weil_ (SV.unsafeToSized' @_ @n -> v)
  where
    Weil v = Weil_ (SV.unsized @_ @n v)

{-# COMPLETE Weil #-}

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Additive (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Monoidal (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Group (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Abelian (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Rig (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Commutative (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Multiplicative (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Semiring (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Unital (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Ring (Weil s r)

deriving via
  WrapFractional (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    Division (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    LeftModule Natural (Weil s r)

instance
  ( Eq r
  , Semiring r
  , KnownNat m
  , KnownNat n
  , Eq r
  , Floating r
  , Reifies s (WeilSettings n m)
  ) =>
  LeftModule r (Weil s r)
  where
  (.*) = coerce $ V.map @r . (NA.*)

instance
  ( Eq r
  , Semiring r
  , KnownNat m
  , KnownNat n
  , Eq r
  , Floating r
  , Reifies s (WeilSettings n m)
  ) =>
  RightModule r (Weil s r)
  where
  (*.) = flip $ coerce $ V.map @r . flip (NA.*)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    RightModule Natural (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    LeftModule Integer (Weil s r)

deriving via
  WrapNum (Weil s r)
  instance
    (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
    RightModule Integer (Weil s r)

fromRational' ::
  Fractional r => Rational -> WrapFractional r
fromRational' = (fromRational .) . (R.%) <$> numerator <*> denominator

injCoeWeil ::
  (KnownNat n, KnownNat m, Num r, Reifies s (WeilSettings n m)) =>
  r ->
  Weil s r
injCoeWeil a =
  Weil $
    SV.generate
      sNat
      (\i -> if i == 0 then a else 0)

instance
  (KnownNat n, KnownNat m, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
  Num (Weil s r)
  where
  (+) = coerce $ V.zipWith ((P.+) @r)
  negate = coerce $ V.map (P.negate @r)
  (-) = coerce $ V.zipWith ((P.-) @r)
  fromInteger = injCoeWeil . fromInteger
  Weil f * Weil g =
    case reflect $ Proxy @s of
      WeilSettings {..} ->
        let a =
              sum
                [ injectCoeff (WrapFractional $ c P.* d)
                  * mapCoeff
                    fromRational'
                    (HM.lookupDefault 0 (min i j, max i j) table)
                | (fromEnum -> i, c) <- itoList f
                , (fromEnum -> j, d) <- itoList g
                ]
         in polyToWeil a

  abs = liftUnary abs
  signum = liftUnary signum

instance
  ( KnownNat m
  , KnownNat n
  , Eq r
  , Eq r
  , Floating r
  , Reifies s (WeilSettings n m)
  ) =>
  Fractional (Weil s r)
  where
  fromRational = injCoeWeil . P.fromRational
  recip = liftUnary P.recip
  (/) = liftBinary (P./)

instance
  ( KnownNat m
  , KnownNat n
  , Eq r
  , Eq r
  , Floating r
  , Reifies s (WeilSettings n m)
  ) =>
  Floating (Weil s r)
  where
  log = liftUnary log
  logBase = liftBinary logBase
  exp = liftUnary exp
  (**) = liftBinary (**)

  pi = injCoeWeil pi
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

liftSmoothSeries ::
  ( Reifies s (WeilSettings n m)
  , KnownNat k
  , Eq r
  , Floating r
  , Eq r
  , KnownNat n
  , KnownNat m
  ) =>
  (forall x. (Floating x) => Vec k x -> x) ->
  Vec k (Weil s r) ->
  Weil s r
liftSmoothSeries f (vs :: Vec k (Weil s r)) =
  let vs' =
        SV.map
          ( coerce @_ @(PowerSeries _ r)
              . injPoly
              . weilToPoly
          )
          vs
   in toWeil $ liftSmooth f vs'

liftSmoothSeriesAD ::
  ( Reifies s (WeilSettings n m)
  , KnownNat k
  , Eq r
  , Floating r
  , KnownNat n
  , KnownNat m
  ) =>
  (forall x. (Floating x) => Vec k x -> x) ->
  Vec k (Weil s r) ->
  Weil s r
liftSmoothSeriesAD f (vs :: Vec k (Weil s r)) =
  let vs' =
        SV.map
          ( coerce . weilToPoly
          )
          vs
   in toWeil $ liftPSToPolysViaAD f vs'

liftSmoothSuccinctTower ::
  ( Reifies s (WeilSettings n m)
  , KnownNat k
  , Floating r
  , Eq r
  , KnownNat n
  , KnownNat m
  ) =>
  (forall x. (Floating x) => Vec k x -> x) ->
  Vec k (Weil s r) ->
  Weil s r
liftSmoothSuccinctTower f (vs :: Reifies s (WeilSettings n m) => Vec k (Weil s r)) =
  let vs' :: Vec k (Tower.SSeries m r)
      vs' =
        SV.map
          ( Tower.towerFromMap . coerce
              . Map.mapKeysMonotonic (SV.map fromIntegral)
              . Map.mapWithKey
                ((.*) . alaf Product ofoldMap (factorial . fromIntegral))
              . terms'
              . weilToPoly
          )
          vs
      WeilSettings {..} = reflect $ Proxy @s
   in polyToWeil $
        polynomial' $
          Map.mapWithKey (flip (P./) . fromInteger . alaf Product ofoldMap (factorial . fromIntegral)) $
            coerce @_ @(Map (UVec m Int) (WrapFractional r)) $
              Map.mapKeysMonotonic (SV.map fromIntegral) $
                Tower.cutoff nonZeroVarMaxPowers $ f vs'

instance
  ( KnownNat m
  , KnownNat n
  , Eq r
  , Floating r
  , Reifies s (WeilSettings n m)
  ) =>
  SmoothRing (Weil s r)
  where
  liftSmooth = liftSmoothSeriesAD

polyToWeil ::
  forall s r n m.
  (KnownNat m, Eq r, KnownNat n, Reifies s (WeilSettings m n), Num r, Fractional r) =>
  Polynomial (WrapFractional r) n ->
  Weil s r
polyToWeil a =
  case reflect @s Proxy of
    WeilSettings {..} ->
      let calcProj ::
            Monomial n ->
            WrapFractional r ->
            Vec m r
          calcProj mon coe =
            maybe
              (SV.replicate' 0)
              (SV.map (unwrapFractional . (* coe) . fromRational'))
              $ HM.lookup
                (SV.map fromIntegral mon)
                weilMonomDic
          intUb = SV.map fromIntegral nonZeroVarMaxPowers
          (less, eq, _) =
            Map.splitLookup intUb $
              terms' a
          coes =
            maybe
              id
              (SV.zipWithSame (P.+) . calcProj intUb)
              eq
              $ ifoldMapBy
                (SV.zipWithSame (P.+))
                (SV.replicate' 0)
                calcProj
                less
       in Weil coes

weilToPoly ::
  forall s r n m.
  (KnownNat m, Eq r, KnownNat n, Reifies s (WeilSettings m n), Fractional r) =>
  Weil s r ->
  Polynomial (WrapFractional r) n
weilToPoly (Weil cs) =
  case reflect @s Proxy of
    WeilSettings {..} ->
      sum $
        SV.zipWithSame
          ( \m c ->
              polynomial' @(Polynomial (WrapFractional r) _) $
                Map.fromList
                  [
                    ( SV.map fromIntegral m
                    , WrapFractional c
                    )
                  ]
          )
          weilBasis
          cs

{- | @i@ th base of Weil algebra.

   @ei 0@ is just the real part.
-}
ei ::
  (Num r, Reifies s (WeilSettings m n), KnownNat n, KnownNat m) =>
  Ordinal m ->
  Weil s r
ei ord = Weil $ diag ord

-- | The list of the basis of Weil algebra.
basisWeil ::
  forall s m n r.
  (Reifies s (WeilSettings m n), KnownNat n, KnownNat m, Num r) =>
  [Weil s r]
basisWeil =
  [Weil $ diag i | i <- enumOrdinal $ sNat @m]

-- | @i@ th infinitesimal of Weil algebra.
di ::
  (Eq r, Num r, Reifies s (WeilSettings m n), Fractional r, KnownNat n, KnownNat m) =>
  Ordinal n ->
  Weil s r
di = polyToWeil . var

toWeil ::
  forall n r s m.
  (Eq r, Num r, Reifies s (WeilSettings m n), KnownNat n, KnownNat m, Fractional r) =>
  PowerSeries n r ->
  Weil s r
toWeil ps =
  case reflect @s Proxy of
    WeilSettings {..} ->
      let dic =
            Map.filter (P./= 0) $
              Map.fromList $
                map (SV.map fromIntegral *** WrapFractional) $
                  cutoffMult nonZeroVarMaxPowers ps
       in polyToWeil $ dic ^. re _Terms'

instance
  (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
  LeftModule (WrapFractional Double) (Weil s r)
  where
  (.*) (WrapFractional d) = coerce $ V.map (realToFrac @_ @r d P.*)

instance
  (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)) =>
  RightModule (WrapFractional Double) (Weil s r)
  where
  Weil_ a *. WrapFractional d =
    Weil_ $ V.map (P.* realToFrac d) a

data SomeWeilSettings m where
  SomeWeil :: (KnownNat n, KnownNat m) => WeilSettings n m -> SomeWeilSettings m

deriving instance Show (SomeWeilSettings m)

{- | A setting of specific \(m\)-dimensional Weil algebra,
 generated by  \(n\)-variables.
-}
data WeilSettings m n where
  WeilSettings ::
    (KnownNat n, KnownNat m) =>
    { -- | Monomial basis (or, standard monomials) of Weil algebra
      weilBasis :: Vec m (UVec n Word)
    , -- | Maximum non-vanishing power of each ariables;
      -- N.B. Could be distinct with @maximum weilBasis@, because
      -- there can be a non-zero monomial which are not a standard monomial.
      nonZeroVarMaxPowers :: UVec n Word
    , -- | Dictionary for non-vanishing monomials and their representation;
      --   should be constructed lazily for the sake of efficiency.
      weilMonomDic :: HM.HashMap (UVec n Word) (Vec m Rational)
    , -- | Multiplciation table
      table :: HM.HashMap (Int, Int) (Polynomial Rational n)
    } ->
    WeilSettings m n

deriving instance Show (WeilSettings m n)

instance
  ( PrettyCoeff (WrapFractional r)
  , KnownNat n
  , KnownNat m
  , Eq r
  , Fractional r
  , Reifies s (WeilSettings n m)
  ) =>
  Show (Weil s r)
  where
  showsPrec d w =
    showsPolynomialWith'
      False
      showsCoeff
      ( SV.generate sNat $ \i ->
          "d(" ++ show (fromEnum i) ++ ")"
      )
      d
      $ weilToPoly w

reifyWeil ::
  KnownNat n =>
  Ideal (Polynomial Rational n) ->
  ( forall m s.
    (Reifies s (WeilSettings m n), KnownNat m) =>
    Proxy s ->
    r
  ) ->
  Maybe r
reifyWeil i f = do
  SomeWeil (ws :: WeilSettings m n) <- isWeil i
  pure $ reify ws f

withWeil ::
  forall a n.
  (KnownNat n, Eq a, Fractional a) =>
  Ideal (Polynomial Rational n) ->
  ( forall s m.
    (KnownNat m, Reifies s (WeilSettings m n)) =>
    Weil s a
  ) ->
  Maybe (Polynomial a n)
withWeil i f = reifyWeil i $ \(s :: Proxy s) ->
  case reflect s of
    WeilSettings {} -> coerce $ weilToPoly $ f @s

isWeil ::
  KnownNat n =>
  Ideal (Polynomial Rational n) ->
  Maybe (SomeWeilSettings n)
isWeil ps = reifyQuotient ps $ \(p :: Proxy s) -> do
  qBasis0 <-
    V.fromList
      <$> standardMonomials' p
  let weilBasis0 =
        V.map
          (SV.map fromIntegral . head . F.toList . monomials . quotRepr)
          qBasis0
      table =
        HM.fromList
          [ ((i, j), c)
          | (i, SV.map fromIntegral -> m) <-
              V.toList $ V.indexed weilBasis0
          , (j, SV.map fromIntegral -> n) <-
              V.toList $ V.indexed weilBasis0
          , i <= j
          , let c = quotRepr $ modIdeal' p (fromMonomial m * fromMonomial n)
          , c /= 0
          ]
      pgens = SV.generate sNat $ \i -> univPoly i ps
      nonZeroVarMaxPowers =
        convVec @_ @V.Vector $
          SV.map (fromIntegral . pred . totalDegree') pgens
  guard $ all isMonomial pgens
  case SV.toSomeSized weilBasis0 of
    SV.SomeSized (sn :: SNat m) weilBasis ->
      withKnownNat sn $
        let weilMonomDic =
              LHM.fromList
                [ (mon, SV.unsafeToSized sn pol)
                | mon <- otraverse (enumFromTo 0) nonZeroVarMaxPowers
                , let pol =
                        vectorRep $
                          modIdeal' p $
                            fromMonomial $
                              SV.map fromIntegral mon
                , oany (/= 0) pol
                ]
         in pure $ SomeWeil WeilSettings {..}

isMonomial :: KnownNat n => OrderedPolynomial Rational Grevlex n -> Bool
isMonomial = (== 1) . Map.size . Map.filter (/= 0) . terms'

{- | Polynomial funtion corresponding to an given element
   of Weil algebra.
-}
weilToPolyFun ::
  (Fractional r, Eq r, KnownNat n, KnownNat m) =>
  Reifies s (WeilSettings n m) =>
  Weil s r ->
  Vec m r ->
  r
weilToPolyFun = polyToFun . weilToPoly

polyToFun ::
  forall r n.
  (Eq r, Num r, KnownNat n) =>
  Polynomial (WrapFractional r) n ->
  Vec n r ->
  r
polyToFun =
  coerce . liftMap (\i -> WrapFun @(Vec n r) (WrapFractional . (SV.%!! i)))

newtype WrapFun a b = WrapFun (a -> b)
  deriving newtype
    ( Abelian
    , Additive
    , Monoidal
    , Group
    )

instance Num b => Num (WrapFun a b) where
  fromInteger = WrapFun . const . fromInteger
  (+) = coerce $ liftA2 @((->) a) $ (P.+) @b
  (-) = coerce $ liftA2 @((->) a) $ (P.-) @b
  (*) = coerce $ liftA2 @((->) a) $ (P.*) @b
  signum = coerce ((signum .) :: (a -> b) -> a -> b)
  negate = coerce ((P.negate .) :: (a -> b) -> a -> b)
  abs = coerce ((P.abs .) :: (a -> b) -> a -> b)

instance Fractional b => Fractional (WrapFun a b) where
  recip = coerce ((P.recip .) :: (a -> b) -> a -> b)
  (/) = coerce $ liftA2 @((->) a) $ (P./) @b
  fromRational = WrapFun . const . P.fromRational

instance Floating b => Floating (WrapFun a b) where
  log = coerce $ fmap @((->) a) @b log
  logBase = coerce $ liftA2 @((->) a) @b logBase
  exp = coerce $ fmap @((->) a) @b exp
  (**) = coerce $ liftA2 @((->) a) @b (**)

  pi = WrapFun $ const pi
  sin = coerce $ fmap @((->) a) @b sin
  cos = coerce $ fmap @((->) a) @b cos
  tan = coerce $ fmap @((->) a) @b tan
  asin = coerce $ fmap @((->) a) @b asin
  acos = coerce $ fmap @((->) a) @b acos
  atan = coerce $ fmap @((->) a) @b atan

  sinh = coerce $ fmap @((->) a) @b sinh
  cosh = coerce $ fmap @((->) a) @b cosh
  tanh = coerce $ fmap @((->) a) @b tanh
  asinh = coerce $ fmap @((->) a) @b asinh
  acosh = coerce $ fmap @((->) a) @b acosh
  atanh = coerce $ fmap @((->) a) @b atanh

instance {-# OVERLAPPING #-} Semiring b => LeftModule (Scalar b) (WrapFun a b) where
  (.*) = \(Scalar c) (WrapFun f) -> WrapFun $ (c *) . f

instance {-# OVERLAPPING #-} Semiring b => RightModule (Scalar b) (WrapFun a b) where
  (*.) = \(WrapFun f) (Scalar c) -> WrapFun $ (* c) . f

instance Multiplicative b => Multiplicative (WrapFun a b) where
  (*) = coerce $ liftA2 @((->) a) $ (*) @b

instance Unital b => Unital (WrapFun a b) where
  one = WrapFun $ const one

instance Commutative b => Commutative (WrapFun a b)

instance Semiring b => Semiring (WrapFun a b)

instance Rig b => Rig (WrapFun a b) where
  fromNatural i = WrapFun $ const $ fromNatural i

instance Ring b => Ring (WrapFun a b) where
  fromInteger i = WrapFun $ const $ fromInteger' i

deriving newtype instance (LeftModule c b) => LeftModule c (WrapFun a b)

deriving newtype instance (RightModule c b) => RightModule c (WrapFun a b)

deriving newtype instance (PrettyCoeff a) => PrettyCoeff (WrapFractional a)

instance PrettyCoeff Double where
  showsCoeff d r
    | r < 0 = Negative $ Just $ showsPrec d $ abs r
    | r == 0 = Vanished
    | r == 1 = OneCoeff
    | otherwise = Positive $ showsPrec d r

{- | @'Weil' 'D1' r@ Corresponds to @'Dual' r@ numbers;
   Just an \(\mathbb{R}[X]/X^2\).
-}
data D1

weilToVector ::
  (KnownNat n, KnownNat m, Reifies s (WeilSettings n m)) =>
  Weil s r ->
  Vec n r
weilToVector (Weil v) = v

instance Reifies D1 (WeilSettings 2 1) where
  reflect =
    const $
      WeilSettings
        { weilBasis = SV.singleton 0 :< SV.singleton 1 :< Nil
        , weilMonomDic =
            HM.fromList
              [ (SV.singleton 0, 1 :< 0 :< SV.Nil)
              , (SV.singleton 1, 0 :< 1 :< SV.Nil)
              ]
        , nonZeroVarMaxPowers = SV.singleton 1
        , table = HM.fromList [((0, 0), one), ((0, 1), var 0)]
        }

-- | \(\mathbb{R} \oplus D(2) = k[x,y]/(x^2,y^2,xy) \)
data D2

instance Reifies D2 (WeilSettings 3 2) where
  reflect = const $
    fromJust $ do
      SomeWeil (sett :: WeilSettings n 2) <-
        isWeil $ toIdeal [var 0 ^ 2, var 1 ^ 2, var 0 * var 1 :: Polynomial Rational 2]
      case (sNat @3) %~ (sNat @n) of
        Equal -> return sett
        _ -> Nothing

{- | Tensor Product.

   For example, we have @'Weil' ('D1' '|*|' 'D1') 'Double'@ \(\cong\) @'Duals' 2 'Double'@
-}
data d |*| d'

instance
  ( Reifies d (WeilSettings n m)
  , Reifies d' (WeilSettings n' m')
  , KnownNat n
  , KnownNat n'
  , KnownNat n''
  , KnownNat m
  , KnownNat m'
  , KnownNat m''
  , (n'' :: Nat) ~ (n * n')
  , (m'' :: Nat) ~ (m + m')
  ) =>
  Reifies (d |*| d') (WeilSettings n'' m'')
  where
  reflect =
    const $
      let weil = reflect @d Proxy :: WeilSettings n m
          weil' = reflect @d' Proxy :: WeilSettings n' m'
          wbs =
            SV.concat $
              SV.map
                (\w -> SV.map (w SV.++) $ weilBasis weil')
                $ weilBasis weil
          n, n' :: Int
          n = fromIntegral $ natVal' @n proxy#
          n' = fromIntegral $ natVal' @n' proxy#
          mub =
            nonZeroVarMaxPowers weil SV.++ nonZeroVarMaxPowers weil'
          tab =
            HM.fromList
              [ ((i, j), castPolynomial pl * shiftR (sNat @m) pr)
              | j <- [0 .. n * n' - 1]
              , i <- [0 .. j]
              , let (il, ir) = i `P.divMod` n'
                    (jl, jr) = j `P.divMod` n'
              , pl <-
                  maybeToList $
                    HM.lookup (min il jl, max il jl) $ table weil
              , pr <-
                  maybeToList $
                    HM.lookup (min ir jr, max ir jr) $ table weil'
              ]
       in WeilSettings
            { weilBasis = wbs
            , weilMonomDic =
                LHM.fromList
                  [ (mon, coes)
                  | (lh, SV.unsized -> lCoes) <- HM.toList $ weilMonomDic weil
                  , (rh, SV.unsized -> rCoes) <- HM.toList $ weilMonomDic weil'
                  , let mon = lh SV.++ rh
                        coes = SV.generate sNat $ \od ->
                          let (l, r) = fromIntegral (ordToNatural od) `P.divMod` n'
                           in (lCoes V.! l) * (rCoes V.! r)
                  , oany (/= 0) coes
                  ]
            , nonZeroVarMaxPowers = mub
            , table = tab
            }

data Cubic

instance Reifies Cubic (WeilSettings 3 1) where
  reflect = const $
    fromJust $ do
      SomeWeil (sett :: WeilSettings n 1) <-
        isWeil $ toIdeal [var 0 ^ 3 :: Polynomial Rational 1]
      Equal <- pure $ (sNat @3) %~ (sNat @n)
      return sett

-- | @'DOrder' n@ corresponds to \(\mathbb{R}[X]/X^n\).
data DOrder (n :: Nat)

instance KnownNat n => Reifies (DOrder n) (WeilSettings n 1) where
  reflect =
    const $
      let n = fromIntegral (natVal' @n proxy#)
       in WeilSettings
            { weilBasis = SV.generate (sNat @n) (SV.singleton . toEnum . fromEnum)
            , weilMonomDic =
                HM.fromList
                  [ ( SV.singleton $ fromIntegral $ ordToNatural i
                    , diag i
                    )
                  | i <- enumOrdinal $ sNat @n
                  ]
            , nonZeroVarMaxPowers = SV.singleton $ n - 1
            , table =
                LHM.fromList
                  [ ((i, j), c)
                  | j <- [0 .. fromIntegral n - 1]
                  , i <- [0 .. j]
                  , i + j < fromIntegral n
                  , let c = var 0 ^ fromIntegral (i + j)
                  ]
            }

realPart ::
  forall w a n m.
  (KnownNat n, KnownNat m, Reifies w (WeilSettings n m), Floating a) =>
  Weil w a ->
  a
realPart (Weil_ vec)
  | V.null vec = 0
  | otherwise = V.head vec

diffUpTo ::
  forall a.
  (Floating a, Eq a) =>
  Natural ->
  (forall x. Floating x => x -> x) ->
  a ->
  M.Map Natural a
diffUpTo n f a = case someNatVal n of
  SomeNat (_ :: Proxy n) ->
    let Weil vec = f (injCoeWeil a + di 0) :: Weil (DOrder (n + 1)) a
     in M.fromList $ zipWith (\i c -> (i, fromIntegral (factorial $ fromIntegral i) P.* c)) [0 ..] $ SV.toList vec
