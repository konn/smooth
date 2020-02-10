{-# LANGUAGE AllowAmbiguousTypes, DataKinds, DerivingVia               #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances   #-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, LambdaCase, MagicHash  #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, NoStarIsType    #-}
{-# LANGUAGE PatternSynonyms, RankNTypes, RecordWildCards              #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances         #-}
{-# LANGUAGE ViewPatterns                                              #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Numeric.Algebra.Smooth.Weil
  ( Weil(Weil), weilToVector
  , type (|*|)
  , D1, Cubic, DOrder
  , toWeil, isWeil
  , weilToPoly, polyToWeil
  ) where
import           Algebra.Algorithms.Groebner
import           Algebra.Algorithms.Groebner.Signature.Rules ()
import           Algebra.Algorithms.ZeroDim
import           Algebra.Ring.Ideal
import           Algebra.Ring.Polynomial
import           Algebra.Ring.Polynomial.Quotient
import           AlgebraicPrelude
import           Control.Lens                                hiding ((:<))
import           Data.Coerce
import qualified Data.Foldable                               as F
import qualified Data.HashMap.Strict                         as HM
import qualified Data.HashSet                                as HS
import qualified Data.Map.Strict                             as Map
import           Data.Maybe
import           Data.MonoTraversable
import           Data.Proxy
import qualified Data.Ratio                                  as R
import           Data.Reflection
import           Data.Singletons.Prelude                     (sing)
import           Data.Singletons.TypeLits                    (withKnownNat)
import           Data.Sized                                  (pattern (:<),
                                                              pattern NilR)
import qualified Data.Sized.Builtin                          as SV
import           Data.Type.Equality
import qualified Data.Vector.Unboxed                         as U
import           GHC.Exts
import           GHC.TypeNats                                as TN
import           Numeric.Algebra.Smooth.Classes
import           Numeric.Algebra.Smooth.PowerSeries
import           Numeric.Algebra.Smooth.Types
import qualified Prelude                                     as P

import qualified Data.Vector as V

{- | Weil algebra.

Weil algebra \(W\) is a \(R\)-algebra together with a unique maximal ideal \(\mathfrak{M}\), which is nipotent and \(W = \mathbb{R} \oplus \mathfrak{M}\) holds.

There are some good characterisation of Weil algebra; the following are equivalent:

  1. \(W\) is a Weil algebra,
  2. \(W\) is isomorphic to a quotient \(\mathbb{R}[X_1, \dots, X_n]/I\) of polynomial ring, and there exists \(k\) such that \(X_1^{k_1} \dots X_n^{k_n} \in I\) for all \(k_1 + \dots + k_n = k\),
  3. \(W\) is isomoprhic to a quotient \(\mathbb{R}[\![X_1, \dots, X_n]\!]/I\) of a ring of formal power series, such that \(I \supseteq (X_1, \dots, X_n)^k\) for some \(k\).
-}
newtype Weil s r = Weil_ { runWeil_ :: Vector r }

pattern Weil
  :: forall s n m r.
     (Reifies s (WeilSettings n m), KnownNat n, KnownNat m)
  => (Reifies s (WeilSettings n m), KnownNat n, KnownNat m)
  => Vec n r -> Weil s r
pattern Weil v <- Weil_ (SV.toSized' @_ @_ @n -> Just v) where
  Weil v = Weil_ (SV.unsized @_ @n v)

deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Additive (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Monoidal (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Group (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Abelian (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Rig (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        =>  Commutative (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Multiplicative (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Semiring (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        =>  Unital (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => Ring (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => LeftModule Natural (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => RightModule Natural (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => LeftModule Integer (Weil s r)
deriving via WrapNum (Weil s r)
  instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
        => RightModule Integer (Weil s r)

fromRational'
  :: Fractional r => Rational -> WrapFractional r
fromRational' = \r -> fromRational $ denominator r R.% numerator r

injCoeWeil
  :: (KnownNat n, KnownNat m, Num r, Reifies s (WeilSettings n m))
  => r -> Weil s r
injCoeWeil a =
  Weil $ SV.generate sing
    (\i -> if i == 0 then a else 0)

instance (KnownNat n, KnownNat m, Eq r, Floating r, Reifies s (WeilSettings n m))
      => Num (Weil s r) where
  (+) = coerce $ V.zipWith ((P.+) @r)
  negate = coerce $ V.map (P.negate @r)
  (-) = coerce $ V.zipWith ((P.-) @r)
  fromInteger = injCoeWeil . fromInteger
  Weil f * Weil g =
    case reflect $ Proxy @s of
      WeilSettings{..} ->
        let a = sum
              [ injectCoeff (WrapFractional $ c P.* d)
                  *
                mapCoeff fromRational'
                  (table HM.! (min i j, max i j))
              | (fromEnum -> i, c) <- itoList f
              , (fromEnum -> j, d) <- itoList g
              ]
        in polyToWeil a

  abs = liftUnary abs
  signum = liftUnary signum

instance
  ( KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)
  ) => Fractional (Weil s r) where
  fromRational = injCoeWeil . P.fromRational
  recip = liftUnary P.recip
  (/) = liftBinary (P./)

instance ( KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)
      ) => Floating (Weil s r) where
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

instance
  ( KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m)
  ) => SmoothRing (Weil s r) where
    liftSmooth f (vs :: KnownNat k => Vec k (Weil s r)) =
      let vs' = SV.map
            ( coerce @_ @(PowerSeries _ r)
            . injPoly
            . weilToPoly
            )
            vs
      in toWeil $ liftSmooth f vs'

polyToWeil
  :: forall s r n m.
       (KnownNat m, Eq r, KnownNat n, Reifies s (WeilSettings m n), Num r)
  => Polynomial (WrapFractional r) n -> Weil s r
polyToWeil a =
  case reflect @s Proxy of
    WeilSettings{..} ->
      Weil
      $ SV.map
          (\m -> unwrapFractional
               $ coeff' (SV.map fromIntegral m) a)
          weilBasis

weilToPoly
  :: forall s r n m.
     (KnownNat m, Eq r, KnownNat n, Reifies s (WeilSettings m n), Fractional r)
  => Weil s r -> Polynomial (WrapFractional r) n
weilToPoly (Weil cs) =
  case reflect @s Proxy of
    WeilSettings{..} -> sum
      $ SV.zipWithSame
          (\m c ->
              polynomial' @(Polynomial (WrapFractional r) _)
              $ Map.fromList
              [ ( SV.map fromIntegral m,
                  WrapFractional c
                )
              ]
          )
          weilBasis
          cs

-- | @i@ th base of Weil algebra.
--
--   @ei 0@ is just the real part.
ei :: (Num r, Reifies s (WeilSettings m n), KnownNat n, KnownNat m)
   => SV.Ordinal m -> Weil s r
ei ord = Weil $ diag ord

-- | @i@ th infinitesimal of Weil algebra.
di :: (Eq r, Num r, Reifies s (WeilSettings m n), KnownNat n, KnownNat m)
   => SV.Ordinal n -> Weil s r
di = polyToWeil . var

toWeil
  :: forall n r s m. (Num r, Reifies s (WeilSettings m n), KnownNat n, KnownNat m)
  => PowerSeries n r -> Weil s r
toWeil ps =
  case reflect @s Proxy of
    WeilSettings{..} ->
      let dic = HM.fromList $ cutoff (osum monomUpperBound) ps
      in Weil
          $ SV.map (\b -> HM.lookupDefault 0 (convVec b) dic)
            weilBasis

instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
      => LeftModule (WrapFractional Double) (Weil s r) where
  (.*) (WrapFractional d) = coerce $ V.map (realToFrac @_ @r d P.*)
instance (KnownNat m, KnownNat n, Eq r, Floating r, Reifies s (WeilSettings n m))
      => RightModule (WrapFractional Double) (Weil s r) where
  Weil_ a *. WrapFractional d =
    Weil_ $ V.map (P.* realToFrac d) a



data SomeWeilSettings m where
  SomeWeil :: (KnownNat n, KnownNat m) => WeilSettings n m -> SomeWeilSettings m

deriving instance Show (SomeWeilSettings m)

data WeilSettings m n where
  WeilSettings
    :: (KnownNat n, KnownNat m) =>
    { weilBasis  :: Vec m (UVec n Word)
    , monomUpperBound :: UVec n Word
    , table :: HM.HashMap (Int, Int) (Polynomial Rational n)
    }
    -> WeilSettings m n

deriving instance Show (WeilSettings m n)


instance
    ( PrettyCoeff (WrapFractional r), KnownNat n, KnownNat m,
      Eq r, Fractional r,
      Reifies s (WeilSettings n m)
    )
  => Show (Weil s r) where
  showsPrec d w =
    showsPolynomialWith'
    False
    showsCoeff
    (SV.generate sing $ \i ->
      "d(" ++ show (fromEnum i) ++ ")"
    )
    d
    $ weilToPoly w

reifyWeil
  :: KnownNat n
  => Ideal (Polynomial Rational n)
  -> (forall m s. Reifies s (WeilSettings m n) =>
        Proxy s -> r
     )
  -> Maybe r
reifyWeil i f = do
  SomeWeil (ws :: WeilSettings m n) <- isWeil i
  pure $ reify ws f

isWeil
  :: KnownNat n
  => Ideal (Polynomial Rational n)
  -> Maybe (SomeWeilSettings n)
isWeil ps = reifyQuotient ps $ \(p :: Proxy s) -> do
  qBasis0 <-
     V.fromList
      <$> standardMonomials' p
  let vs = vars
      weilBasis0 =
        V.map
          (SV.map fromIntegral . head . F.toList . monomials . quotRepr)
          qBasis0
      table =
        HM.fromList
          [ ((i, j), c)
          | (i, SV.map fromIntegral -> m)
              <- V.toList $ V.indexed weilBasis0
          , (j, SV.map fromIntegral -> n)
              <- V.toList $ V.indexed weilBasis0
          , i <= j
          , let c = quotRepr $ modIdeal' p (fromMonomial m * fromMonomial n)
          ]
      rootI = radical $ mapIdeal convertPolynomial ps
      monomUpperBound =
          convVec
          $ SV.map (fromIntegral . maximum)
          $ traverse (convVec @V.Vector)
            weilBasis0
  guard $ all (`isIdealMember` rootI) vs
  case SV.toSomeSized weilBasis0 of
    SV.SomeSized sn weilBasis -> withKnownNat sn $
      pure $ SomeWeil WeilSettings{..}

deriving newtype instance (PrettyCoeff a) => PrettyCoeff (WrapFractional a)
instance PrettyCoeff Double where
  showsCoeff d r
    | r < 0 = Negative $ Just $ showsPrec d $ abs r
    | r == 0 = Vanished
    | r == 1 = OneCoeff
    | otherwise = Positive $ showsPrec d r

-- | @'Weil' 'D1' r@ Corresponds to @'Dual' r@ numbers;
--   Just \(\mathbb{R}[X]/X^2\).
data D1

weilToVector
  :: (KnownNat n, KnownNat m, Reifies s (WeilSettings n m))
  => Weil s r -> Vec n r
weilToVector (Weil v) = v

instance Reifies D1 (WeilSettings 2 1) where
  reflect = const $
    WeilSettings
    { weilBasis = SV.singleton 0 :< SV.singleton 1 :< NilR
    , monomUpperBound = SV.singleton 1
    , table = HM.fromList [((0,0), one), ((0, 1), var 0), ((1,1), zero)]
    }

-- | \(D(2) = k[x,y]/(x^2,y^2,xy) \)
data D2

instance Reifies D2 (WeilSettings 3 2) where
  reflect = const $ fromJust $ do
    SomeWeil (sett :: WeilSettings n 2) <-
      isWeil $ toIdeal [var 0 ^ 2, var 1^2, var 0 * var 1 :: Polynomial Rational 2]
    Refl <- testEquality (sing @3) (sing @n)
    return sett

-- | Tensor Product.
data d |*| d'

instance
  ( Reifies d  (WeilSettings n m),
    Reifies d' (WeilSettings n' m'),
    KnownNat n, KnownNat n', KnownNat n'',
    KnownNat m, KnownNat m', KnownNat m'',
    (n'' :: Nat) ~ (n * n'),
    (m'' :: Nat) ~ (m + m')
  ) => Reifies (d |*| d') (WeilSettings n'' m'') where
  reflect = const $
    let weil  = reflect @d Proxy :: WeilSettings n m
        weil' = reflect @d' Proxy :: WeilSettings n' m'
        wbs = SV.concat
          $ SV.map
            (\w -> SV.map (w SV.++) $ weilBasis weil')
          $ weilBasis weil
        n, n' :: Int
        n  = fromIntegral $ natVal' @n proxy#
        n' = fromIntegral $ natVal' @n' proxy#
        mub =
          monomUpperBound weil SV.++ monomUpperBound weil'
        tab =
          HM.fromList
            [ ((i,j), pl * pr)
            | j <- [0.. n * n']
            , i <- [0.. j-1]
            , let (ir, il) = i `P.divMod` n'
                  (jr, jl) = i `P.divMod` n'
                  pl = castPolynomial $ table weil HM.! (min il jl, max il jl)
                  pr = shiftR (sing @m) $
                       table weil' HM.! (min ir jr, max ir jr)
            ]
    in WeilSettings
        { weilBasis = wbs
        , monomUpperBound = mub
        , table = tab
        }

data Cubic
instance Reifies Cubic (WeilSettings 3 1) where
  reflect = const $ fromJust $ do
    SomeWeil (sett :: WeilSettings n 1) <-
      isWeil $ toIdeal [var 0 ^ 3 :: Polynomial Rational 1]
    Refl <- testEquality (sing @3) (sing @n)
    return sett

-- | @'DOrder' n@ corresponds to \(\mathbb{R}[X]/X^n\).
data DOrder (n :: Nat)

instance KnownNat n => Reifies (DOrder n) (WeilSettings n 1) where
  reflect = const $
    let n = fromIntegral (natVal' @n proxy#)
    in WeilSettings
    { weilBasis = SV.generate (sing @n) (SV.singleton . toEnum . fromEnum)
    , monomUpperBound = SV.singleton $ n - 1
    , table = HM.fromList
        [ ((i, j), c)
        | j <- [0..fromIntegral n - 1]
        , i <- [0..j]
        , let c = if i + j >= fromIntegral n then 0 else var 0 ^ (fromIntegral $ i + j)
        ]
    }
