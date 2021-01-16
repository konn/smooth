{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Utils where

import Control.Subcategory (CFoldable, CFreeMonoid, CZip, Dom)
import Data.MonoTraversable
import Data.Reflection (Reifies)
import Data.Singletons.Prelude (sing)
import Data.Sized.Builtin (Sized)
import qualified Data.Sized.Builtin as SV
import Data.Type.Ordinal.Builtin
import qualified Data.Vector.Generic as G
import GHC.Exts
import GHC.Generics
import GHC.TypeNats
import Generic.Random hiding ((:+))
import qualified Generic.Random as GR
import Numeric.Algebra.Smooth.Dual
import Numeric.Algebra.Smooth.Weil
import Numeric.Natural
import Test.QuickCheck
import Test.QuickCheck.Instances ()

data Expr n
  = Sin (Expr n)
  | Cos (Expr n)
  | Tan (Expr n)
  | Asin (Expr n)
  | Acos (Expr n)
  | Atan (Expr n)
  | Sinh (Expr n)
  | Cosh (Expr n)
  | Tanh (Expr n)
  | Asinh (Expr n)
  | Acosh (Expr n)
  | Atanh (Expr n)
  | Exp (Expr n)
  | Log (Expr n)
  | LogBase (Expr n) (Expr n)
  | Expr n :+ Expr n
  | Expr n :- Expr n
  | Expr n :* Expr n
  | -- | Expr n :/ Expr n
    --  | Expr n :** Expr n
    Expr n :^ Natural
  | Negate (Expr n)
  | -- | Recip (Expr n)
    K Double
  | Arg (Ordinal n)
  deriving (Show, Eq, Ord, Generic)

infixl 6 :+, :-

infixl 7 :* -- , :/

infixr 8 :^ --, :**

instance
  ( MonoTraversable (v a)
  , Element (v a) ~ a
  , Dom v a
  , G.Vector v a
  , KnownNat n
  , Arbitrary a
  ) =>
  Arbitrary (Sized v n a)
  where
  arbitrary =
    SV.unsafeToSized' . G.fromList
      <$> vector (fromIntegral $ natVal' @n proxy#)
  shrink = otraverse shrink

instance (KnownNat n) => Arbitrary (Ordinal n) where
  arbitrary
    | natVal' @n proxy# == 0 = elements []
    | otherwise = elements $ enumOrdinal @n sing
  shrink =
    map toEnum
      . filter (\i -> fromIntegral i < natVal' @n proxy# && 0 <= i)
      . shrink
      . fromEnum

instance (KnownNat n) => Arbitrary (Expr n) where
  arbitrary =
    genericArbitraryRec uniform
      `withBaseCase` (Arg <$> arbitrary)
  shrink = genericShrink

newtype TotalExpr n = TotalExpr {runTotalExpr :: Expr n}
  deriving newtype (Eq, Show)

instance KnownNat n => Arbitrary (TotalExpr n) where
  arbitrary =
    TotalExpr
      <$> genericArbitraryRecG
        ((runTotalExpr @n <$> arbitrary) GR.:+ (arbitrary @Double) GR.:+ (arbitrary @(Ordinal n)) GR.:+ ())
        ( (1 :: W "Sin") % (1 :: W "Cos") % (0 :: W "Tan")
            % (0 :: W "Asin")
            % (0 :: W "Acos")
            % (1 :: W "Atan")
            % (0 :: W "Sinh")
            % (0 :: W "Cosh")
            % (0 :: W "Tanh")
            -- Actually, sinh is total. but it grows so fast to reach infinity
            % (1 :: W "Asinh")
            % (0 :: W "Acosh")
            % (0 :: W "Atanh")
            % (0 :: W "Exp") -- Yes, exponential is total, but it is easy to explode...
            % (0 :: W "Log")
            % (0 :: W "LogBase")
            % (1 :: W ":+")
            % (1 :: W ":-")
            % (1 :: W ":*")
            % (0 :: W ":^")
            % (1 :: W "Negate")
            % (1 :: W "K")
            % (1 :: W "Arg")
            % ()
        )
      `withBaseCase` (Arg <$> arbitrary)

evalExpr ::
  forall n a f.
  (KnownNat n, Floating a, CFoldable f, SV.DomC f a) =>
  Expr n ->
  Sized f n a ->
  a
evalExpr (Arg o) v = v SV.%!! o
evalExpr (Exp e) v = exp $ evalExpr e v
evalExpr (Log e) v = log $ evalExpr e v
evalExpr (LogBase b e) v = logBase (evalExpr b v) $ evalExpr e v
evalExpr (Sin e) v = sin $ evalExpr e v
evalExpr (Cos e) v = cos $ evalExpr e v
evalExpr (Tan e) v = tan $ evalExpr e v
evalExpr (Asin e) v = asin $ evalExpr e v
evalExpr (Acos e) v = acos $ evalExpr e v
evalExpr (Atan e) v = atan $ evalExpr e v
evalExpr (Sinh e) v = sinh $ evalExpr e v
evalExpr (Cosh e) v = cosh $ evalExpr e v
evalExpr (Tanh e) v = tanh $ evalExpr e v
evalExpr (Asinh e) v = asinh $ evalExpr e v
evalExpr (Acosh e) v = acosh $ evalExpr e v
evalExpr (Atanh e) v = atanh $ evalExpr e v
evalExpr (l :+ r) v = evalExpr l v + evalExpr r v
evalExpr (l :- r) v = evalExpr l v - evalExpr r v
evalExpr (l :* r) v = evalExpr l v * evalExpr r v
-- evalExpr (l :/ r)      v = evalExpr l v / evalExpr r v
evalExpr (l :^ r) v = evalExpr l v ^ r
-- evalExpr (l :** r)     v = evalExpr l v ** evalExpr r v
evalExpr (K i) _ = realToFrac i
evalExpr (Negate e) v = negate $ evalExpr e v

-- evalExpr (Recip e)     v = recip $ evalExpr e v

class ApproxEq a where
  approxEqWith :: Rational -> a -> a -> Bool
  approxEq :: a -> a -> Bool
  approxEq = approxEqWith 1e-6

instance ApproxEq Double where
  approxEqWith err l r
    | isIndefinite l = isIndefinite r
    | isIndefinite r = isIndefinite l
    | l == 0 = abs r < fromRational err
    | r == 0 = abs l < fromRational err
    | otherwise =
      abs (l - r) / max (abs l) (abs r) < fromRational err

instance
  ( ApproxEq a
  , Floating a
  , Reifies w (WeilSettings n m)
  , KnownNat n
  , KnownNat m
  ) =>
  ApproxEq (Weil w a)
  where
  approxEqWith err (Weil as) (Weil bs) =
    oand $ SV.zipWithSame (approxEqWith err) as bs

(==~) :: (ApproxEq a, Show a) => a -> a -> Property
l ==~ r =
  counterexample (show l ++ " ~/= " ++ show r) $
    approxEq l r

infix 4 ==~

instance Arbitrary SomeNat where
  arbitrary = sized $ \i ->
    someNatVal <$> elements [1 .. fromIntegral (i + 1)]
  shrink (SomeNat p) =
    map someNatVal $ shrink $ natVal p

isIndefinite :: RealFloat a => a -> Bool
isIndefinite v = isNaN v || isInfinite v

instance
  ( MonoTraversable (v a)
  , MonoFoldable (v Bool)
  , Element (v a) ~ a
  , Element (v Bool) ~ Bool
  , SV.DomC v Bool
  , SV.DomC v a
  , G.Vector v a
  , KnownNat n
  , ApproxEq a
  , CZip v
  , CFreeMonoid v
  ) =>
  ApproxEq (Sized v n a)
  where
  approxEqWith err = fmap oand . SV.zipWith (approxEqWith err)

dualToTup ::
  Num a => Dual a -> (a, a)
dualToTup (Dual a da) = (a, da)

(!?) :: Num a => [a] -> Word -> a
[] !? _ = 0
(x : _) !? 0 = x
(_ : xs) !? n = xs !? (n - 1)

instance
  ( KnownNat n
  , KnownNat m
  , Arbitrary a
  , Reifies w (WeilSettings n m)
  ) =>
  Arbitrary (Weil w a)
  where
  arbitrary = Weil <$> arbitrary
  shrink (Weil as) = Weil <$> (mapM shrink as)
