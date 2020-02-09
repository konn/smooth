{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveGeneric, DerivingStrategies #-}
{-# LANGUAGE GADTs, MagicHash, ScopedTypeVariables, TypeApplications      #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances, UndecidableInstances    #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Utils where
import           Data.ListLike               (ListLike)
import           Data.MonoTraversable
import           Data.Singletons.Prelude     (sing)
import           Data.Sized.Builtin          (Sized)
import qualified Data.Sized.Builtin          as SV
import           Data.Type.Ordinal.Builtin
import qualified Data.Vector.Generic         as G
import           Generic.Random              hiding ((:+))
import           GHC.Exts
import           GHC.Generics
import           GHC.TypeNats
import           Numeric.Algebra.Smooth.Dual
import           Numeric.Natural
import           Test.QuickCheck
import           Test.QuickCheck.Instances   ()

data Expr n
  = Sin (Expr n)
  | Cos (Expr n)
  | Tan (Expr n)
  -- | Asin (Expr n)
  -- | Acos (Expr n)
  | Atan (Expr n)
  | Sinh (Expr n)
  | Cosh (Expr n)
  | Tanh (Expr n)
  -- | Asinh (Expr n)
  -- | Acosh (Expr n)
  | Atanh (Expr n)
  | Exp (Expr n)
  -- | Log (Expr n)
  -- | LogBase (Expr n) (Expr n)
  | Expr n :+ Expr n
  | Expr n :- Expr n
  | Expr n :* Expr n
  -- | Expr n :/ Expr n
--  | Expr n :** Expr n
  | Expr n :^  Natural
  | Negate (Expr n)
  -- | Recip (Expr n)
  | K Double
  | Arg (Ordinal n)
    deriving (Show, Eq, Ord, Generic)

infixl 6 :+, :-
infixl 7 :* -- , :/
infixr 8 :^ --, :**

instance
  ( MonoTraversable (v a), Element (v a) ~ a,
    ListLike (v a) a, G.Vector v a, KnownNat n, Arbitrary a
  ) => Arbitrary (Sized v n a) where
  arbitrary = SV.unsafeToSized' . G.fromList
      <$> vector (fromIntegral $ natVal' @n proxy#)
  shrink = otraverse shrink

instance (KnownNat n) => Arbitrary (Ordinal n) where
  arbitrary
    | natVal' @n proxy# == 0 = elements []
    | otherwise = elements $ enumOrdinal @n sing
  shrink =
      map toEnum
    . filter (\i -> fromIntegral i < natVal' @n proxy# && 0 <= i)
    . shrink . fromEnum

instance (KnownNat n) => Arbitrary (Expr n) where
  arbitrary = genericArbitraryRec uniform
        `withBaseCase`
    (Arg <$> arbitrary)
  shrink = genericShrink

evalExpr
  :: forall n a f.
      (KnownNat n, Floating a, ListLike (f a) a)
  => Expr n -> Sized f n a -> a
evalExpr (Arg o)       v = v SV.%!! o
evalExpr (Exp e)       v = exp $ evalExpr e v
-- evalExpr (Log e)       v = log $ evalExpr e v
-- evalExpr (LogBase b e) v = logBase (evalExpr b v) $ evalExpr e v
evalExpr (Sin e)       v = sin $ evalExpr e v
evalExpr (Cos e)       v = cos $ evalExpr e v
evalExpr (Tan e)       v = tan $ evalExpr e v
-- evalExpr (Asin e)      v = asin $ evalExpr e v
-- evalExpr (Acos e)      v = acos $ evalExpr e v
evalExpr (Atan e)      v = atan $ evalExpr e v
evalExpr (Sinh e)      v = sinh $ evalExpr e v
evalExpr (Cosh e)      v = cosh $ evalExpr e v
evalExpr (Tanh e)      v = tanh $ evalExpr e v
-- evalExpr (Asinh e)     v = asinh $ evalExpr e v
-- evalExpr (Acosh e)     v = acosh $ evalExpr e v
evalExpr (Atanh e)     v = atanh $ evalExpr e v
evalExpr (l :+ r)      v = evalExpr l v + evalExpr r v
evalExpr (l :- r)      v = evalExpr l v - evalExpr r v
evalExpr (l :* r)      v = evalExpr l v * evalExpr r v
-- evalExpr (l :/ r)      v = evalExpr l v / evalExpr r v
evalExpr (l :^ r)      v = evalExpr l v ^ r
-- evalExpr (l :** r)     v = evalExpr l v ** evalExpr r v
evalExpr (K i)         _ = realToFrac i
evalExpr (Negate e)    v = negate $ evalExpr e v
-- evalExpr (Recip e)     v = recip $ evalExpr e v

class ApproxEq a where
  approxEqWith :: Rational -> a -> a -> Bool
  approxEq :: a -> a -> Bool
  approxEq = approxEqWith 1e-7

instance ApproxEq Double where
  approxEqWith err l r
    | isIndefinite l = isIndefinite r
    | isIndefinite r = isIndefinite l
    | l == 0 = abs r < fromRational err
    | r == 0 = abs l < fromRational err
    | otherwise =
        abs (l - r) / max (abs l) (abs r) < fromRational err

instance (ApproxEq a, ApproxEq a)
      => ApproxEq (Dual a) where
  approxEqWith err (Dual l dl) (Dual r dr) =
    approxEqWith err l r && approxEqWith err dl dr

(==~) :: (ApproxEq a, Show a) => a -> a -> Property
l ==~ r =
  counterexample (show l ++ " ~/= " ++ show r)
  $ approxEq l r

infix 4 ==~

instance Arbitrary SomeNat where
  arbitrary = sized $ \i ->
    someNatVal <$> elements [1 .. fromIntegral (i+1)]
  shrink (SomeNat p) =
    map someNatVal $ shrink $ natVal p

instance Arbitrary a => Arbitrary (Dual a) where
  arbitrary = genericArbitrary uniform
  shrink = genericShrink

isIndefinite :: Double -> Bool
isIndefinite v = isNaN v || isInfinite v

instance
  ( MonoTraversable (v a),
    MonoFoldable (v Bool),
    Element (v a) ~ a,
    Element (v Bool) ~ Bool,
    ListLike (v Bool) Bool,
    ListLike (v a) a, G.Vector v a, KnownNat n, ApproxEq a
  ) => ApproxEq (Sized v n a) where
  approxEqWith err = fmap oand . SV.zipWith (approxEqWith err)

instance (ApproxEq r, KnownNat n) => ApproxEq (Duals n r) where
  approxEqWith err (Duals ns) (Duals ms) =
    approxEqWith err ns ms

instance (KnownNat n, Arbitrary r) => Arbitrary (Duals n r) where
  arbitrary = Duals <$> arbitrary
