{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, DataKinds, DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, DerivingVia                #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, MagicHash        #-}
{-# LANGUAGE MultiParamTypeClasses, ParallelListComp, PolyKinds           #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeApplications            #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances            #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
module Numeric.Algebra.Smooth.Dual where
import qualified AlgebraicPrelude                   as AP
import           Control.Lens
import           Data.Bits
import           Data.Coerce
import           Data.List
import qualified Data.Map                           as M
import           Data.Maybe
import           Data.Singletons.Prelude            (type (<), Sing, sing,
                                                     withSingI)
import           Data.Sized.Builtin                 (Sized)
import qualified Data.Sized.Builtin                 as SV
import           Data.Tuple
import qualified Data.Type.Natural                  as PN
import           Data.Type.Natural.Builtin          (ToPeano, sToPeano)
import           Data.Type.Natural.Class.Arithmetic hiding (PNum (..))
import           Data.Type.Natural.Class.Order      hiding (type (<=))
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
  liftSmooth f (ds :: Vec n (Dual' a)) =
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

-- | \(n\)-ary product of 'Dual' numbers,
--   which does not have mutual relation between
--   each distinct infinitesimals.
type family Duals' n a where
  Duals' 0 a = a
  Duals' n a = Dual' (Duals (n - 1) a)

newtype Duals n a = Duals { runDuals :: Duals' n a }

instance (KnownNat n, Num a) => Num (Duals n a) where
  fromInteger n =
    case sing @n of
      Zero -> Duals $ fromInteger n
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        Dual (fromInteger n :: Duals m a) 0
  Duals a + Duals b =
    case sing @n of
      Zero -> Duals $ a + b
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
            g = unsafeCoerce b
        in f + g
  negate (Duals a) =
    case sing @n of
      Zero -> Duals $ negate a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in negate f
  abs (Duals a) =
    case sing @n of
      Zero -> Duals $ abs a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in abs f
  signum (Duals a) =
    case sing @n of
      Zero -> Duals $ signum a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in signum f
  Duals a * Duals b =
    case sing @n of
      Zero -> Duals $ a * b
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
            g = unsafeCoerce b
        in f * g
  Duals a - Duals b =
    case sing @n of
      Zero -> Duals $ a - b
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
            g = unsafeCoerce b
        in f - g

instance (KnownNat n, Fractional a) => Fractional (Duals n a) where
  fromRational r =
    case sing @n of
      Zero -> Duals $ fromRational r
      Succ (sl :: Sing l) ->
        Duals $ unsafeCoerce (fromRational r :: Dual' (Duals l a))
  Duals a / Duals b =
    case sing @n of
      Zero -> Duals $ a / b
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
            g = unsafeCoerce b
        in f / g
  recip (Duals a) =
    case sing @n of
      Zero -> Duals $ recip a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in recip f

instance (KnownNat n, Floating a) => Floating (Duals n a) where
  sin (Duals a) =
    case sing @n of
      Zero -> Duals $ sin a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in sin f
  cos (Duals a) =
    case sing @n of
      Zero -> Duals $ cos a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in cos f
  tan (Duals a) =
    case sing @n of
      Zero -> Duals $ tan a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in tan f
  asin (Duals a) =
    case sing @n of
      Zero -> Duals $ asin a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in asin f
  acos (Duals a) =
    case sing @n of
      Zero -> Duals $ acos a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in acos f
  atan (Duals a) =
    case sing @n of
      Zero -> Duals $ atan a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in atan f
  exp (Duals a) =
    case sing @n of
      Zero -> Duals $ exp a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in exp f
  log (Duals a) =
    case sing @n of
      Zero -> Duals $ log a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in log f
  sinh (Duals a) =
    case sing @n of
      Zero -> Duals $ sinh a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in sinh f
  cosh (Duals a) =
    case sing @n of
      Zero -> Duals $ cosh a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in cosh f
  tanh (Duals a) =
    case sing @n of
      Zero -> Duals $ tanh a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in tanh f
  asinh (Duals a) =
    case sing @n of
      Zero -> Duals $ asinh a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in asinh f
  acosh (Duals a) =
    case sing @n of
      Zero -> Duals $ acosh a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in acosh f
  atanh (Duals a) =
    case sing @n of
      Zero -> Duals $ atanh a
      Succ (sm :: Sing m) -> Duals $ unsafeCoerce $
        let f = unsafeCoerce a :: Dual' (Duals m a)
        in atanh f
  pi =
    case sing @n of
      Zero                -> Duals pi
      Succ (sl :: Sing m) -> Duals $ unsafeCoerce (pi :: Dual' (Duals m a))



monomIndices :: KnownNat n => Vec n Bool -> V.Vector Int
monomIndices =
  V.map fst . V.filter snd . V.indexed . SV.unsized

components
  :: forall n a. (Eq a, Num a, KnownNat n) => Duals n a -> M.Map (Vec n Bool) a
components (Duals a) =
  case sing @n of
    Zero -> M.singleton SV.empty a
    Succ (sl :: Sing l) ->
      let Dual f df = unsafeCoerce a :: Dual' (Duals l a)
          leftDic = components f
          rightDic = components df
      in  M.filter (/= 0)
        $ M.mapKeys (False SV.<|) leftDic
            `M.union`
          M.mapKeys (True SV.<|) rightDic

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
          , c /= 0
          ]
      where
        showsTerm = foldr ((.) . (\i -> showString "d(" . shows i . showChar ')')) id

dx :: forall k a n. (Num a, KnownNat k, KnownNat n, (k < n) ~ 'True)
   => Duals n a
dx =
  case sing @n of
    Succ (sn :: Sing m) ->
      case zeroOrSucc $ sing @k of
        IsZero                -> Duals $ unsafeCoerce $ Dual (0 :: Duals m a) 1
        IsSucc (sl :: Sing l) ->
          Duals $ unsafeCoerce $ Dual (dx @l :: Duals m a) 0

fromCoeff :: forall n a. (Num a, KnownNat n) => a -> Duals n a
fromCoeff c =
  case sing @n of
    Zero -> Duals c
    Succ (sl :: Sing m) -> Duals $ unsafeCoerce
      (Dual (fromCoeff @m c) 0)
