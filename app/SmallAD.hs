{-# LANGUAGE DeriveFunctor, RankNTypes #-}
module SmallAD where
import Symbolic

data AD a = AD { real :: a, inifinitesimal :: a }
  deriving (Eq, Ord, Functor)

instance Show a => Show (AD a) where
  showsPrec d (AD r i) = showParen (d > 10) $
    showsPrec 11 r . showString " + "
    . showsPrec 11 i
    . showString " d"

instance Num a => Num (AD a) where
  fromInteger = flip AD 0 . fromInteger
  AD f f' + AD g g' = AD (f + g) (f' + g')
  AD f f' * AD g g' = AD (f * g) (f' * g + f * g')
  AD f f' - AD g g' = AD (f - g) (f' - g')
  negate (AD f f') = AD (negate f) (negate f')
  abs (AD f f') = AD (abs f) (signum f)
  signum (AD f f') = AD (signum f) 0

instance Fractional a => Fractional (AD a) where
  recip (AD f f') = AD (recip f) (negate $ f^2 * f')
  AD f f' / AD g g' = AD (f / g) (f' / g - g' * f / g^2)
  fromRational = flip AD 0 . fromRational

instance Floating a => Floating (AD a) where
  pi = AD pi 0
  sin (AD f f') = AD (sin f) (f' * cos f)
  cos (AD f f') = AD (cos f) (-f' * sin f)
  tan (AD f f') = AD (tan f) (f' / cos f ^ 2)
  asin (AD f f') = AD (asin f) (f' / sqrt (1 - f^2))
  acos (AD f f') = AD (acos f) (-f' / sqrt (1 - f^2))
  atan (AD f f') = AD (atan f) (f' / (1 + f^2))
  exp (AD f f') = AD (exp f) (f' * exp f)
  log (AD f f') = AD (log f) (f' / f)

  sinh (AD f f') = AD (sinh f) (f' * cosh f)
  cosh (AD f f') = AD (cosh f) (f' * sinh f)
  tanh (AD f f') = AD (tanh f) (f' / cosh f ^ 2)
  asinh (AD f f') = AD (asinh f) (f' / sqrt (1 + f^2))
  acosh (AD f f') = AD (acosh f) (f' / sqrt (f^2-1))
  atanh (AD f f') = AD (atanh f) (f' / (1 - f^2))

d :: Num a => AD a
d = AD 0 1

diff :: Floating a => (forall x. Floating x => x -> x) -> a -> a
diff f x = inifinitesimal $ f (AD x 1)

-- >>> let x = pi/4 + d
-- >>> cos x  + sin x
-- 1.414213562373095 + 1.1102230246251565e-16 d

-- >>> cos (pi/4) + sin (pi/4)
-- 1.414213562373095

-- >>> -sin (pi/4) + cos (pi/4)
-- 1.1102230246251565e-16

-- * 記号微分の復元
-- >>> :type x

-- >>> normalise <$> cos (AD x 1) + sin (AD x 1)

-- * 二重数の冪零性

-- >>> d

-- >>> d * d
