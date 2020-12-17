{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall #-}

module Symbolic
  ( Symbolic (..),
    (.:*),
    (.:+),
    (.:-),
    (.:/),
    (.:**),
    x,
    y,
    Reducer,
    normalise,
  )
where

import Algebra.Ring.Polynomial.Class (PrettyCoeff (..))
import AlgebraicPrelude
  ( WrapFractional (..),
    WrapNum (..),
  )
import Control.Arrow ((***))
import Control.Lens
  ( Plated (..),
    Prism',
    Rewrapped,
    Wrapped (Unwrapped),
    ala,
    makePrisms,
    review,
    transformM,
    (^.),
    (^?),
    _Wrapped',
  )
import Control.Monad ((>=>))
import Control.Monad.Trans.Accum (Accum, add, runAccum)
import qualified Data.DList as DL
import Data.Data (Data)
import Data.Either (partitionEithers)
import Data.Foldable (Foldable (foldl'))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.List (foldl1')
import Data.Monoid (Product (..), Sum (Sum, getSum))
import GHC.Generics (Generic)
import Numeric.Algebra
  ( Abelian,
    Additive,
    Division,
    Group,
    LeftModule,
    Monoidal,
    Multiplicative,
    Rig,
    RightModule,
    Ring,
    Semiring,
    Unital,
  )
import Numeric.Natural (Natural)
import Type.Reflection (Typeable)

data Symbolic
  = Var String
  | Fun String [Symbolic]
  | Lit Double
  | Negate Symbolic
  | Symbolic :+ Symbolic
  | Symbolic :- Symbolic
  | Symbolic :* Symbolic
  | Symbolic :/ Symbolic
  | Symbolic :** Symbolic
  deriving (Eq, Ord, Generic, Typeable, Data)
  deriving
    ( Additive
    , LeftModule Natural
    , RightModule Natural
    , LeftModule Integer
    , RightModule Integer
    , Multiplicative
    , Rig
    , Ring
    , Unital
    , Monoidal
    , Group
    , Abelian
    , Semiring
    )
    via WrapNum Symbolic
  deriving
    (Division)
    via WrapFractional Symbolic
  deriving anyclass (PrettyCoeff, Hashable)

instance Plated Symbolic

infixl 6 :+, :-

infixl 7 :*, :/

infixr 8 :**

instance Show Symbolic where
  showsPrec _ (Var v) = showString v
  showsPrec d (Negate sym) =
    showParen (d > 6) $
      showString "- " . showsPrec 10 sym
  showsPrec d (Fun fun args) =
    showParen (d > 9) $
      showString fun
        . foldl'
          (\l r -> l . showChar ' ' . r)
          id
          (map (showsPrec 10) args)
  showsPrec d (Lit c) = showsPrec d c
  showsPrec d (l :+ r) =
    showParen (d > 6) $
      showsPrec 6 l . showString " + " . showsPrec 6 r
  showsPrec d (l :- r) =
    showParen (d > 6) $
      showsPrec 6 l . showString " - " . showsPrec 7 r
  showsPrec d (l :* r) =
    showParen (d > 7) $
      showsPrec 7 l . showString " * " . showsPrec 8 r
  showsPrec d (l :/ r) =
    showParen (d > 7) $
      showsPrec 7 l . showString " / " . showsPrec 8 r
  showsPrec d (l :** r) =
    showParen (d > 8) $
      showsPrec 9 l . showString " ** " . showsPrec 8 r

instance Num Symbolic where
  fromInteger = Lit . fromInteger
  (+) = (:+)
  (-) = (:-)
  (*) = (:*)
  negate = Negate
  abs = Fun "abs" . pure
  signum = Fun "signum" . pure

instance Fractional Symbolic where
  (/) = (:/)
  recip = Fun "recip" . pure
  fromRational = Lit . fromRational

instance Floating Symbolic where
  pi = Lit pi
  exp = Fun "exp" . pure
  log = Fun "log" . pure
  sqrt = Fun "sqrt" . pure
  (**) = (:**)
  logBase b a = Fun "logBase" [b, a]
  sin = Fun "sin" . pure
  cos = Fun "cos" . pure
  tan = Fun "tan" . pure
  asin = Fun "asin" . pure
  acos = Fun "acos" . pure
  atan = Fun "atan" . pure
  sinh = Fun "sinh" . pure
  cosh = Fun "cosh" . pure
  tanh = Fun "tanh" . pure
  asinh = Fun "asinh" . pure
  acosh = Fun "acosh" . pure
  atanh = Fun "atanh" . pure

makePrisms ''Symbolic

x :: Symbolic
x = Var "x"

y :: Symbolic
y = Var "y"

data Reduction = Reduced | NormalForm
  deriving (Read, Show, Eq, Ord)

instance Semigroup Reduction where
  NormalForm <> r = r
  Reduced <> _ = Reduced

instance Monoid Reduction where
  mempty = NormalForm

type Reducer = Accum Reduction

normalise :: Symbolic -> Symbolic
normalise =
  fixedPoint $
    simplMulM >=> simplAddM >=> reduceM

fixedPoint :: (Symbolic -> Reducer Symbolic) -> Symbolic -> Symbolic
fixedPoint reducer = go
  where
    go sym =
      let (sym', reduced) = runAccum (transformM reducer sym) mempty
       in case reduced of
            NormalForm -> sym'
            Reduced -> go sym'

progress :: a -> Reducer a
progress a = add Reduced >> pure a

noProgress :: a -> Reducer a
noProgress = pure

simplMulM :: Symbolic -> Reducer Symbolic
simplMulM = simpleCommBinM (.:*) Product

simplAddM :: Symbolic -> Reducer Symbolic
simplAddM = simpleCommBinM (.:+) Sum

reduceM :: Symbolic -> Reducer Symbolic
reduceM (Lit 0 :* _) = progress $ Lit 0
reduceM (_ :* Lit 0) = progress $ Lit 0
reduceM (Lit l :+ Lit r) = progress $ Lit $ l + r
reduceM (Lit l :- Lit r) = progress $ Lit $ l - r
reduceM (l :- Lit 0) = progress l
reduceM (Lit 0 :- l) = progress $ Negate l
reduceM (Lit l :* Lit r) = progress $ Lit $ l * r
reduceM (Lit l :/ Lit r) = progress $ Lit $ l / r
reduceM (l :/ Lit 1) = progress l
reduceM (Lit l :** Lit r) = progress $ Lit $ l ** r
reduceM (Negate (Negate l)) = progress l
reduceM (Negate (Lit l)) = progress $ Lit $ negate l
reduceM (Fun uFun [Lit l])
  | Just f <- HM.lookup uFun uFuns = progress $ Lit $ f l
reduceM (Fun binFun [Lit l, Lit r])
  | Just op <- HM.lookup binFun binFuns =
    progress $ Lit $ op l r
reduceM f@Fun {} = noProgress f
reduceM t = noProgress t

binFuns :: HashMap String (Double -> Double -> Double)
binFuns =
  HM.fromList
    [ ("logBase", logBase)
    ]

uFuns :: HashMap String (Double -> Double)
uFuns =
  HM.fromList
    [ ("abs", abs)
    , ("signum", signum)
    , ("recip", recip)
    , ("sqrt", sqrt)
    , ("exp", exp)
    , ("log", log)
    , ("sin", sin)
    , ("cos", cos)
    , ("tan", tan)
    , ("asin", asin)
    , ("acos", acos)
    , ("atan", atan)
    , ("sinh", sinh)
    , ("cosh", cosh)
    , ("tanh", tanh)
    , ("asinh", asinh)
    , ("acosh", acosh)
    , ("atanh", atanh)
    ]

simpleCommBinM ::
  forall w.
  (Rewrapped w w, Unwrapped w ~ Double, Monoid w) =>
  Prism' Symbolic (Symbolic, Symbolic) ->
  (Double -> w) ->
  Symbolic ->
  Reducer Symbolic
simpleCommBinM p op e = do
  let (_, facs) = unfoldBin p e
      (coes0, rests) =
        partitionEithers $
          map
            (\case Lit c -> Left c; e0 -> Right e0)
            facs
      unit = (mempty :: w) ^. _Wrapped'
      coes = filter (/= unit) coes0
      cfacts = ala op foldMap coes
      e'
        | null coes && null rests = Lit unit
        | null coes = foldl1' (curry $ review p) rests
        | otherwise = foldl' (curry $ review p) (Lit cfacts) rests
  if e == e'
    then noProgress e
    else progress e'

unfoldBin :: Prism' a (a, a) -> a -> (Int, [a])
unfoldBin p = (getSum *** DL.toList) . go
  where
    go e =
      case e ^? p of
        Nothing -> (1, DL.singleton e)
        Just (l, r) -> go l <> go r
