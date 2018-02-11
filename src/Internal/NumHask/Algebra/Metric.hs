{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies   #-}
{-# OPTIONS_GHC -Wall #-}

-- | Metric classes
module Internal.NumHask.Algebra.Metric
  ( Signed(..)
  , Normed(..)
  , Metric(..)
  , Epsilon(..)
  , (≈)
  , Abs
  ) where

import Internal.NumHask.Algebra.Additive
import Internal.NumHask.Algebra.Field
import Internal.NumHask.Algebra.Multiplicative
import qualified Protolude as P
import Internal.Internal
import Protolude
       (Bool(..), Double, Eq(..), Float, Int, Integer, Ord(..), ($), (&&))

-- | 'signum' from base is not an operator replicated in numhask, being such a very silly name, and preferred is the much more obvious 'sign'.  Compare with 'Norm' and 'Banach' where there is a change in codomain
--
-- > abs a * sign a == a
--
-- Generalising this class tends towards size and direction (abs is the size on the one-dim number line of a vector with its tail at zero, and sign is the direction, right?).
class (MultiplicativeUnital a  r t) =>
      Signed a  r t where
  sign :: a -> Computation r t (D r t) 
  abs :: a -> Computation r t (D r t)

data Abs = Abs deriving P.Show 

instance Signed (D r Double) r Double where
  sign a =
    if a >= zero
      then one
      else negate (one :: D r Double)
  abs = monOp Abs

instance Signed (D r Float) r Float where
  sign a =
    if a >= zero
      then one
      else negate (one :: D r Float)
  abs =  monOp Abs

instance Signed (Computation r Double (D r Double)) r Double where
  sign a = do
    ca <- a
    if ca >= (zero :: (D r Double))
      then one
      else negate (one :: D r Double)
  abs a = do
    ca <- a
    monOp Abs ca

instance Signed (Computation r Float (D r Float)) r Float where
  sign a = do
    ca <- a
    if ca >= zero
      then one
      else negate (one :: D r Float)
  abs a =  do
    ca <- a
    monOp Abs ca


-- | Abs
--  compute $ diff' abs a
-- (D 3.0, D 1.0)
instance (P.Num a, Signed (D r a) r a, AdditiveUnital (D r a) r a, AdditiveInvertible (D r a) r a, P.Ord a, Multiplicative (D r a) (Computation r a (D r a)) r a
         ) =>
         MonOp Abs r a where

  {-# INLINE fd #-}
  fd _ a =
    if a >= (zero :: D r a)
      then P.pure a
      else monOp Negate a
  {-# INLINE df #-}
  df _ _ ap at = at * sign ap
  
instance (P.Num a) => FfMon Abs a where
  {-# INLINE ff #-}
  ff _ a = P.abs a

instance (Signed (D r a) r a,  Multiplicative (D r a) (D r a) r a) => Trace Abs r a where
  pushEl (U _ a) dA = do
    sp <-  sign (p a)
    dl <- dA * sp
    P.pure [(dl, a)]
  resetEl (U _ a ) = P.pure [a]

-- | Like Signed, except the codomain can be different to the domain.
class Normed a r t | a -> r, a -> t where
  size :: a -> Computation r t (D r t)

instance Normed (D r Double) r Double where
  size = abs

instance Normed (D r Float) r Float where
  size = abs

instance Normed (Computation r Double (D r Double)) r Double where
  size = abs

instance Normed (Computation r Float (D r Float)) r Float where
  size = abs

-- | distance between numbers
--
-- > distance a b >= zero
-- > distance a a == zero
-- > \a b c -> distance a c + distance b c - distance a b >= zero &&
-- >           distance a b + distance b c - distance a c >= zero &&
-- >           distance a b + distance a c - distance b c >= zero &&
class Metric a b r t | a -> r, a -> t, b -> r, b -> t, a b -> r, a b -> t where
  distance :: a -> b -> Computation r t (D r t)

instance Metric (D r Double) (D r Double) r Double where
  distance a b = abs (a - b)

instance Metric (D r Float) (D r Float) r Float where
  distance a b = abs (a - b)

instance Metric (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double where
  distance a b = abs (a - b)

instance Metric (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float where
  distance a b = abs (a - b)

instance Metric (D r Double) (Computation r Double (D r Double)) r Double where
  distance a b = abs (a - b)

instance Metric (D r Float) (Computation r Float (D r Float)) r Float where
  distance a b = abs (a - b)

instance Metric (Computation r Double (D r Double)) (D r Double) r Double where
  distance a b = abs (a - b)

instance Metric (Computation r Float (D r Float)) (D r Float) r Float where
  distance a b = abs (a - b)


-- | todo: This should probably be split off into some sort of alternative Equality logic, but to what end?
class (AdditiveGroup a b r t) =>
      Epsilon a b r t where
  nearZero :: (c ~ a, c ~ b) => c -> Computation r t (Bool)
  aboutEqual :: a -> b -> Computation r t (Bool)
  positive :: (c ~ a, c ~ b) => c -> Computation r t (Bool)
  veryPositive :: (c ~ a, c ~ b) => c -> Computation r t (Bool)
  veryNegative :: (c ~ a, c ~ b) => c -> Computation r t (Bool)
  

infixl 4 ≈

-- | todo: is utf perfectly acceptable these days?
(≈) :: (Epsilon a b r t ) => a -> b -> Computation r t (Bool)
(≈) = aboutEqual

instance (P.Eq (Computation r Double (D r Double))) => Epsilon (D r Double) (D r Double) r Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D r Double))
  aboutEqual a b = nearZero $ a - b
  positive a = do
    ca <- abs a
    P.pure $ (a == ca)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Float (D r Float))) => Epsilon (D r Float) (D r Float) r Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D r Float))
  aboutEqual a b = nearZero $ a - b
  positive a = do
    ca <- abs a
    P.pure $ (a == ca)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Double (D r Double))) => Epsilon (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D r Double))
  aboutEqual a b = nearZero $ a - b
  positive a = P.pure $ (a == abs a)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Float (D r Float))) => Epsilon (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D r Float))
  aboutEqual a b = nearZero $ a - b
  positive a = P.pure $ (a == abs a)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Double (D r Double))) => Epsilon (D r Double) (Computation r Double (D r Double)) r Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D r Double))
  aboutEqual a b = nearZero $ a - b
  positive a = do
    ca <- abs a
    P.pure $ (a == ca)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Float (D r Float))) => Epsilon (D r Float) (Computation r Float (D r Float)) r Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D r Float))
  aboutEqual a b = nearZero $ a - b
  positive a = do
    ca <- abs a
    P.pure $ (a == ca)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Double (D r Double))) => Epsilon (Computation r Double (D r Double)) (D r Double) r Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D r Double))
  aboutEqual a b = nearZero $ a - b
  positive a = P.pure $ (a == abs a)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

instance (P.Eq (Computation r Float (D r Float))) => Epsilon (Computation r Float (D r Float)) (D r Float) r Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D r Float))
  aboutEqual a b = nearZero $ a - b
  positive a = P.pure $ (a == abs a)
  veryPositive a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na && pa
  veryNegative a = do
    na <- nearZero a
    pa <- positive a
    P.pure $ P.not na P.|| pa

