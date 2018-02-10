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
class (MultiplicativeUnital a) =>
      Signed a where
  sign :: a -> CodomainU a 
  abs :: a -> CodomainU a 

data Abs = Abs deriving P.Show 

instance Signed (D r Double) where
  sign a =
    if a >= zero
      then one
      else negate (one :: D r Double)
  abs = monOp Abs

instance Signed (D r Float) where
  sign a =
    if a >= zero
      then one
      else negate (one :: D r Float)
  abs =  monOp Abs

instance Signed (Computation r Double (D r Double)) where
  sign a = do
    ca <- a
    if ca >= (zero :: (D r Double))
      then one
      else negate (one :: D r Double)
  abs a = do
    ca <- a
    monOp Abs ca

instance Signed (Computation r Float (D r Float))  where
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
instance ( Signed (D r a), AdditiveUnital (D r a), AdditiveInvertible (D r a), P.Ord a, Multiplicative (D r a) (Computation r a (D r a))
         ) =>
         MonOp Abs a where
  {-# INLINE ff #-}
  ff _ a = P.abs a
  {-# INLINE fd #-}
  fd _ a =
    if a >= (zero :: D r a)
      then P.pure a
      else monOp Negate a
  {-# INLINE df #-}
  df _ _ ap at = at * sign ap


instance (Signed (D r a),  Multiplicative (D r a) (D r a)) => Trace Abs a where
  pushEl (U _ a) dA = do
    sp <-  sign (p a)
    dl <- dA * sp
    P.pure [(dl, a)]
  resetEl (U _ a ) = P.pure [a]

-- | Like Signed, except the codomain can be different to the domain.
class Normed a where
  size :: a -> CodomainU a

instance Normed (D r Double) where
  size = abs

instance Normed (D r Float) where
  size = abs

instance Normed (Computation r Double (D r Double)) where
  size = abs

instance Normed (Computation r Float (D r Float)) where
  size = abs

-- | distance between numbers
--
-- > distance a b >= zero
-- > distance a a == zero
-- > \a b c -> distance a c + distance b c - distance a b >= zero &&
-- >           distance a b + distance b c - distance a c >= zero &&
-- >           distance a b + distance a c - distance b c >= zero &&
class Metric a b where
  distance :: a -> b -> CodomainB a b

instance Metric (D r Double) (D r Double) where
  distance a b = abs (a - b)

instance Metric (D r Float) (D r Float)  where
  distance a b = abs (a - b)

instance Metric (Computation r Double (D r Double)) (Computation r Double (D r Double)) where
  distance a b = abs (a - b)

instance Metric (Computation r Float (D r Float)) (Computation r Float (D r Float)) where
  distance a b = abs (a - b)

instance Metric (D r Double) (Computation r Double (D r Double)) where
  distance a b = abs (a - b)

instance Metric (D r Float) (Computation r Float (D r Float)) where
  distance a b = abs (a - b)

instance Metric (Computation r Double (D r Double)) (D r Double) where
  distance a b = abs (a - b)

instance Metric (Computation r Float (D r Float)) (D r Float) where
  distance a b = abs (a - b)


-- | todo: This should probably be split off into some sort of alternative Equality logic, but to what end?
class (AdditiveGroup a b) =>
      Epsilon a b where
  nearZero :: (a ~ c, b ~ c) => c -> Computation r t (Bool)
  aboutEqual :: a -> b -> Computation r t (Bool)
  positive :: (a ~ c, b ~ c, Eq c, Signed c t) => c -> Computation r t (Bool)
  veryPositive ::
       (a ~ c, b ~ c, Eq c, Signed c t) => c -> Computation r t (Bool)
  veryNegative ::
       (a ~ c, b ~ c, Eq c, Signed c t) => c -> Computation r t (Bool)
  

infixl 4 ≈

-- | todo: is utf perfectly acceptable these days?
(≈) :: (Epsilon a b ) => a -> b -> Computation r t (Bool)
(≈) = aboutEqual

instance Epsilon (D r Double) (D r Double) where
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

instance Epsilon (D r Float) (D r Float) where
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

instance Epsilon (Computation r Double (D r Double)) (Computation r Double (D r Double)) where
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

instance Epsilon (Computation r Float (D r Float)) (Computation r Float (D r Float)) where
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

instance Epsilon (D r Double) (Computation r Double (D r Double)) where
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

instance Epsilon (D r Float) (Computation r Float (D r Float)) where
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

instance Epsilon (Computation r Double (D r Double)) (D r Double) where
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

instance Epsilon (Computation r Float (D r Float)) (D r Float) where
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

