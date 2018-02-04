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
class (MultiplicativeUnital a t) =>
      Signed a t  | a -> t where
  sign :: a -> Computation t (D t) 
  abs :: a -> Computation t (D t) 

data Abs = Abs deriving P.Show 

instance Signed (D Double) Double where
  sign a =
    if a >= zero
      then one
      else negate (one :: D Double)
  abs = monOp Abs

instance Signed (D Float) Float where
  sign a =
    if a >= zero
      then one
      else negate (one :: D Float)
  abs =  monOp Abs

instance Signed (Computation Double (D Double)) Double where
  sign a = do
    ca <- a
    if ca >= (zero :: (D Double))
      then one
      else negate (one :: D Double)
  abs a = do
    ca <- a
    monOp Abs ca

instance Signed (Computation Float (D Float)) Float  where
  sign a = do
    ca <- a
    if ca >= zero
      then one
      else negate (one :: D Float)
  abs a =  do
    ca <- a
    monOp Abs ca


-- | Abs
--  compute $ diff' abs a
-- (D 3.0, D 1.0)
instance ( ScalarInABox a, Signed (D a) a, AdditiveUnital (D a) a, AdditiveInvertible (D a) a, P.Ord a, Multiplicative (D a) (Computation a (D a)) a
         ) =>
         MonOp Abs a where
  {-# INLINE ff #-}
  ff _ a = P.abs a
  {-# INLINE fd #-}
  fd _ a =
    if a >= (zero :: D a)
      then P.pure a
      else monOp Negate a
  {-# INLINE df #-}
  df _ _ ap at = at * sign ap


instance (Signed (D a) a, ScalarInABox a, Multiplicative (D a) (D a) a) => Trace Abs a where
  pushEl (U _ a) dA = do
    sp <-  sign (p a)
    dl <- dA * sp
    P.pure [(X dl, X a)]
  resetEl (U _ a ) = P.pure [X a]

-- | Like Signed, except the codomain can be different to the domain.
class Normed a t | a -> t where
  size :: a -> Computation t (D t)

instance Normed (D Double) Double where
  size = abs

instance Normed (D Float) Float where
  size = abs

instance Normed (Computation Double (D Double)) Double where
  size = abs

instance Normed (Computation Float (D Float)) Float where
  size = abs

-- | distance between numbers
--
-- > distance a b >= zero
-- > distance a a == zero
-- > \a b c -> distance a c + distance b c - distance a b >= zero &&
-- >           distance a b + distance b c - distance a c >= zero &&
-- >           distance a b + distance a c - distance b c >= zero &&
class Metric a b t | a -> t, b -> t, a b -> t where
  distance :: a -> b -> Computation t (D t)

instance Metric (D Double) (D Double) Double where
  distance a b = abs (a - b)

instance Metric (D Float) (D Float) Float  where
  distance a b = abs (a - b)

instance Metric (Computation Double (D Double)) (Computation Double (D Double)) Double where
  distance a b = abs (a - b)

instance Metric (Computation Float (D Float)) (Computation Float (D Float)) Float where
  distance a b = abs (a - b)

instance Metric (D Double) (Computation Double (D Double)) Double where
  distance a b = abs (a - b)

instance Metric (D Float) (Computation Float (D Float)) Float where
  distance a b = abs (a - b)

instance Metric (Computation Double (D Double)) (D Double) Double where
  distance a b = abs (a - b)

instance Metric (Computation Float (D Float)) (D Float) Float where
  distance a b = abs (a - b)


-- | todo: This should probably be split off into some sort of alternative Equality logic, but to what end?
class (AdditiveGroup a b t) =>
      Epsilon a b t where
  nearZero :: (a ~ c, b ~ c) => c -> Computation t (Bool)
  aboutEqual :: a -> b -> Computation t (Bool)
  positive :: (a ~ c, b ~ c, Eq c, Signed c t) => c -> Computation t (Bool)
  veryPositive ::
       (a ~ c, b ~ c, Eq c, Signed c t) => c -> Computation t (Bool)
  veryNegative ::
       (a ~ c, b ~ c, Eq c, Signed c t) => c -> Computation t (Bool)
  

infixl 4 ≈

-- | todo: is utf perfectly acceptable these days?
(≈) :: (Epsilon a b t) => a -> b -> Computation t (Bool)
(≈) = aboutEqual

instance Epsilon (D Double) (D Double) Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D Double))
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

instance Epsilon (D Float) (D Float) Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D Float))
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

instance Epsilon (Computation Double (D Double)) (Computation Double (D Double)) Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D Double))
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

instance Epsilon (Computation Float (D Float)) (Computation Float (D Float)) Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D Float))
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

instance Epsilon (D Double) (Computation Double (D Double)) Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D Double))
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

instance Epsilon (D Float) (Computation Float (D Float)) Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D Float))
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

instance Epsilon (Computation Double (D Double)) (D Double) Double where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-12 :: D Double))
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

instance Epsilon (Computation Float (D Float)) (D Float) Float where
  nearZero a = do
    ca <- abs a
    P.pure (ca <= (D 1e-6 :: D Float))
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

