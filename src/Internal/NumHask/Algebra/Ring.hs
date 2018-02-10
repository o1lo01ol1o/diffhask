{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}

-- | Ring classes. A distinguishment is made between Rings and Commutative Rings.
module Internal.NumHask.Algebra.Ring
  ( Semiring
  , Ring
  , CRing
  , StarSemiring(..)
  , KleeneAlgebra
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Distribution
import           Internal.NumHask.Algebra.Multiplicative
import           Protolude                               (Double, Float)

-- | Semiring
class ( MultiplicativeAssociative a
      , MultiplicativeUnital a
      , MultiplicativeAssociative b
      , MultiplicativeUnital b
      , Distribution a b
      ) =>
      Semiring a b

instance Semiring (D r Double) (D r Double)

instance Semiring (Computation r Double (D r Double)) (D r Double)

instance Semiring (D r Double) (Computation r Double (D r Double))

instance Semiring (D r Float) (D r Float)

instance Semiring (D r Float) (Computation r Float (D r Float))

instance Semiring (Computation r Float (D r Float)) (D r Float)

instance Semiring (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance Semiring (Computation r Float (D r Float)) (Computation r Float (D r Float))



-- | Ring
-- a summary of the laws inherited from the ring super-classes
--
-- > zero + a == a
-- > a + zero == a
-- > (a + b) + c == a + (b + c)
-- > a + b == b + a
-- > a - a = zero
-- > negate a = zero - a
-- > negate a + a = zero
-- > a + negate a = zero
-- > one `times` a == a
-- > a `times` one == a
-- > (a `times` b) `times` c == a `times` (b `times` c)
-- > a `times` (b + c) == a `times` b + a `times` c
-- > (a + b) `times` c == a `times` c + b `times` c
-- > a `times` zero == zero
-- > zero `times` a == zero
class ( Semiring a b
      , AdditiveGroup a b
      ) =>
      Ring a b

instance Ring (D r Double) (D r Double)

instance Ring (Computation r Double (D r Double)) (D r Double)

instance Ring (D r Double) (Computation r Double (D r Double))

instance Ring (D r Float) (D r Float)

instance Ring (D r Float) (Computation r Float (D r Float))

instance Ring (Computation r Float (D r Float)) (D r Float)

instance Ring (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance Ring (Computation r Float (D r Float)) (Computation r Float (D r Float))


-- | CRing is a Ring with Multiplicative Commutation.  It arises often due to '*' being defined as a multiplicative commutative operation.
class (Multiplicative a b, Ring a b) =>
      CRing a b

instance CRing (D r Double) (D r Double)

instance CRing (Computation r Double (D r Double)) (D r Double)

instance CRing (D r Double) (Computation r Double (D r Double))

instance CRing (D r Float) (D r Float)

instance CRing (D r Float) (Computation r Float (D r Float))

instance CRing (Computation r Float (D r Float)) (D r Float)

instance CRing (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance CRing (Computation r Float (D r Float)) (Computation r Float (D r Float))

-- | StarSemiring
--
-- > star a = one + a `times` star a
--
class ( Semiring a a
      , MultiplicativeUnital a
      , MultiplicativeUnital a
      , MultiplicativeMagma a (CodomainU a)
      , Additive a (CodomainU a)
      , Additive a a)
     =>
      StarSemiring a  where
  star :: a -> CodomainU a
  star a = (one :: a) + plus' a
  plus' :: a -> CodomainU a
  plus' a = a `times` star a

-- | KleeneAlgebra
--
-- > a `times` x + x = a ==> star a `times` x + x = x
-- > x `times` a + x = a ==> x `times` star a + x = x
--
class (StarSemiring a, StarSemiring b, AdditiveIdempotent a b) =>
      KleeneAlgebra a b
