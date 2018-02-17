{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-#LANGUAGE TypeFamilies #-}
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
import           NumHask.Prelude                               (Double, Float)

-- | Semiring
class ( MultiplicativeAssociative a r t
      , MultiplicativeUnital a r t
      , MultiplicativeAssociative b r t
      , MultiplicativeUnital b r t
      , Distribution a b r t
      ) =>
      Semiring a b r t

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
class ( Semiring a b r t
      , AdditiveGroup a b r t
      ) =>
      Ring a b r t



-- | CRing is a Ring with Multiplicative Commutation.  It arises often due to '*' being defined as a multiplicative commutative operation.
class (Multiplicative a b r t, Ring a b r t) =>
      CRing a b r t

-- | StarSemiring
--
-- > star a = one + a `times` star a
--
class ( Semiring a a r t
      , MultiplicativeUnital a r t
      , MultiplicativeMagma a ( Computation r t (D r t)) r t
      , Additive a ( Computation r t (D r t)) r t
      , Additive a a r t)
     =>
      StarSemiring a r t where
  star :: ( (GetShape a ~ r )) => a -> Computation r t (D r t)
  star a = (one :: a) + plus' a
  plus' ::( (GetShape a ~ r )) => a ->  Computation r t (D r t)
  plus' a = a `times` star a

-- | KleeneAlgebra
--
-- > a `times` x + x = a ==> star a `times` x + x = x
-- > x `times` a + x = a ==> x `times` star a + x = x
--
class (StarSemiring a r t, StarSemiring b r t, AdditiveIdempotent a b r t) =>
      KleeneAlgebra a b r t

instance (BasisConstraints r Double) => Semiring (D r Double) (D r Double) r Double

instance (BasisConstraints r Double) => Semiring (Computation r Double (D r Double)) (D r Double) r Double

instance (BasisConstraints r Double) => Semiring (D r Double) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float) =>  Semiring (D r Float) (D r Float) r Float

instance (BasisConstraints r Float) =>  Semiring (D r Float) (Computation r Float (D r Float)) r Float

instance (BasisConstraints r Float) => Semiring (Computation r Float (D r Float)) (D r Float) r Float

instance (BasisConstraints r Double) => Semiring (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float) => Semiring (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float



instance (BasisConstraints r Double) =>  Ring (D r Double) (D r Double) r Double

instance (BasisConstraints r Double) => Ring (Computation r Double (D r Double)) (D r Double) r Double

instance (BasisConstraints r Double) =>  Ring (D r Double) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float) => Ring (D r Float) (D r Float) r Float

instance (BasisConstraints r Float) => Ring (D r Float) (Computation r Float (D r Float)) r Float

instance (BasisConstraints r Float) => Ring (Computation r Float (D r Float)) (D r Float) r Float

instance (BasisConstraints r Double) => Ring (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float) => Ring (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float

instance (BasisConstraints r Double) => CRing (D r Double) (D r Double) r Double

instance (BasisConstraints r Double) =>  CRing (Computation r Double (D r Double)) (D r Double) r Double

instance (BasisConstraints r Double) => CRing (D r Double) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float) => CRing (D r Float) (D r Float) r Float

instance (BasisConstraints r Float) => CRing (D r Float) (Computation r Float (D r Float)) r Float

instance (BasisConstraints r Float) => CRing (Computation r Float (D r Float)) (D r Float) r Float

instance (BasisConstraints r Double) =>  CRing (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float) => CRing (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float

