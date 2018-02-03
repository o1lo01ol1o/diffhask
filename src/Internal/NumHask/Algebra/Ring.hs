{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}

-- | Ring classes. A distinguishment is made between Rings and Commutative Rings.
module Internal.NumHask.Algebra.Ring
  ( Semiring
  , Ring
  , CRing
  , StarSemiring(..)
  , KleeneAlgebra
  ) where

import Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Distribution
import           Internal.NumHask.Algebra.Multiplicative
import           Protolude                      (Double, Float)

-- | Semiring
class (MultiplicativeAssociative a t, MultiplicativeUnital a t, MultiplicativeAssociative b t, MultiplicativeUnital b t, Distribution a b t) =>
      Semiring a b t | a b -> t, a -> t, b -> t

instance Semiring (D Double) (D Double) Double

instance Semiring (Computation Double (D Double)) (D Double) Double

instance Semiring (D Double) (Computation Double (D Double)) Double

instance Semiring (D Float) (D Float) Float

instance Semiring (D Float) (Computation Float (D Float)) Float

instance Semiring (Computation Float (D Float)) (D Float) Float

instance Semiring (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Semiring (Computation Float (D Float)) (Computation Float (D Float)) Float



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
class ( Semiring a b t
      , AdditiveGroup a b t
      ) =>
      Ring a b t | a b -> t, a -> t, b -> t

instance Ring (D Double) (D Double) Double

instance Ring (Computation Double (D Double)) (D Double) Double

instance Ring (D Double) (Computation Double (D Double)) Double

instance Ring (D Float) (D Float) Float

instance Ring (D Float) (Computation Float (D Float)) Float

instance Ring (Computation Float (D Float)) (D Float) Float

instance Ring (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Ring (Computation Float (D Float)) (Computation Float (D Float)) Float


-- | CRing is a Ring with Multiplicative Commutation.  It arises often due to '*' being defined as a multiplicative commutative operation.
class (Multiplicative a b t, Ring a b t) =>
      CRing a b t | a b -> t, a -> t, b -> t

instance CRing (D Double) (D Double) Double

instance CRing (Computation Double (D Double)) (D Double) Double

instance CRing (D Double) (Computation Double (D Double)) Double

instance CRing (D Float) (D Float) Float

instance CRing (D Float) (Computation Float (D Float)) Float

instance CRing (Computation Float (D Float)) (D Float) Float

instance CRing (Computation Double (D Double)) (Computation Double (D Double)) Double

instance CRing (Computation Float (D Float)) (Computation Float (D Float)) Float

-- | StarSemiring
--
-- > star a = one + a `times` star a
--
class ( Semiring a a t
      , MultiplicativeUnital a t
      , MultiplicativeUnital (D a) t
      , MultiplicativeMagma a (Computation t (D t)) t
      , Additive a (Computation t (D t)) t
      , Additive (D a) (Computation t (D t)) t
      ) =>
      StarSemiring a t | a -> t where
  star :: a -> Computation t (D t)
  star a = (one :: D a) + plus' a
  plus' :: a -> Computation t (D t)
  plus' a = a `times` star a

-- | KleeneAlgebra
--
-- > a `times` x + x = a ==> star a `times` x + x = x
-- > x `times` a + x = a ==> x `times` star a + x = x
--
class (StarSemiring a t, StarSemiring b t, AdditiveIdempotent a b t) => KleeneAlgebra a b t

