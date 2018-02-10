{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
-- | 'Distribution' avoids a name clash with 'Data.Distributive'
module Internal.NumHask.Algebra.Distribution
  ( Distribution
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Multiplicative
import           Protolude                               (Double, Float)

-- | Distribution (and annihilation) laws
--
-- > a * (b + c) == a * b + a * c
-- > (a + b) * c == a * c + b * c
-- > a * zero == zero
-- > zero * a == zero
class (Additive a b, MultiplicativeMagma a b) =>
      Distribution a b

instance Distribution (D r Double) (D r Double)

instance Distribution (Computation r Double (D r Double)) (D r Double)

instance Distribution (D r Double) (Computation r Double (D r Double))

instance Distribution (D r Float) (D r Float)

instance Distribution (D r Float) (Computation r Float (D r Float))

instance Distribution (Computation r Float (D r Float)) (D r Float)

instance Distribution (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance Distribution (Computation r Float (D r Float)) (Computation r Float (D r Float))
