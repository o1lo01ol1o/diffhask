{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
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
import           NumHask.Prelude                         (Double, Float)

-- | Distribution (and annihilation) laws
--
-- > a * (b + c) == a * b + a * c
-- > (a + b) * c == a * c + b * c
-- > a * zero == zero
-- > zero * a == zero
class (Additive a b r t, MultiplicativeMagma a b r t) =>
      Distribution a b r t

instance (BasisConstraints r Double ) => Distribution (D r Double) (D r Double) r Double

instance (BasisConstraints r Double ) => Distribution (Computation r Double (D r Double)) (D r Double) r Double

instance (BasisConstraints r Double ) => Distribution (D r Double) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float ) => Distribution (D r Float) (D r Float) r Float

instance (BasisConstraints r Float ) =>  Distribution (D r Float) (Computation r Float (D r Float)) r Float

instance (BasisConstraints r Float ) =>  Distribution (Computation r Float (D r Float)) (D r Float) r Float

instance (BasisConstraints r Double ) => Distribution (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance (BasisConstraints r Float ) =>  Distribution (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float


