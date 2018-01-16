{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
-- | 'Distribution' avoids a name clash with 'Data.Distributive'
module NumHask.Algebra.Distribution
  ( Distribution
  ) where

import           Core                           (Computation, D (..))
import           NumHask.Algebra.Additive
import           NumHask.Algebra.Multiplicative
import           Protolude                      (Double, Float)

-- | Distribution (and annihilation) laws
--
-- > a * (b + c) == a * b + a * c
-- > (a + b) * c == a * c + b * c
-- > a * zero == zero
-- > zero * a == zero
class (Additive a b t, MultiplicativeMagma a b t) =>
      Distribution a b t | a b -> t, a -> t, b -> t

instance Distribution (D Double) (D Double) Double

instance Distribution (Computation Double (D Double)) (D Double) Double

instance Distribution (D Double) (Computation Double (D Double)) Double

instance Distribution (D Float) (D Float) Float

instance Distribution (D Float) (Computation Float (D Float)) Float

instance Distribution (Computation Float (D Float)) (D Float) Float

instance Distribution (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Distribution (Computation Float (D Float)) (Computation Float (D Float)) Float
