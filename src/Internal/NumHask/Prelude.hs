{-# OPTIONS_GHC -Wall #-}
{-#LANGUAGE NoImplicitPrelude#-}
-- | A prelude for NumHask
module Internal.NumHask.Prelude
  ( -- * Backend
    -- $backend
    module Protolude

    -- * Algebraic Heirarchy
    -- $instances
  , module Internal.NumHask.Algebra.Additive
 
  -- , module Internal.NumHask.Algebra.Distribution
  -- , module Internal.NumHask.Algebra.Field
 
  -- , module Internal.NumHask.Algebra.Magma
  -- , module Internal.NumHask.Algebra.Metric
  -- , module Internal.NumHask.Algebra.Module
  -- , module Internal.NumHask.Algebra.Multiplicative
  -- , module Internal.NumHask.Algebra.Ring
  -- , module Internal.NumHask.Algebra.Singleton


  ) where

import Protolude
       hiding (Bounded(..), Integral(..), Rep, Semiring(..), (*), (**),
               (+), (-), (/), (^), (^^), abs, acos, acosh, asin, asinh, atan,
               atan2, atanh, ceiling, cos, cosh, exp, floor, fromInteger,
               fromIntegral, infinity, isNaN, log, logBase, negate, pi, product,
               recip, round, sin, sinh, sqrt, sum, tan, tanh, toInteger, trans,
               zero)

import Internal.NumHask.Algebra.Additive
import Internal.Internal
import qualified NumHask.Array as A
-- import Internal.NumHask.Algebra.Distribution
-- import Internal.NumHask.Algebra.Field

-- import Internal.NumHask.Algebra.Magma
-- import Internal.NumHask.Algebra.Metric
-- import Internal.NumHask.Algebra.Module
-- import Internal.NumHask.Algebra.Multiplicative
-- import Internal.NumHask.Algebra.Ring
-- import Internal.NumHask.Algebra.Singleton


-- $backend
-- NumHask imports Protolude as the prelude and replaces much of the 'Num' heirarchy in base.
-- Usage of 'Semigroup' and 'Monoid' has been avoided to retain basic compatability.
-- $instances
-- Re-defines the numeric tower.
--
-- Instances for 'Int', 'Integer', 'Float', 'Double', 'Bool' and 'Complex' are supplied.
--
