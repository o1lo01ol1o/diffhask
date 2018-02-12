{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# OPTIONS_GHC -Wall #-}

-- | Element-by-element operation for 'Representable's
module Internal.NumHask.Algebra.Basis
  ( AdditiveBasis(..)
  , AdditiveGroupBasis(..)
  , MultiplicativeBasis(..)
  , MultiplicativeGroupBasis(..)
  ) where

import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Multiplicative
import Internal.NumHask.Algebra.Module
import Internal.Internal







