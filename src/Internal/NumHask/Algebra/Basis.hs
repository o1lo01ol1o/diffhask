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
import Internal.Internal

-- | element by element addition
--
-- > (a .+. b) .+. c == a .+. (b .+. c)
-- > zero .+. a = a
-- > a .+. zero = a
-- > a .+. b == b .+. a
class (Additive a b r t) =>
      AdditiveBasis r a b t where
  infixl 7 .+.
  (.+.) :: a -> b -> Computation r t (D r t)

-- | element by element subtraction
--
-- > a .-. a = singleton zero
class (AdditiveGroup a b r t ) =>
      AdditiveGroupBasis r a b t where
  infixl 6 .-.
  (.-.) :: a -> b -> Computation r t (D r t)

-- | element by element multiplication
--
-- > (a .*. b) .*. c == a .*. (b .*. c)
-- > singleton one .*. a = a
-- > a .*. singelton one = a
-- > a .*. b == b .*. a
class (Multiplicative a b  r t) =>
      MultiplicativeBasis r a b t where
  infixl 7 .*.
  (.*.) :: a -> b -> Computation r t (D r t)

-- | element by element division
--
-- > a ./. a == singleton one
class (MultiplicativeGroup a b r t ) =>
      MultiplicativeGroupBasis r a b t where
  infixl 7 ./.
  (./.) :: a -> b -> Computation r t (D r t)



