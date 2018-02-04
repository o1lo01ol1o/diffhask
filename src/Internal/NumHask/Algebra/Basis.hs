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
  , AdditiveBoxBasis(..)
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
class (Additive a b t) =>
      AdditiveBasis a b m t | a b -> t, a -> t, b -> t where
  infixl 7 .+.
  (.+.) :: a -> b -> Computation t (D (m t))

-- | element by element subtraction
--
-- > a .-. a = singleton zero
class (AdditiveGroup a b t) =>
      AdditiveGroupBasis a b m t | a b -> t, a -> t, b -> t where
  infixl 6 .-.
  (.-.) :: a -> b -> Computation t (D (m t))

-- | element by element multiplication
--
-- > (a .*. b) .*. c == a .*. (b .*. c)
-- > singleton one .*. a = a
-- > a .*. singelton one = a
-- > a .*. b == b .*. a
class (Multiplicative a b t) =>
      MultiplicativeBasis a b m t | a b -> t, a -> t, b -> t where
  infixl 7 .*.
  (.*.) :: a -> b -> Computation t (D (m t))

-- | element by element division
--
-- > a ./. a == singleton one
class (MultiplicativeGroup a b t) =>
      MultiplicativeGroupBasis a b m t | a b -> t, a -> t, b -> t where
  infixl 7 ./.
  (./.) :: a -> b -> Computation t (D (m t))

-- data M

-- instance (AdditiveBasis (D (r a)) (D (r a)) r a) => CDelta (D (r a)) a where
--   data Delta a M = M (D (r a))


