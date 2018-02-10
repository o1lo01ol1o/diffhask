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
class (Additive a b, r ~ DomainArr(Domains a b)) =>
      AdditiveBasis a b r  where
  infixl 7 .+.
  (.+.) :: a -> b -> CodomainB a b

-- | element by element subtraction
--
-- > a .-. a = singleton zero
class (AdditiveGroup a b, r ~ DomainArr(Domains a b) ) =>
      AdditiveGroupBasis a b r where
  infixl 6 .-.
  (.-.) :: a -> b -> CodomainB a b

-- | element by element multiplication
--
-- > (a .*. b) .*. c == a .*. (b .*. c)
-- > singleton one .*. a = a
-- > a .*. singelton one = a
-- > a .*. b == b .*. a
class (Multiplicative a b, r ~ DomainArr(Domains a b) ) =>
      MultiplicativeBasis a b r  where
  infixl 7 .*.
  (.*.) :: a -> b -> CodomainB a b

-- | element by element division
--
-- > a ./. a == singleton one
class (MultiplicativeGroup a b, r ~ DomainArr(Domains a b) ) =>
      MultiplicativeGroupBasis a b r where
  infixl 7 ./.
  (./.) :: a -> b -> CodomainB a b



