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

instance (P.Num a) => FfBin Add a r where
  {-#INLINE rff_bin #-}
  rff_bin _ a b = a .+. b
  {-#INLINE r_ff_bin #-}
  r_ff_bin _ a b = a .+ b
  {-#INLINE _ff_bin #-}
  _ff_bin _ a b = a +. b

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

instance (P.Num a) => FfBin Multiply a r where
  {-#INLINE rff_bin #-}
  rff_bin _ a b = a .*. b
  {-#INLINE r_ff_bin #-}
  r_ff_bin _ a b = a .* b
  {-#INLINE _ff_bin #-}
  _ff_bin _ a b = a *. b

-- | element by element division
--
-- > a ./. a == singleton one
class (MultiplicativeGroup a b r t ) =>
      MultiplicativeGroupBasis r a b t where
  infixl 7 ./.
  (./.) :: a -> b -> Computation r t (D r t)

instance (P.Num a) => FfBin Divide a r where
  {-#INLINE rff_bin #-}
  rff_bin _ a b = a ./. b
  {-#INLINE r_ff_bin #-}
  r_ff_bin _ a b = a ./ b
  {-#INLINE _ff_bin #-}
  _ff_bin _ a b = a /. b

