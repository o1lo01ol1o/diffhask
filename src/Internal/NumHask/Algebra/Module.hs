{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wall #-}

-- | Algebra for Representable numbers
module Internal.NumHask.Algebra.Module
  ( AdditiveModule(..)
  , AdditiveGroupModule(..)
  , MultiplicativeModule(..)
  , MultiplicativeGroupModule(..)
  , Banach(..)
  , Hilbert(..)
  , type (><)
  , TensorProduct(..)
  , AdditiveBoxModule(..)
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Field
import           Internal.NumHask.Algebra.Metric
import           Internal.NumHask.Algebra.Multiplicative
import           Internal.NumHask.Algebra.Ring
import           Protolude                               (Double, Float, Int,
                                                          Integer)





-- | Additive Module Laws
--
-- > (a + b) .+ c == a + (b .+ c)
-- > (a + b) .+ c == (a .+ c) + b
-- > a .+ zero == a
-- > a .+ b == b +. a
class (Additive a b, r ~ DomainArr(Domains a b)) =>
      AdditiveModule r a b where
  infixl 6 .+
  (.+) ::  a -> b -> CodomainB a b
  infixl 6 +.
  (+.) :: a -> b -> CodomainB a b


-- | Subtraction Module Laws
--
-- > (a + b) .- c == a + (b .- c)
-- > (a + b) .- c == (a .- c) + b
-- > a .- zero == a
-- > a .- b == negate b +. a
class (AdditiveGroup a b, AdditiveModule r a b, r ~ DomainArr(Domains a b)) =>
      AdditiveGroupModule r a b where
  infixl 6 .-
  (.-) ::  a -> b -> CodomainB a b
  infixl 6 -.
  (-.) ::   a -> b -> CodomainB a b

-- | Multiplicative Module Laws
--
-- > a .* one == a
-- > (a + b) .* c == (a .* c) + (b .* c)
-- > c *. (a + b) == (c *. a) + (c *. b)
-- > a .* zero == zero
-- > a .* b == b *. a
class (Multiplicative a b, r ~ DomainArr(Domains a b)) =>
      MultiplicativeModule r a b where
  infixl 7 .*
  (.*) ::  a -> b -> CodomainB a b
  infixl 7 *.
  (*.) ::  a -> b -> CodomainB a b

-- | Division Module Laws
--
-- > nearZero a || a ./ one == a
-- > b == zero || a ./ b == recip b *. a
class (MultiplicativeGroup a b, MultiplicativeModule r a b, r ~ DomainArr(Domains a b)) =>
      MultiplicativeGroupModule r a b where
  infixl 7 ./
  (./) ::  a -> b -> CodomainB a b
  infixl 7 /.
  (/.) ::  a -> b -> CodomainB a b

-- | Banach (with Norm) laws form rules around size and direction of a number, with a potential crossing into another codomain.
--
-- > a == singleton zero || normalize a *. size a == a
class ( ExpField a
      , Normed  a
      , MultiplicativeGroupModule r a a, r ~ DomainArr(Domains a b)
      ) =>
      Banach r a where
  normalize ::
       (Normed a )
    => a
    -> CodomainU a
  normalize a = a ./ size a

-- | the inner product of a representable over a semiring
--
-- > a <.> b == b <.> a
-- > a <.> (b +c) == a <.> b + a <.> c
-- > a <.> (s *. b + c) == s * (a <.> b) + a <.> c
-- (s0 *. a) <.> (s1 *. b) == s0 * s1 * (a <.> b)
class (Semiring a b, r ~ DomainArr(Domains a b)) =>
      Hilbert r a b where
  infix 8 <.>
  (<.>) ::
     a
    -> b
    -> CodomainB a b

-- | tensorial type
type family (><) (a :: k1) (b :: k2) :: *

type instance Int >< Int = Int

type instance Integer >< Integer = Integer

type instance Double >< Double = Double

type instance Float >< Float = Float

-- | representation synthesis
type family TensorRep k1 k2 where
  TensorRep (r a) (r a) = r (r a)
  TensorRep (r a) (s a) = r (s a)
  TensorRep (r a) a = r a

type instance r a >< b = TensorRep (r a) b

-- | generalised outer product
--
-- > a><b + c><b == (a+c) >< b
-- > a><b + a><c == a >< (b+c)
--
-- todo: work out why these laws down't apply
-- > a *. (b><c) == (a><b) .* c
-- > (a><b) .* c == a *. (b><c)
class TensorProduct a where
  infix 8 ><
  (><) :: a -> a -> (a >< a)
  outer :: a -> a -> (a >< a)
  outer = (><)
  timesleft :: a -> (a >< a) -> a
  timesright :: (a >< a) -> a -> a
