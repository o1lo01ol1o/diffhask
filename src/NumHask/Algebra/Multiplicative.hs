{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}

-- | A magma heirarchy for multiplication. The basic magma structure is repeated and prefixed with 'Multiplicative-'.
module NumHask.Algebra.Multiplicative
  ( MultiplicativeMagma(..)
  , MultiplicativeUnital(..)
  , MultiplicativeAssociative
  , MultiplicativeCommutative
  , MultiplicativeInvertible(..)
  , product
  , Multiplicative(..)
  , MultiplicativeRightCancellative(..)
  , MultiplicativeLeftCancellative(..)
  , MultiplicativeGroup(..)
  ) where


import           Core                     hiding (negate, one, signum, zero,
                                           (*), (+), (-), (/))
import           NumHask.Algebra.Additive
import           Protolude                (Bool (..), Double, Float, Int,
                                           Integer)
import qualified Protolude                as P

-- | 'times' is used as the operator for the multiplicative magam to distinguish from '*' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `times` b ∈ A
--
-- law is true by construction in Haskell
class MultiplicativeMagma a b t | a b -> t, a -> t, b -> t where
  times :: a -> b -> Computation t (D t)

instance MultiplicativeMagma (Computation Float (D Float)) (Computation Float (D Float)) Float where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance MultiplicativeMagma (Computation Float (D Float)) (D Float) Float where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance MultiplicativeMagma (D Float) (Computation Float (D Float)) Float where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance MultiplicativeMagma (D Float) (D Float) Float where
  times = binOp Multiply


instance MultiplicativeMagma (Computation Double (D Double)) (Computation Double (D Double)) Double where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance MultiplicativeMagma (Computation Double (D Double)) (D Double) Double where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance MultiplicativeMagma (D Double) (Computation Double (D Double)) Double where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance MultiplicativeMagma (D Double) (D Double) Double where
  times = binOp Multiply

-- | Unital magma for multiplication.
--
-- > one `times` a == a
-- > a `times` one == a
class MultiplicativeMagma a a t=>
      MultiplicativeUnital a t | a -> t where
  one :: a

instance MultiplicativeUnital (D Double) Double where
  one = D 1

instance MultiplicativeUnital  (D Float) Float where
  one = D 1

instance MultiplicativeUnital  (Computation Double (D Double)) Double where
  one = P.pure P.$ D 1

instance MultiplicativeUnital (Computation Float (D Float)) Float where
  one = P.pure P.$ D 1


-- | Associative magma for multiplication.
--
-- > (a `times` b) `times` c == a `times` (b `times` c)
class MultiplicativeMagma a a t=>
      MultiplicativeAssociative a t | a -> t

instance MultiplicativeAssociative (D Double) Double

instance MultiplicativeAssociative (D Float) Float

instance MultiplicativeAssociative (Computation Float (D Float)) Float

instance MultiplicativeAssociative (Computation Double (D Double)) Double


-- | Commutative magma for multiplication.
--
-- > a `times` b == b `times` a
class MultiplicativeMagma a a t =>
      MultiplicativeCommutative a t | a -> t

instance MultiplicativeCommutative (D Double) Double

instance MultiplicativeCommutative (D Float) Float

instance MultiplicativeCommutative (Computation Float (D Float)) Float

instance MultiplicativeCommutative (Computation Double (D Double)) Double

-- | Invertible magma for multiplication.
--
-- > ∀ a ∈ A: recip a ∈ A
--
-- law is true by construction in Haskell
class MultiplicativeMagma a a t =>
      MultiplicativeInvertible a t | a -> t where
  recip :: a -> Computation t (D t)

instance MultiplicativeInvertible (D Double) Double where
  recip = binOp Divide one

instance MultiplicativeInvertible (D Float) Float where
  recip = binOp Divide one

instance MultiplicativeInvertible  (Computation Double (D Double)) Double where
  recip a = do
    aa <- a
    binOp Divide one aa

instance MultiplicativeInvertible (Computation Float (D Float)) Float where
  recip a = do
    aa <- a
    binOp Divide one aa

-- | Idempotent magma for multiplication.
--
-- > a `times` a == a
class MultiplicativeMagma a a t=>
      MultiplicativeIdempotent a t | a -> t


-- | product definition avoiding a clash with the Product monoid in base
--
product ::
     ( Multiplicative a (Computation t (D t)) t
     , P.Foldable f
     , MultiplicativeUnital (Computation t (D t)) t
     )
  => f a
  -> Computation t (D t)
product = P.foldr (*) one

-- | Multiplicative is commutative, associative and unital under multiplication
--
-- > one * a == a
-- > a * one == a
-- > (a * b) * c == a * (b * c)
-- > a * b == b * a
class ( MultiplicativeCommutative a t
      , MultiplicativeCommutative b t
      , MultiplicativeUnital a t
      , MultiplicativeUnital b t
      , MultiplicativeMagma a b t
      , MultiplicativeAssociative a t
      , MultiplicativeAssociative b t
      ) =>
      Multiplicative a b t | a b -> t, a -> t, b -> t where
  infixl 7 *
  (*) :: a -> b -> Computation t (D t)
  a * b = times a b

instance Multiplicative (D Double) (D Double) Double

instance Multiplicative (Computation Double (D Double)) (D Double) Double

instance Multiplicative (D Double) (Computation Double (D Double)) Double

instance Multiplicative (D Float) (D Float) Float

instance Multiplicative (D Float) (Computation Float (D Float)) Float

instance Multiplicative (Computation Float (D Float)) (D Float) Float

instance Multiplicative (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Multiplicative (Computation Float (D Float)) (Computation Float (D Float)) Float-- | Non-commutative left divide
--
-- > recip a `times` a = one
class ( MultiplicativeUnital a t
      , MultiplicativeAssociative a t
      , MultiplicativeInvertible a t
      , MultiplicativeUnital b t
      , MultiplicativeMagma (Computation t (D t)) a t
      , MultiplicativeAssociative b t
      , MultiplicativeInvertible b t
      ) =>
      MultiplicativeLeftCancellative a b t | a b -> t, a -> t, b -> t where
  infixl 7 ~/
  (~/) :: a -> b -> Computation t (D t)
  a ~/ b = recip b `times` a

-- | Non-commutative right divide
--
-- > a `times` recip a = one
class ( MultiplicativeUnital a t
      , MultiplicativeAssociative a t
      , MultiplicativeInvertible a t
      , MultiplicativeUnital b t
      , MultiplicativeMagma a (Computation t (D t)) t
      , MultiplicativeAssociative b t
      , MultiplicativeInvertible b t
      ) =>
      MultiplicativeRightCancellative a b t | a b -> t, a -> t, b -> t where
  infixl 7 /~
  (/~) :: a -> b -> Computation t (D t)
  a /~ b = a `times` recip b

-- | Divide ('/') is reserved for where both the left and right cancellative laws hold.  This then implies that the MultiplicativeGroup is also Abelian.
--
-- > a / a = one
-- > recip a = one / a
-- > recip a * a = one
-- > a * recip a = one
class ( Multiplicative a b t
      , MultiplicativeInvertible a t
      , MultiplicativeInvertible b t
      , MultiplicativeMagma a (Computation t (D t)) t
      ) =>
      MultiplicativeGroup a b t | a b -> t, a -> t, b -> t where
  infixl 7 /
  (/) :: a -> b -> Computation t (D t)
  (/) a b = a `times` recip b

instance MultiplicativeGroup (D Double) (D Double) Double

instance MultiplicativeGroup (Computation Double (D Double)) (D Double) Double

instance MultiplicativeGroup (D Double) (Computation Double (D Double)) Double

instance MultiplicativeGroup (D Float) (D Float) Float

instance MultiplicativeGroup (D Float) (Computation Float (D Float)) Float

instance MultiplicativeGroup (Computation Float (D Float)) (D Float) Float

instance MultiplicativeGroup (Computation Double (D Double)) (Computation Double (D Double)) Double

instance MultiplicativeGroup (Computation Float (D Float)) (Computation Float (D Float)) Float

