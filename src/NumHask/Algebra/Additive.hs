{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}

-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- | A magma heirarchy for addition. The basic magma structure is repeated and prefixed with 'Additive-'.
module NumHask.Algebra.Additive
  ( AdditiveMagma(..)
  , AdditiveUnital(..)
  , AdditiveAssociative
  , AdditiveCommutative
  , AdditiveInvertible(..)
  , AdditiveIdempotent
  , sum
  , Additive(..)
  , AdditiveRightCancellative(..)
  , AdditiveLeftCancellative(..)
  , AdditiveGroup(..)
  ) where
import           Core      hiding (negate, signum, zero, (*), (+), (-), (/))
import           Protolude (Bool (..), Double, Float, Int, Integer)
import qualified Protolude as P

-- | 'plus' is used as the operator for the additive magma to distinguish from '+' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `plus` b ∈ A
--
-- law is true by construction in Haskell
class AdditiveMagma a b t | a b -> t, a -> t, b -> t where
  plus :: a -> b -> Computation t (D t)

instance AdditiveMagma (Computation Float (D Float)) (Computation Float (D Float)) Float where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance AdditiveMagma (Computation Float (D Float)) (D Float) Float where
  plus a b = do
    aa <- a
    binOp Add aa b

instance AdditiveMagma (D Float) (Computation Float (D Float)) Float where
  plus a b = do
    bb <- b
    binOp Add a bb

instance AdditiveMagma (D Float) (D Float) Float where
  plus= binOp Add


instance AdditiveMagma (Computation Double (D Double)) (Computation Double (D Double)) Double where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance AdditiveMagma (Computation Double (D Double)) (D Double) Double where
  plus a b = do
    aa <- a
    binOp Add aa b

instance AdditiveMagma (D Double) (Computation Double (D Double)) Double where
  plus a b = do
    bb <- b
    binOp Add a bb

instance AdditiveMagma (D Double) (D Double) Double where
  plus = binOp Add



-- | Unital magma for addition.
--
-- > zero `plus` a == a
-- > a `plus` zero == a
class AdditiveMagma a a t =>
      AdditiveUnital a t | a -> t where
  zero :: a

instance AdditiveUnital (D Double) Double where
  zero = D 0

instance AdditiveUnital  (D Float) Float where
  zero = D 0

instance AdditiveUnital  (Computation Double (D Double)) Double where
  zero = P.pure P.$ D 0

instance AdditiveUnital (Computation Float (D Float)) Float where
  zero = P.pure P.$ D 0


-- | Associative magma for addition.
--
-- > (a `plus` b) `plus` c == a `plus` (b `plus` c)
class AdditiveMagma a b t=>
      AdditiveAssociative a b t | a b -> t, a -> t, b -> t

instance AdditiveAssociative (D Double) (D Double) Double

instance AdditiveAssociative (Computation Double (D Double)) (D Double) Double

instance AdditiveAssociative (D Double) (Computation Double (D Double)) Double

instance AdditiveAssociative (D Float) (D Float) Float

instance AdditiveAssociative (D Float) (Computation Float (D Float)) Float

instance AdditiveAssociative (Computation Float (D Float)) (D Float) Float

instance AdditiveAssociative (Computation Double (D Double)) (Computation Double (D Double)) Double

instance AdditiveAssociative (Computation Float (D Float)) (Computation Float (D Float)) Float


-- | Commutative magma for addition.
--
-- > a `plus` b == b `plus` a
class AdditiveMagma a b t =>
      AdditiveCommutative a b t | a b -> t, a -> t, b -> t

instance AdditiveCommutative (D Double) (D Double) Double

instance AdditiveCommutative (D Float) (D Float) Float

instance AdditiveCommutative (Computation Double (D Double)) (Computation Double (D Double)) Double

instance AdditiveCommutative (D Double) (Computation Double (D Double)) Double

instance AdditiveCommutative (Computation Double (D Double))  (D Double) Double

instance AdditiveCommutative (Computation Float (D Float)) (Computation Float (D Float)) Float

instance AdditiveCommutative (D Float) (Computation Float (D Float)) Float

instance AdditiveCommutative (Computation Float (D Float)) (D Float) Float


-- | Invertible magma for addition.
--
-- > ∀ a ∈ A: negate a ∈ A
--
-- law is true by construction in Haskell
class AdditiveMagma a a t =>
      AdditiveInvertible a t | a -> t where
  negate :: a -> Computation t (D t)

instance AdditiveInvertible (Computation Double (D Double)) Double where
  negate a = do
    aa <- a
    monOp Negate aa

instance AdditiveInvertible  (Computation Float (D Float)) Float where
  negate a = do
    aa <- a
    monOp Negate aa

instance AdditiveInvertible  (D Double) Double where
  negate = monOp Negate

instance AdditiveInvertible   (D Float) Float where
  negate = monOp Negate

-- | Idempotent magma for addition.
--
-- > a `plus` a == a
class AdditiveMagma a b t=>
      AdditiveIdempotent a b t

-- | sum definition avoiding a clash with the Sum monoid in base
-- >>> compute P.$ sum [ D 2.0 :: D Float, D 3.0]
-- D 5.0
sum ::
     ( Additive a (Computation t (D t)) t
     , P.Foldable f
     , AdditiveUnital (Computation t (D t)) t
     )
  => f a
  -> Computation t (D t)
sum = P.foldr (+) zero

-- | Additive is commutative, unital and associative under addition
--
-- > zero + a == a
-- > a + zero == a
-- > (a + b) + c == a + (b + c)
-- > a + b == b + a
class ( AdditiveCommutative a b t
      , AdditiveUnital a t
      , AdditiveUnital b t
      , AdditiveAssociative a b t
      ) =>
      Additive a b t | a b -> t, a -> t, b -> t where
  infixl 6 +
  (+) :: a -> b -> Computation t (D t)
  a + b = plus a b

instance Additive (D Double) (D Double) Double

instance Additive (Computation Double (D Double)) (D Double) Double

instance Additive (D Double) (Computation Double (D Double)) Double

instance Additive (D Float) (D Float) Float

instance Additive (D Float) (Computation Float (D Float)) Float

instance Additive (Computation Float (D Float)) (D Float) Float

instance Additive (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Additive (Computation Float (D Float)) (Computation Float (D Float)) Float

-- | Non-commutative left minus
--
-- > negate a `plus` a = zero
class ( AdditiveMagma a b t
      , AdditiveMagma (Computation t (D t)) a t
      , AdditiveUnital b t
      , AdditiveAssociative a b t
      , AdditiveAssociative b a t
      , AdditiveInvertible b t
      ) =>
      AdditiveLeftCancellative a b t | a b -> t, a -> t, b -> t where
  infixl 6 ~-
  (~-) :: a -> b -> Computation t (D t)
  (~-) a b = negate b `plus` a

-- | Non-commutative right minus
--
-- > a `plus` negate a = zero
class ( AdditiveUnital b t
      , AdditiveMagma a (Computation t (D t)) t
      , AdditiveAssociative a b t
      , AdditiveInvertible b t
      ) =>
      AdditiveRightCancellative a b t | a b -> t, a -> t, b -> t where
  infixl 6 -~
  (-~) :: a -> b -> Computation t (D t)
  (-~) a b = a `plus` negate b

-- | Minus ('-') is reserved for where both the left and right cancellative laws hold.  This then implies that the AdditiveGroup is also Abelian.
--
-- Syntactic unary negation - substituting "negate a" for "-a" in code - is hard-coded in the language to assume a Num instance.  So, for example, using ''-a = zero - a' for the second rule below doesn't work.
--
-- > a - a = zero
-- > negate a = zero - a
-- > negate a + a = zero
-- > a + negate a = zero
class ( Additive a b t
      , AdditiveMagma a (Computation t (D t)) t
      , AdditiveInvertible b t
      ) =>
      AdditiveGroup a b t | a b -> t, a -> t, b -> t where
  infixl 6 -
  (-) :: a -> b -> Computation t (D t)
  (-) a b = a `plus` negate b

instance AdditiveGroup (D Double) (D Double) Double

instance AdditiveGroup (Computation Double (D Double)) (D Double) Double

instance AdditiveGroup (D Double) (Computation Double (D Double)) Double

instance AdditiveGroup (D Float) (D Float) Float

instance AdditiveGroup (D Float) (Computation Float (D Float)) Float

instance AdditiveGroup (Computation Float (D Float)) (D Float) Float

instance AdditiveGroup (Computation Double (D Double)) (Computation Double (D Double)) Double

instance AdditiveGroup (Computation Float (D Float)) (Computation Float (D Float)) Float
