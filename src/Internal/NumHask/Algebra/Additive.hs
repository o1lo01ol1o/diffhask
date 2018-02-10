{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- | A magma heirarchy for addition. The basic magma structure is repeated and prefixed with 'Additive-'.
module Internal.NumHask.Algebra.Additive
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
  , Trace(..)
  , Add(..)
  , Negate(..)
  ) where
import           Internal.Internal
import           Protolude         (Bool (..), Double, Float, Int, Integer,
                                    Show, pure, ($))
import qualified Protolude         as P

data Add = Add deriving Show

data Negate = Negate deriving Show

-- | 'plus' is used as the operator for the additive magma to distinguish from '+' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `plus` b ∈ A
--
-- law is true by construction in Haskell
class (BinaryComputation a b) => AdditiveMagma a b  where
  plus :: a -> b -> CodomainB a b

instance AdditiveMagma (Computation r Float (D r Float)) (Computation r Float (D r Float)) where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance AdditiveMagma (Computation r Float (D r Float)) (D r Float) where
  plus a b = do
    aa <- a
    binOp Add aa b

instance AdditiveMagma (D r Float) (Computation r Float (D r Float)) where
  plus a b = do
    bb <- b
    binOp Add a bb

instance AdditiveMagma (D r Float) (D r Float) where
  plus= binOp Add


instance AdditiveMagma (Computation r Double (D r Double)) (Computation r Double (D r Double)) where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance AdditiveMagma (Computation r Double (D r Double)) (D r Double) where
  plus a b = do
    aa <- a
    binOp Add aa b

instance AdditiveMagma (D r Double) (Computation r Double (D r Double)) where
  plus a b = do
    bb <- b
    binOp Add a bb

instance AdditiveMagma (D r Double) (D r Double) where
  plus = binOp Add


instance (P.Num a) => FFBin Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b P.+ a

instance DfDaBin Add r (D r a) a where
  {-# INLINE df_da #-}
  df_da _ _ _ _ at = pure at

instance DfDbBin Add r (D r a) a where
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt = pure bt

instance (P.Num a) => BinOp Add  r (D r a) (D r a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Add a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Add at bt

instance  Trace Add r a where
  pushEl (B _ a b) dA = pure [(dA, a), (dA, b), (dA, a), (dA, b)]
  resetEl (B _ a b) = pure [a, b, a, b]


-- | Unital magma for addition.
--
-- > zero `plus` a == a
-- > a `plus` zero == a
class AdditiveMagma a a  =>
      AdditiveUnital a  where
  zero :: a

instance AdditiveUnital (D r Double) where
  zero = D 0

instance AdditiveUnital  (D r Float) where
  zero = D 0

instance AdditiveUnital  (Computation r Double (D r Double)) where
  zero = P.pure P.$ D 0

instance AdditiveUnital (Computation r Float (D r Float)) where
  zero = P.pure P.$ D 0


-- | Associative magma for addition.
--
-- > (a `plus` b) `plus` c == a `plus` (b `plus` c)
class AdditiveMagma a a =>
      AdditiveAssociative a

instance AdditiveAssociative (D r Double)

instance AdditiveAssociative (Computation r Double (D r Double))

instance AdditiveAssociative (D r Float)

instance AdditiveAssociative (Computation r Float (D r Float))



-- | Commutative magma for addition.
--
-- > a `plus` b == b `plus` a
class AdditiveMagma a a =>
      AdditiveCommutative a

instance AdditiveCommutative (D r Double)

instance AdditiveCommutative (D r Float)

instance AdditiveCommutative (Computation r Double (D r Double))

instance AdditiveCommutative (Computation r Float (D r Float))


-- | Invertible magma for addition.
--
-- > ∀ a ∈ A: negate a ∈ A
--
-- law is true by construction in Haskell
class AdditiveMagma a a =>
      AdditiveInvertible a where
  negate :: a -> CodomainU a

instance AdditiveInvertible (Computation r Double (D r Double)) where
  negate a = do
    aa <- a
    monOp Negate aa

instance AdditiveInvertible  (Computation r Float (D r Float)) where
  negate a = do
    aa <- a
    monOp Negate aa

instance AdditiveInvertible  (D r Double) where
  negate = monOp Negate

instance AdditiveInvertible   (D r Float) where
  negate = monOp Negate

instance (P.Num a) => FfMon Negate a where
  {-# INLINE ff #-}
  ff _ a = P.negate a

instance (AdditiveInvertible (D r a), P.Num a) => MonOp Negate r a where
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at

instance (AdditiveInvertible (D r a), P.Num a) => Trace Negate r a where
  pushEl (U _ a) dA = do
    cda <- negate dA
    pure [(cda, a)]
  resetEl (U _ a) = pure [a]

-- | Idempotent magma for addition.
--
-- > a `plus` a == a
class AdditiveMagma a b =>
      AdditiveIdempotent a b

-- | sum definition avoiding a clash with the Sum monoid in base

sum ::
     ( Additive a a
     , Additive a (CodomainU a)
     , P.Foldable f
     , AdditiveUnital a
     )
  => f a
  -> CodomainU a
sum = P.foldr (+) zero

-- | Additive is commutative, unital and associative under addition
--
-- > zero + a == a
-- > a + zero == a
-- > (a + b) + c == a + (b + c)
-- > a + b == b + a
class ( AdditiveCommutative a
      , AdditiveCommutative b
      , AdditiveUnital a
      , AdditiveUnital b
      , AdditiveAssociative a
      , AdditiveAssociative b
      , AdditiveMagma a b
      ) =>
      Additive a b  where
  infixl 6 +
  (+) :: a -> b -> CodomainB a b
  a + b = plus a b

instance Additive (D r Double) (D r Double)

instance Additive (Computation r Double (D r Double)) (D r Double)

instance Additive (D r Double) (Computation r Double (D r Double))

instance Additive (D r Float) (D r Float)

instance Additive (D r Float) (Computation r Float (D r Float))

instance Additive (Computation r Float (D r Float)) (D r Float)

instance Additive (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance Additive (Computation r Float (D r Float)) (Computation r Float (D r Float))

-- | Non-commutative left minus
--
-- > negate a `plus` a = zero
class ( AdditiveMagma a b
      , AdditiveMagma (CodomainU b) a
      , AdditiveUnital b
      , AdditiveAssociative a
      , AdditiveAssociative b
      , AdditiveInvertible b)
     =>
      AdditiveLeftCancellative a b  where
  infixl 6 ~-
  (~-) :: a -> b -> CodomainB a b
  (~-) a b = negate b `plus` a

-- | Non-commutative right minus
--
-- > a `plus` negate a = zero
class ( AdditiveUnital b
      , AdditiveAssociative a
      , AdditiveInvertible b
      , AdditiveMagma a (CodomainU b)
      , BinaryComputation a b
      ) =>
      AdditiveRightCancellative a b where
  infixl 6 -~
  (-~) :: a -> b -> CodomainB a b
  (-~) a b = a `plus` negate b

-- | Minus ('-') is reserved for where both the left and right cancellative laws hold.  This then implies that the AdditiveGroup is also Abelian.
--
-- Syntactic unary negation - substituting "negate a" for "-a" in code - is hard-coded in the language to assume a Num instance.  So, for example, using ''-a = zero - a' for the second rule below doesn't work.
--
-- > a - a = zero
-- > negate a = zero - a
-- > negate a + a = zero
-- > a + negate a = zero
class ( Additive a b
      , AdditiveInvertible b
      , AdditiveMagma a (CodomainU b)
      , BinaryComputation a b
      ) =>
      AdditiveGroup a b where
  infixl 6 -
  (-) :: a -> b -> CodomainB a b
  (-) a b = a `plus` negate b

instance AdditiveGroup (D r Double) (D r Double)

instance AdditiveGroup (Computation r Double (D r Double)) (D r Double)

instance AdditiveGroup (D r Double) (Computation r Double (D r Double))

instance AdditiveGroup (D r Float) (D r Float)

instance AdditiveGroup (D r Float) (Computation r Float (D r Float))

instance AdditiveGroup (Computation r Float (D r Float)) (D r Float)

instance AdditiveGroup (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance AdditiveGroup (Computation r Float (D r Float)) (Computation r Float (D r Float))


