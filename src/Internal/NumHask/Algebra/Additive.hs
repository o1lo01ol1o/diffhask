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
  ) where
import           Internal.Internal
import           Protolude         (Bool (..), Double, Float, Int, Integer,
                                    Show, pure, ($))
import qualified Protolude         as P
 
import qualified NumHask.Prelude as E

-- | 'plus' is used as the operator for the additive magma to distinguish from '+' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `plus` b ∈ A
--
-- law is true by construction in Haskell
class AdditiveMagma a b r t | a b -> t, a -> t, b -> t, a -> r, b -> r, a b -> r where -- Fundep: r and t can be determined by a, b, or a and b:  scalar ops don't change shape and must have the same representation.
  plus :: a -> b -> Computation r t (D r t)


-- | Unital magma for addition.
--
-- > zero `plus` a == a
-- > a `plus` zero == a
class AdditiveMagma a a r t =>
      AdditiveUnital a r t where
  zero :: a

-- | Associative magma for addition.
--
-- > (a `plus` b) `plus` c == a `plus` (b `plus` c)
class AdditiveMagma a a r t=>
      AdditiveAssociative a r t


-- | Commutative magma for addition.
--
-- > a `plus` b == b `plus` a
class AdditiveMagma a a r t =>
      AdditiveCommutative a r t


-- | Invertible magma for addition.
--
-- > ∀ a ∈ A: negate a ∈ A
--
-- law is true by construction in Haskell
class AdditiveMagma a a r t =>
      AdditiveInvertible a r t | a -> t, a -> r where
  negate :: a -> Computation r t (D r t)


-- | Idempotent magma for addition.
--
-- > a `plus` a == a
class AdditiveMagma a b r t =>
      AdditiveIdempotent a b r t

-- | sum definition avoiding a clash with the Sum monoid in base

sum ::
     ( Additive a a r t
     , Additive a (Computation r t (D r t)) r t
     , P.Foldable f
     , AdditiveUnital a r t
     )
  => f a
  -> Computation r t (D r t)
sum = P.foldr (+) zero

-- | Additive is commutative, unital and associative under addition
--
-- > zero + a == a
-- > a + zero == a
-- > (a + b) + c == a + (b + c)
-- > a + b == b + a
class ( AdditiveCommutative a r t
      , AdditiveCommutative b r t
      , AdditiveUnital a r t
      , AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveAssociative b r t
      , AdditiveMagma a b r t
      ) =>
      Additive a b r t where
  infixl 6 +
  (+) :: a -> b -> Computation r t (D r t)
  a + b = plus a b



-- | Non-commutative left minus
--
-- > negate a `plus` a = zero
class ( AdditiveMagma a b r t
      , AdditiveMagma (Computation r t (D r t)) a r t
      , AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveAssociative b r t
      , AdditiveInvertible b r t)
     =>
      AdditiveLeftCancellative a b r t where
  infixl 6 ~-
  (~-) :: a -> b -> Computation r t (D r t)
  (~-) a b = negate b `plus` a

-- | Non-commutative right minus
--
-- > a `plus` negate a = zero
class ( AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveInvertible b r t
      , AdditiveMagma a (Computation r t (D r t)) r t

      ) =>
      AdditiveRightCancellative a b r t where
  infixl 6 -~
  (-~) :: a -> b -> Computation r t (D r t)
  (-~) a b = a `plus` negate b

-- | Minus ('-') is reserved for where both the left and right cancellative laws hold.  This then implies that the AdditiveGroup is also Abelian.
--
-- Syntactic unary negation - substituting "negate a" for "-a" in code - is hard-coded in the language to assume a Num instance.  So, for example, using ''-a = zero - a' for the second rule below doesn't work.
--
-- > a - a = zero
-- > negate a = zero - a
-- > negate a + a = zero
-- > a + negate a = zero
class ( Additive a b r t
      , AdditiveInvertible b r t
      , AdditiveMagma a (Computation r t (D r t)) r t

      ) =>
      AdditiveGroup a b r t where
  infixl 6 -
  (-) :: a -> b -> Computation r t (D r t)
  (-) a b = a `plus` negate b

data Add = Add deriving Show

data Negate = Negate deriving Show



instance AdditiveMagma (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance AdditiveMagma (Computation r Float (D r Float)) (D r Float) r Float where
  plus a b = do
    aa <- a
    binOp Add aa b

instance AdditiveMagma (D r Float) (Computation r Float (D r Float)) r Float where
  plus a b = do
    bb <- b
    binOp Add a bb

instance AdditiveMagma (D r Float) (D r Float) r Float where
  plus= binOp Add

instance AdditiveMagma (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance AdditiveMagma (Computation r Double (D r Double)) (D r Double) r Double where
  plus a b = do
    aa <- a
    binOp Add aa b

instance AdditiveMagma (D r Double) (Computation r Double (D r Double)) r Double where
  plus a b = do
    bb <- b
    binOp Add a bb

instance AdditiveMagma (D r Double) (D r Double) r Double where
  plus = binOp Add

instance (P.Num a) => BinOp Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b P.+ a

instance FfBin Add a r where
  {-# INLINE rff_bin #-}
  rff_bin _ a b = a E..+. b
  {-# INLINE r_ff_bin #-}
  r_ff_bin _ a b = a E..+ b
  {-# INLINE _ff_bin #-}
  _ff_bin _ a b = a E.+. b

instance DfDaBin Add r (D r a) a where
  {-# INLINE df_da #-}
  df_da _ _ _ _ at = pure at


instance DfDbBin Add r (D r a) a where
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt = pure bt

instance (P.Num a) => DfBin Add  r (D r a) (D r a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Add a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Add at bt

instance  Trace Add r a where
  pushEl (B _ a b) dA = pure [(dA, a), (dA, b), (dA, a), (dA, b)]
  resetEl (B _ a b) = pure [a, b, a, b]


instance AdditiveUnital (D r Double) r Double where
  zero = D 0

instance AdditiveUnital  (D r Float) r Float where
  zero = D 0

instance AdditiveUnital  (Computation r Double (D r Double)) r Double where
  zero = P.pure P.$ D 0

instance AdditiveUnital (Computation r Float (D r Float)) r Float where
  zero = P.pure P.$ D 0


instance AdditiveAssociative (D r Double) r Double

instance AdditiveAssociative (Computation r Double (D r Double)) r Double

instance AdditiveAssociative (D r Float) r Float

instance AdditiveAssociative (Computation r Float (D r Float)) r Float

instance AdditiveCommutative (D r Double) r Double

instance AdditiveCommutative (D r Float) r Float

instance AdditiveCommutative (Computation r Double (D r Double)) r Double

instance AdditiveCommutative (Computation r Float (D r Float)) r Float

instance AdditiveInvertible (Computation r Double (D r Double)) r Double where
  negate a = do
    aa <- a
    monOp Negate aa

instance AdditiveInvertible  (Computation r Float (D r Float)) r Float where
  negate a = do
    aa <- a
    monOp Negate aa

instance AdditiveInvertible  (D r Double) r Double where
  negate = monOp Negate

instance AdditiveInvertible   (D r Float) r Float where
  negate = monOp Negate

instance (P.Num a) => FfMon Negate a where
  {-# INLINE ff #-}
  ff _ a = P.negate a

instance (AdditiveInvertible (D r a) r a, P.Num a) => MonOp Negate r a where
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at


instance (AdditiveInvertible (D r a) r a, P.Num a) => Trace Negate r a where
  pushEl (U _ a) dA = do
    cda <- negate dA
    pure [(cda, a)]
  resetEl (U _ a) = pure [a]


instance Additive (D r Double) (D r Double) r Double

instance Additive (Computation r Double (D r Double)) (D r Double) r Double

instance Additive (D r Double) (Computation r Double (D r Double)) r Double

instance Additive (D r Float) (D r Float) r Float

instance Additive (D r Float) (Computation r Float (D r Float)) r Float

instance Additive (Computation r Float (D r Float)) (D r Float) r Float

instance Additive (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double


instance Additive (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float

instance AdditiveGroup (D r Double) (D r Double) r Double

instance AdditiveGroup (Computation r Double (D r Double)) (D r Double) r Double

instance AdditiveGroup (D r Double) (Computation r Double (D r Double)) r Double

instance AdditiveGroup (D r Float) (D r Float) r Float

instance AdditiveGroup (D r Float) (Computation r Float (D r Float)) r Float

instance AdditiveGroup (Computation r Float (D r Float)) (D r Float) r Float

instance AdditiveGroup (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance AdditiveGroup (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float


-- | Additive Module Laws
--
-- > (a + b) .+ c == a + (b .+ c)
-- > (a + b) .+ c == (a .+ c) + b
-- > a .+ zero == a
-- > a .+ b == b +. a
class (Additive a b r t) =>
      AdditiveModule r a b t where
  infixl 6 .+
  (.+) ::  a -> b -> Computation r t (D r t)
  infixl 6 +.
  (+.) :: a -> b -> Computation r t (D r t)


-- | Subtraction Module Laws
--
-- > (a + b) .- c == a + (b .- c)
-- > (a + b) .- c == (a .- c) + b
-- > a .- zero == a
-- > a .- b == negate b +. a
class (AdditiveGroup a b r t) =>
      AdditiveGroupModule r a b t where
  infixl 6 .-
  (.-) ::  a -> b -> Computation r t (D r t)
  infixl 6 -.
  (-.) ::   a -> b -> Computation r t (D r t)

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
