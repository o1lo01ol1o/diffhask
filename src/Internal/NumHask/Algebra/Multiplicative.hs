{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | A magma heirarchy for multiplication. The basic magma structure is repeated and prefixed with 'Multiplicative-'.
module Internal.NumHask.Algebra.Multiplicative
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

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Protolude                         (Bool (..), Double, Float,
                                                    Int, Integer, Show, pure,
                                                    ($))
import qualified Protolude                         as P



-- | 'times' is used as the operator for the multiplicative magam to distinguish from '*' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `times` b ∈ A
--
-- law is true by construction in Haskell
class MultiplicativeMagma a b r t | a b -> t, a -> t, b -> t, a -> r, b -> r, a b -> r where
  times :: a -> b -> Computation r t (D r t)


-- | Unital magma for multiplication.
--
-- > one `times` a == a
-- > a `times` one == a
class MultiplicativeMagma a a r t=>
      MultiplicativeUnital a r t where
  one :: a




-- | Associative magma for multiplication.
--
-- > (a `times` b) `times` c == a `times` (b `times` c)
class MultiplicativeMagma a a r t=>
      MultiplicativeAssociative a r t




-- | Commutative magma for multiplication.
--
-- > a `times` b == b `times` a
class MultiplicativeMagma a a r t =>
      MultiplicativeCommutative a r t



-- | Invertible magma for multiplication.
--
-- > ∀ a ∈ A: recip a ∈ A
--
-- law is true by construction in Haskell
class ( MultiplicativeMagma a a r t
      , AdditiveGroup a a r t
      ) =>
      MultiplicativeInvertible a r t where
  recip :: a -> Computation r t (D r t)




-- | Idempotent magma for multiplication.
--
-- > a `times` a == a
class MultiplicativeMagma a a r t=>
      MultiplicativeIdempotent a r t

-- | product definition avoiding a clash with the Product monoid in base
--
product ::
     ( Multiplicative a a r t
     , Multiplicative a (Computation r t (D r t)) r t
     , MultiplicativeUnital a r t
     , P.Foldable f
     )
  => f a
  -> Computation r t (D r t)
product = P.foldr (*) one

-- | Multiplicative is commutative, associative and unital under multiplication
--
-- > one * a == a
-- > a * one == a
-- > (a * b) * c == a * (b * c)
-- > a * b == b * a
class ( MultiplicativeCommutative a r t
      , MultiplicativeCommutative b r t
      , MultiplicativeUnital a r t
      , MultiplicativeUnital b r t
      , MultiplicativeMagma a b r t
      , MultiplicativeAssociative a r t
      , MultiplicativeAssociative b r t
      ) =>
      Multiplicative a b r t where
  infixl 7 *
  (*) :: a -> b -> Computation r t (D r t)
  a * b = times a b

-- > recip a `times` a = one
class ( MultiplicativeUnital a r t
      , MultiplicativeAssociative a r t
      , MultiplicativeInvertible a r t
      , MultiplicativeUnital b r t
      , MultiplicativeMagma a b r t
      , MultiplicativeMagma (Computation r t (D r t)) a r t
      , MultiplicativeAssociative b r t
      , MultiplicativeInvertible b r t
      ) =>
      MultiplicativeLeftCancellative a b r t where
  infixl 7 ~/
  (~/) :: a -> b -> Computation r t (D r t)
  a ~/ b = recip b `times` a

-- | Non-commutative right divide
--
-- > a `times` recip a = one
class ( MultiplicativeUnital a r t
      , MultiplicativeAssociative a r t
      , MultiplicativeInvertible a r t
      , MultiplicativeUnital b r t
      , MultiplicativeMagma a b r t
      , MultiplicativeMagma a (Computation r t (D r t)) r t
      , MultiplicativeAssociative b r t
      , MultiplicativeInvertible b r t
      ) =>
      MultiplicativeRightCancellative a b r t where
  infixl 7 /~
  (/~) :: a -> b -> Computation r t (D r t)
  a /~ b = a `times` recip b

-- | Divide ('/') is reserved for where both the left and right cancellative laws hold.  This then implies that the MultiplicativeGroup is also Abelian.
--
-- > a / a = one
-- > recip a = one / a
-- > recip a * a = one
-- > a * recip a = one
class ( Multiplicative a b r t
      , MultiplicativeInvertible a r t
      , MultiplicativeInvertible b r t
      , MultiplicativeMagma a b r t
      , MultiplicativeMagma a (Computation r t (D r t)) r t
      ) =>
      MultiplicativeGroup a b r t where
  infixl 7 /
  (/) :: a -> b -> Computation r t (D r t)
  (/) a b = a `times` recip b


data Multiply = Multiply deriving Show

data Divide = Divide deriving Show

instance MultiplicativeMagma (Computation r Float (D r Float)) (Computation r Float (D r Float))r Float where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance MultiplicativeMagma (Computation r Float (D r Float)) (D r Float)r Float where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance MultiplicativeMagma (D r Float) (Computation r Float (D r Float))r Float where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance MultiplicativeMagma (D r Float) (D r Float)r Float where
  times = binOp Multiply

instance MultiplicativeMagma (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance MultiplicativeMagma (Computation r Double (D r Double)) (D r Double) r Double where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance MultiplicativeMagma (D r Double) (Computation r Double (D r Double)) r Double where
  times a b = do
    bb <- b
    binOp Multiply a bb


instance MultiplicativeMagma (D r Double) (D r Double) r Double where
  times = binOp Multiply

instance (P.Num a) => BinOp Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.* a


instance (P.Num t, Multiplicative (D r t) (D r t) r t) => DfDaBin Multiply r (D r t) t where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = binOp Multiply at b

instance ( P.Num t, Multiplicative (D r t) (D r t) r t) => DfDbBin Multiply r (D r t) t where
  {-# INLINE df_db #-}
  df_db _ a _ _ bt = binOp Multiply bt a


instance (P.Num a) => FfBin Multiply a r where
  {-#INLINE rff_bin #-}
  rff_bin _ a b = a .*. b
  {-#INLINE r_ff_bin #-}
  r_ff_bin _ a b = a .* b
  {-#INLINE _ff_bin #-}
  _ff_bin _ a b = a *. b


instance ( P.Num t, Multiplicative (D r t) (D r t) r t ) => DfBin Multiply r (D r t) (D r t) t  where
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  binOp Multiply a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ ap at bp bt = do
    a <- (binOp Multiply at bp)
    b <- (binOp Multiply ap bt)
    binOp Add a b

instance ( Multiplicative (D r t) (D r t) r t ) => Trace Multiply r t where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA * p b
    opb <- cdA * p a
    arga <- cdA * b
    argb <- cdA * a
    pure [(opa, a), (opb, b), (arga, a), (argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

instance MultiplicativeUnital (D r Double) r Double where
  one = D 1

instance MultiplicativeUnital  (D r Float) r Float where
  one = D 1

instance MultiplicativeUnital  (Computation r Double (D r Double)) r Double where
  one = P.pure P.$ D 1

instance MultiplicativeUnital (Computation r Float (D r Float)) r Float where
  one = P.pure P.$ D 1

instance MultiplicativeAssociative (D r Double) r Double

instance MultiplicativeAssociative (D r Float) r Float

instance MultiplicativeAssociative (Computation r Float (D r Float)) r Float

instance MultiplicativeAssociative (Computation r Double (D r Double)) r Double

instance MultiplicativeCommutative (D r Double) r Double

instance MultiplicativeCommutative (D r Float) r Float

instance MultiplicativeCommutative (Computation r Float (D r Float)) r Float

instance MultiplicativeCommutative (Computation r Double (D r Double)) r Double

instance
         MultiplicativeInvertible (D r Double) r Double where
  recip = binOp Divide one

instance
         MultiplicativeInvertible (D r Float) r Float where
  recip = binOp Divide one

instance
         MultiplicativeInvertible (Computation r Double (D r Double)) r Double where
  recip a = do
    aa <- a
    binOp Divide one aa

instance
         MultiplicativeInvertible (Computation r Float (D r Float)) r Float where
  recip a = do
    aa <- a
    binOp Divide one aa

instance (P.Num a, P.Fractional a) => BinOp Divide a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b P./ a


instance (P.Num a) => FfBin Divide a r where
  {-#INLINE rff_bin #-}
  rff_bin _ a b = a ./. b
  {-#INLINE r_ff_bin #-}
  r_ff_bin _ a b = a ./ b
  {-#INLINE _ff_bin #-}
  _ff_bin _ a b = a /. b


instance ( P.Fractional t
         , AdditiveGroup (D r t) (D r t) r t
         , Multiplicative (D r t) (D r t) r t
         , MultiplicativeGroup (D r t) (D r t) r t
         , MultiplicativeGroup (Computation r t (D r t)) (D r t) r t
         , Multiplicative (D r t) (Computation r t (D r t)) r t
         ) =>
         DfDaBin Divide r (D r t) t where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = binOp Divide at b

instance ( P.Fractional t

         , AdditiveGroup (D r t) (D r t) r t
         , Multiplicative (D r t) (D r t) r t
         , AdditiveInvertible (D r t) r t

         , MultiplicativeGroup (Computation r t (D r t)) (D r t) r t
         , Multiplicative (D r t) (Computation r t (D r t)) r t
         , MultiplicativeGroup (D r t) (D r t) r t
         ) =>
         DfDbBin Divide r (D r t) t  where
  {-# INLINE df_db #-}
  df_db _ a cp bp bt = do
    cbt <- (monOp Negate bt)
    ccpbp <- (binOp Divide cp bp)
    binOp Divide cbt ccpbp


instance ( P.Fractional t
         , AdditiveGroup (D r t) (D r t) r t
         , Multiplicative (D r t) (D r t) r t
         , Multiplicative (D r t) (Computation r t (D r t)) r t
         , MultiplicativeGroup (D r t) (D r t) r t
         , MultiplicativeGroup (Computation r t (D r t)) (D r t) r t
         ) =>
         DfBin Divide r (D r t) (D r t) t where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Divide a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ cp ap at bp bt = do
    catbt <- at - bt
    ccp <- binOp Multiply catbt cp
    binOp Divide (ccp) bp

instance ( P.Fractional t
         , Multiplicative (D r t) (Computation r t (D r t)) r t
         , AdditiveGroup (D r t) (D r t) r t
         , MultiplicativeGroup (D r t) (D r t) r t
         , MultiplicativeGroup (Computation r t (D r t)) (D r t) r t
         , Multiplicative (D r t) (D r t) r t
         , AdditiveInvertible (D r t) r t
         ) =>
         Trace Divide r t where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA / p b
    opb <- cdA * (((negate (p a)) / p b) * p b)
    arga <- cdA * b
    argb <- cdA * a
    pure [(opa, a), (opb, b), (arga, a), (argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

instance Multiplicative (D r Double) (D r Double) r Double

instance Multiplicative (Computation r Double (D r Double)) (D r Double) r Double

instance Multiplicative (D r Double) (Computation r Double (D r Double)) r Double

instance Multiplicative (D r Float) (D r Float) r Float

instance Multiplicative (D r Float) (Computation r Float (D r Float)) r Float

instance Multiplicative (Computation r Float (D r Float)) (D r Float) r Float

instance Multiplicative (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance Multiplicative (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float -- | Non-commutative left divide
--

instance MultiplicativeGroup (D r Double) (D r Double) r Double

instance MultiplicativeGroup (Computation r Double (D r Double)) (D r Double) r Double

instance MultiplicativeGroup (D r Double) (Computation r Double (D r Double)) r Double

instance MultiplicativeGroup (D r Float) (D r Float) r Float

instance MultiplicativeGroup (D r Float) (Computation r Float (D r Float)) r Float

instance MultiplicativeGroup (Computation r Float (D r Float)) (D r Float) r Float

instance MultiplicativeGroup (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance MultiplicativeGroup (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float


-- | Multiplicative Module Laws
--
-- > a .* one == a
-- > (a + b) .* c == (a .* c) + (b .* c)
-- > c *. (a + b) == (c *. a) + (c *. b)
-- > a .* zero == zero
-- > a .* b == b *. a
class (Multiplicative a b r t) =>
      MultiplicativeModule r a b t where
  infixl 7 .*
  (.*) ::  a -> b -> Computation r t (D r t)
  infixl 7 *.
  (*.) ::  a -> b -> Computation r t (D r t)

-- | Division Module Laws
--
-- > nearZero a || a ./ one == a
-- > b == zero || a ./ b == recip b *. a
class (MultiplicativeGroup a b r t) =>
      MultiplicativeGroupModule r a b t where
  infixl 7 ./
  (./) :: a -> b -> Computation r t (D r t)
  infixl 7 /.
  (/.) :: a -> b -> Computation r t (D r t)


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
