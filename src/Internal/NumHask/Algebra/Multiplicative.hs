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
  , Multiply(..)
  , Divide(..)
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Protolude                         (Bool (..), Double, Float,
                                                    Int, Integer, pure, ($), Show)
import qualified Protolude                         as P

data Multiply = Multiply deriving Show

data Divide = Divide deriving Show

-- | 'times' is used as the operator for the multiplicative magam to distinguish from '*' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `times` b ∈ A
--
-- law is true by construction in Haskell
class (BinaryComputation a b) => MultiplicativeMagma a b  where
  times :: a -> b -> CodomainB a b

instance MultiplicativeMagma (Computation r Float (D r Float)) (Computation r Float (D r Float))  where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance MultiplicativeMagma (Computation r Float (D r Float)) (D r Float)  where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance MultiplicativeMagma (D r Float) (Computation r Float (D r Float))  where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance MultiplicativeMagma (D r Float) (D r Float)  where
  times = binOp Multiply


instance MultiplicativeMagma (Computation r Double (D r Double)) (Computation r Double (D r Double))  where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance MultiplicativeMagma (Computation r Double (D r Double)) (D r Double)  where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance MultiplicativeMagma (D r Double) (Computation r Double (D r Double))  where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance MultiplicativeMagma (D r Double) (D r Double)  where
  times = binOp Multiply

instance (P.Num a) => FFBin Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.* a

instance (P.Num a, Multiplicative (D r a) (D r a)) => DfDaBin Multiply r (D r a) a where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = binOp Multiply at b

instance ( P.Num a, Multiplicative (D r a) (D r a)) => DfDbBin Multiply r (D r a) a where
  {-# INLINE df_db #-}
  df_db _ a _ _ bt = binOp Multiply bt a

instance ( P.Num a, Multiplicative (D r a) (D r a)  ) => BinOp Multiply r (D r a) (D r a) a  where
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  binOp Multiply a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ ap at bp bt = do
    a <- (binOp Multiply at bp)
    b <- (binOp Multiply ap bt)
    binOp Add a b

instance ( Multiplicative (D r a) (D r a) ) => Trace Multiply r a where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA * p b
    opb <- cdA * p a
    arga <- cdA * b
    argb <- cdA * a
    pure [(opa, a), (opb, b), (arga, a), (argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]


-- | Unital magma for multiplication.
--
-- > one `times` a == a
-- > a `times` one == a
class MultiplicativeMagma a a =>
      MultiplicativeUnital a  where
  one :: a

instance MultiplicativeUnital (D r Double)  where
  one = D 1

instance MultiplicativeUnital  (D r Float)  where
  one = D 1

instance MultiplicativeUnital  (Computation r Double (D r Double))  where
  one = P.pure P.$ D 1

instance MultiplicativeUnital (Computation r Float (D r Float))  where
  one = P.pure P.$ D 1


-- | Associative magma for multiplication.
--
-- > (a `times` b) `times` c == a `times` (b `times` c)
class MultiplicativeMagma a a =>
      MultiplicativeAssociative a

instance MultiplicativeAssociative (D r Double)

instance MultiplicativeAssociative (D r Float)

instance MultiplicativeAssociative (Computation r Float (D r Float))

instance MultiplicativeAssociative (Computation r Double (D r Double))


-- | Commutative magma for multiplication.
--
-- > a `times` b == b `times` a
class MultiplicativeMagma a a =>
      MultiplicativeCommutative a 

instance MultiplicativeCommutative (D r Double)

instance MultiplicativeCommutative (D r Float)

instance MultiplicativeCommutative (Computation r Float (D r Float))

instance MultiplicativeCommutative (Computation r Double (D r Double))

-- | Invertible magma for multiplication.
--
-- > ∀ a ∈ A: recip a ∈ A
--
-- law is true by construction in Haskell
class ( MultiplicativeMagma a a
      , AdditiveGroup a a
      , AdditiveGroup (DomainElem (Domain a)) (DomainElem (Domain a))
      ) =>
      MultiplicativeInvertible a where
  recip :: a -> CodomainU a

instance (AdditiveGroup Double Double, Multiplicative Double Double) =>
         MultiplicativeInvertible (D r Double) where
  recip = binOp Divide one

instance (AdditiveGroup Float Float, Multiplicative Float Float) =>
         MultiplicativeInvertible (D r Float) where
  recip = binOp Divide one

instance (AdditiveGroup Double Double, Multiplicative Double Double) =>
         MultiplicativeInvertible (Computation r Double (D r Double)) where
  recip a = do
    aa <- a
    binOp Divide one aa

instance (AdditiveGroup Float Float, Multiplicative Float Float) =>
         MultiplicativeInvertible (Computation r Float (D r Float)) where
  recip a = do
    aa <- a
    binOp Divide one aa

instance (P.Num a, P.Fractional a) => FFBin Divide a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b P./ a

instance ( P.Fractional a
         , AdditiveGroup a a
         , AdditiveGroup (D r a) (D r a)
         , Multiplicative (D r a) (D r a)
         , MultiplicativeGroup (D r a) (D r a)
         , MultiplicativeGroup (Computation r a (D r a)) (D r a)
         , Multiplicative (D r a) (Computation r a (D r a))
         , Multiplicative a a
         ) =>
         DfDaBin Divide r (D r a) a where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = binOp Divide at b

instance ( P.Fractional a
         , AdditiveGroup a a
         , AdditiveGroup (D r a) (D r a)
         , Multiplicative (D r a) (D r a)
         , AdditiveInvertible (D r a)
         , Multiplicative a a
         , MultiplicativeGroup (Computation r a (D r a)) (D r a)
         , Multiplicative (D r a) (Computation r a (D r a))
         , MultiplicativeGroup (D r a) (D r a)
         ) =>
         DfDbBin Divide r (D r a) a  where
  {-# INLINE df_db #-}
  df_db _ a cp bp bt = do
    cbt <- (monOp Negate bt)
    ccpbp <- (binOp Divide cp bp)
    binOp Divide cbt ccpbp

instance ( P.Fractional a
         , Multiplicative a a
         , AdditiveGroup a a
         , AdditiveGroup (D r a) (D r a)
         , Multiplicative (D r a) (D r a)
         , Multiplicative (D r a) (Computation r a (D r a))
         , MultiplicativeGroup (D r a) (D r a)
         , MultiplicativeGroup (Computation r a (D r a)) (D r a)
         ) =>
         BinOp Divide r (D r a) (D r a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Divide a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ cp ap at bp bt = do
    catbt <- at - bt
    ccp <- binOp Multiply catbt cp
    binOp Divide (ccp) bp

instance ( P.Fractional a
         , AdditiveGroup a a
         -- , MultiplicativeGroup a a
         , Multiplicative a a
         , Multiplicative (D r a) (Computation r a (D r a))
         , AdditiveGroup (D r a) (D r a)
         , MultiplicativeGroup (D r a) (D r a)
         , MultiplicativeGroup (Computation r a (D r a)) (D r a)
         , Multiplicative (D r a) (D r a)
         , AdditiveInvertible (D r a)
         ) =>
         Trace Divide r a where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA / p b
    opb <- cdA * (((negate (p a)) / p b) * p b)
    arga <- cdA * b
    argb <- cdA * a
    pure [(opa, a), (opb, b), (arga, a), (argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

-- | Idempotent magma for multiplication.
--
-- > a `times` a == a
class MultiplicativeMagma a a =>
      MultiplicativeIdempotent a 

-- | product definition avoiding a clash with the Product monoid in base
--
product ::
     ( Multiplicative a a
     , Multiplicative a (CodomainU a)
     , MultiplicativeUnital a
     , P.Foldable f
     , MultiplicativeUnital a
     )
  => f a
  -> CodomainU a
product = P.foldr (*) one

-- | Multiplicative is commutative, associative and unital under multiplication
--
-- > one * a == a
-- > a * one == a
-- > (a * b) * c == a * (b * c)
-- > a * b == b * a
class ( MultiplicativeCommutative a
      , MultiplicativeCommutative b
      , MultiplicativeUnital a
      , MultiplicativeUnital b
      , MultiplicativeMagma a b
      , MultiplicativeAssociative a 
      ) =>
      Multiplicative a b  where
  infixl 7 *
  (*) :: a -> b -> CodomainB a b
  a * b = times a b

instance Multiplicative (D r Double) (D r Double)

instance Multiplicative (Computation r Double (D r Double)) (D r Double)

instance Multiplicative (D r Double) (Computation r Double (D r Double))

instance Multiplicative (D r Float) (D r Float)

instance Multiplicative (D r Float) (Computation r Float (D r Float))

instance Multiplicative (Computation r Float (D r Float)) (D r Float)

instance Multiplicative (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance Multiplicative (Computation r Float (D r Float)) (Computation r Float (D r Float)) -- | Non-commutative left divide
--
-- > recip a `times` a = one
class ( MultiplicativeUnital a
      , MultiplicativeAssociative a
      , MultiplicativeInvertible a
      , MultiplicativeUnital b
      , MultiplicativeMagma a b
      , MultiplicativeMagma (CodomainB a b) a
      , MultiplicativeAssociative b
      , MultiplicativeInvertible b
      ) =>
      MultiplicativeLeftCancellative a b  where
  infixl 7 ~/
  (~/) :: a -> b -> CodomainB a b
  a ~/ b = recip b `times` a

-- | Non-commutative right divide
--
-- > a `times` recip a = one
class ( MultiplicativeUnital a
      , MultiplicativeAssociative a
      , MultiplicativeInvertible a
      , MultiplicativeUnital b
      , MultiplicativeMagma a b
      , MultiplicativeMagma a (CodomainB a b)
      , MultiplicativeAssociative b
      , MultiplicativeInvertible b
      ) =>
      MultiplicativeRightCancellative a b where
  infixl 7 /~
  (/~) :: a -> b -> CodomainB a b
  a /~ b = a `times` recip b

-- | Divide ('/') is reserved for where both the left and right cancellative laws hold.  This then implies that the MultiplicativeGroup is also Abelian.
--
-- > a / a = one
-- > recip a = one / a
-- > recip a * a = one
-- > a * recip a = one
class ( Multiplicative a b
      , MultiplicativeInvertible a
      , MultiplicativeInvertible b
      , MultiplicativeMagma a b
      , MultiplicativeMagma a (CodomainB a b)
      ) =>
      MultiplicativeGroup a b where
  infixl 7 /
  (/) :: a -> b -> CodomainB a b
  (/) a b = a `times` recip b

instance (AdditiveGroup Double Double, Multiplicative Double Double) => MultiplicativeGroup (D r Double) (D r Double)

instance (AdditiveGroup Double Double, Multiplicative Double Double) =>MultiplicativeGroup (Computation r Double (D r Double)) (D r Double)

instance (AdditiveGroup Double Double, Multiplicative Double Double ) =>MultiplicativeGroup (D r Double) (Computation r Double (D r Double))

instance (AdditiveGroup Float Float, Multiplicative Float Float) => MultiplicativeGroup (D r Float) (D r Float)

instance (AdditiveGroup Float Float, Multiplicative Float Float) => MultiplicativeGroup (D r Float) (Computation r Float (D r Float))

instance (AdditiveGroup Float Float, Multiplicative Float Float) => MultiplicativeGroup (Computation r Float (D r Float)) (D r Float)

instance (AdditiveGroup Double Double, Multiplicative Double Double) => MultiplicativeGroup (Computation r Double (D r Double)) (Computation r Double (D r Double))

instance (AdditiveGroup Float Float, Multiplicative Float Float) => MultiplicativeGroup (Computation r Float (D r Float)) (Computation r Float (D r Float))

