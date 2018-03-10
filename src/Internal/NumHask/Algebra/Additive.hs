{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds        #-}
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
  , AdditiveGroupModule(..)
  , AdditiveBasis(..)
  , AdditiveModule(..)
  , Add(..)
  , Negate(..)
  , AdditiveBasisConstraints
  ) where
import           Internal.Internal
import           NumHask.Prelude   (Bool (..), Double, Float, Int, Integer,
                                    Show, pure, ($))
import qualified NumHask.Prelude   as P
import qualified NumHask.Array as A
import qualified NumHask.Prelude   as E

type AdditiveBasisConstraints r t
   = ( E.Num t
     , E.AdditiveBasis r t
     , E.AdditiveInvertible (r t)
     , E.AdditiveGroupBasis r t
     , E.AdditiveGroupModule r t
     , E.AdditiveModule r t)
-- | 'plus' is used as the operator for the additive magma to distinguish from '+' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `plus` b ∈ A
--
-- law is true by construction in Haskell
class (GetScope a ~ GetScope b) =>
      AdditiveMagma a b r t | a b -> t, a -> t, b -> t
  --, a -> r, b -> r
                                                , a b -> r
          -- Fundep: r and t can be determined by a, b, or a and b:  scalar ops don't change shape and must have the same representation.
                                                                                                                                          where
  plus :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)


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
class (AdditiveMagma a a r t ) =>
      AdditiveInvertible a r t | a -> t, a -> r where
  negate :: a -> Computation (GetScope a) t (D (GetScope a) r t)


-- | Idempotent magma for addition.
--
-- > a `plus` a == a
class AdditiveMagma a b r t =>
      AdditiveIdempotent a b r t

-- | sum definition avoiding a clash with the Sum monoid in base

sum ::
     ( Additive a a r t
     , Additive a (Computation (GetScope a) t (D (GetScope a) r t)) r t
     , P.Foldable f
     , AdditiveUnital a r t
     )
  => f a
  -> Computation (GetScope a) t (D (GetScope a) r t)
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
      , GetScope a ~GetScope b
      ) =>
      Additive a b r t where
  infixl 6 +
  (+) ::  a -> b -> Computation (GetScope b) t (D (GetScope a) r t)
  a + b = plus a b



-- | Non-commutative left minus
--
-- > negate a `plus` a = zero
class ( AdditiveMagma a b r t
      , AdditiveMagma (Computation (GetScope b) t (D (GetScope a) r t)) a r t
      , AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveAssociative b r t
      , AdditiveInvertible b r t
      , GetScope a ~GetScope b)
     =>
      AdditiveLeftCancellative a b r t where
  infixl 6 ~-
  (~-) :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)
  (~-) a b = negate b `plus` a

-- | Non-commutative right minus
--
-- > a `plus` negate a = zero
class ( AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveInvertible b r t
      , AdditiveMagma a (Computation (GetScope b) t (D (GetScope a) r t)) r t
      , GetScope a ~GetScope b
      ) =>
      AdditiveRightCancellative a b r t where
  infixl 6 -~
  (-~) :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)
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
      , AdditiveMagma a (Computation (GetScope b) t (D (GetScope a) r t)) r t
      , GetScope a ~GetScope b
      ) =>
      AdditiveGroup a b r t where
  infixl 6 -
  (-) :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)
  (-) a b = a `plus` negate b

data Add = Add deriving Show

data Negate = Negate deriving Show



instance (AdditiveBasisConstraints r Float) => AdditiveMagma (Computation s Float (D s r Float)) (Computation s Float (D s r Float)) r Float where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance (AdditiveBasisConstraints r Float) => AdditiveMagma (Computation s Float (D s r Float)) (D s r Float) r Float where
  plus a b = do
    aa <- a
    binOp Add aa b

instance (AdditiveBasisConstraints r Float) => AdditiveMagma (D s r Float) (Computation s Float (D s r Float)) r Float where
  plus a b = do
    bb <- b
    binOp Add a bb

instance (AdditiveBasisConstraints r Float) => AdditiveMagma (D s r Float) (D s r Float) r Float where
  plus= binOp Add

instance (AdditiveBasisConstraints r Double) => AdditiveMagma (Computation s Double (D s r Double)) (Computation s Double (D s r Double)) r Double where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance (AdditiveBasisConstraints r Double) => AdditiveMagma (Computation s Double (D s r Double)) (D s r Double) r Double where
  plus a b = do
    aa <- a
    binOp Add aa b

instance (AdditiveBasisConstraints r Double) => AdditiveMagma (D s r Double) (Computation s Double (D s r Double)) r Double where
  plus a b = do
    bb <- b
    binOp Add a bb

instance (AdditiveBasisConstraints r Double) => AdditiveMagma (D s r Double) (D s r Double) r Double where
  plus = binOp Add

instance (E.Additive a) => BinOp Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b P.+ a

instance (E.AdditiveBasis r a, E.AdditiveModule r a) => FfBin Add a r where
  {-# INLINE rff_bin #-}
  rff_bin _ a b = a E..+. b
  {-# INLINE r_ff_bin #-}
  r_ff_bin _ a b = a E..+ b
  {-# INLINE _ff_bin #-}
  _ff_bin _ a b = a E.+. b

instance DfDaBin Add s r (D s r a) a where
  {-# INLINE df_da #-}
  df_da _ _ _ _ at = pure at


instance DfDbBin Add s r (D s r a) a where
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt = pure bt

instance (E.AdditiveBasis r a, E.AdditiveModule r a, E.Num a) => DfBin Add s r (D s r a) (D s r a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Add a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Add at bt

instance  Trace Add s r a where
  pushAlg (B _ a b) dA = pure [(dA, a), (dA, b), (dA, a), (dA, b)]
  resetAlg (B _ a b) = pure [a, b, a, b]


instance (AdditiveBasisConstraints r Double) =>
         AdditiveUnital (D s r Double) r Double where
  zero = D 0

instance (AdditiveBasisConstraints r Float) => AdditiveUnital  (D s r Float) r Float where
  zero = D 0

instance (AdditiveBasisConstraints r Double) => AdditiveUnital  (Computation s Double (D s r Double)) r Double where
  zero = P.pure P.$ D 0

instance (AdditiveBasisConstraints r Float) => AdditiveUnital (Computation s Float (D s r Float)) r Float where
  zero = P.pure P.$ D 0


instance (AdditiveBasisConstraints r Double) => AdditiveAssociative (D s r Double) r Double

instance (AdditiveBasisConstraints r Double) => AdditiveAssociative (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints r Float) => AdditiveAssociative (D s r Float) r Float

instance (AdditiveBasisConstraints r Float) => AdditiveAssociative (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints r Double) => AdditiveCommutative (D s r Double) r Double

instance (AdditiveBasisConstraints r Float) => AdditiveCommutative (D s r Float) r Float

instance (AdditiveBasisConstraints r Double) => AdditiveCommutative (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints r Float) => AdditiveCommutative (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints r Double) => AdditiveInvertible (Computation s Double (D s r Double)) r Double where
  negate a = do
    aa <- a
    monOp Negate aa

instance (AdditiveBasisConstraints r Float) => AdditiveInvertible  (Computation s Float (D s r Float)) r Float where
  negate a = do
    aa <- a
    monOp Negate aa

instance (AdditiveBasisConstraints r Double) => AdditiveInvertible  (D s r Double) r Double where
  negate = monOp Negate

instance (AdditiveBasisConstraints r Float) => AdditiveInvertible   (D s r Float) r Float where
  negate = monOp Negate

instance (E.AdditiveInvertible a) => FfMon Negate a where
  {-# INLINE ff #-}
  ff _ a = P.negate a

instance (E.AdditiveInvertible (r a)) => RffMon Negate r a where
  {-# INLINE rff #-}
  rff _ a = P.negate a

instance (E.AdditiveInvertible a
         , AdditiveInvertible (D s r a) r a
         , E.Num a, E.AdditiveInvertible (r a)) => MonOp Negate s r a where
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at


instance (AdditiveInvertible (D s r a) r a, E.Num a) => Trace Negate s r a where
  pushAlg (U _ a) dA = do
    cda <- negate dA
    pure [(cda, a)]
  resetAlg (U _ a) = pure [a]


instance (AdditiveBasisConstraints r Double) => Additive (D s r Double) (D s r Double) r Double

instance (AdditiveBasisConstraints r Double) => Additive (Computation s Double (D s r Double)) (D s r Double) r Double

instance (AdditiveBasisConstraints r Double) => Additive (D s r Double) (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints r Float) => Additive (D s r Float) (D s r Float) r Float

instance (AdditiveBasisConstraints r Float) => Additive (D s r Float) (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints r Float) => Additive (Computation s Float (D s r Float)) (D s r Float) r Float

instance (AdditiveBasisConstraints r Double) => Additive (Computation s Double (D s r Double)) (Computation s Double (D s r Double)) r Double


instance (AdditiveBasisConstraints r Float) => Additive (Computation s Float (D s r Float)) (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints r Double) => AdditiveGroup (D s r Double) (D s r Double) r Double

instance (AdditiveBasisConstraints r Double) => AdditiveGroup (Computation s Double (D s r Double)) (D s r Double) r Double

instance (AdditiveBasisConstraints r Double) => AdditiveGroup (D s r Double) (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints r Float) => AdditiveGroup (D s r Float) (D s r Float) r Float

instance (AdditiveBasisConstraints r Float) => AdditiveGroup (D s r Float) (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints r Float) => AdditiveGroup (Computation s Float (D s r Float)) (D s r Float) r Float

instance (AdditiveBasisConstraints r Double) => AdditiveGroup (Computation s Double (D s r Double)) (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints r Float) => AdditiveGroup (Computation s Float (D s r Float)) (Computation s Float (D s r Float)) r Float


-- | Additive Module Laws
--
-- > (a + b) .+ c == a + (b .+ c)
-- > (a + b) .+ c == (a .+ c) + b
-- > a .+ zero == a
-- > a .+ b == b +. a
class (Additive a b r t) =>
      AdditiveModule r a b t where
  infixl 6 .+
  (.+) ::  a -> b -> Computation (GetScope b) t (D (GetScope a) r t)
  infixl 6 +.
  (+.) :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveModule (A.Array c s) (Computation sc Double  (D sc (A.Array c s) Double)) (D sc (A.Array c s) Double)  Double where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) a b = do
    ca <- a
    binOp Add ca b

instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveModule (A.Array c s) (Computation sc Double (D sc (A.Array c s) Double)) (Computation sc Double (D sc (A.Array c s) Double)) Double where
  (.+) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb
  (+.) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveModule (A.Array c s) (D sc (A.Array c s) Double) (D sc (A.Array c s) Double) Double where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b

instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveModule (A.Array c s) (D sc (A.Array c s) Double) (Computation sc Double  (D sc (A.Array c s) Double)) Double where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) a b = do
    cb <- b
    binOp Add a cb

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveModule (A.Array c s) (D sc (A.Array c s) Float) (D sc (A.Array c s) Float) Float where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveModule (A.Array c s) (D sc (A.Array c s) Float) (Computation sc Float  (D sc (A.Array c s) Float)) Float where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) a b = do
    cb <- b
    binOp Add a cb

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveModule (A.Array c s) (Computation sc Float  (D sc (A.Array c s) Float)) (D sc (A.Array c s) Float)  Float where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) a b = do
    ca <- a
    binOp Add ca b

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveModule (A.Array c s) (Computation sc Float (D sc (A.Array c s) Float)) (Computation sc Float (D sc (A.Array c s) Float)) Float where
  (.+) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb
  (+.) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb
-- | Subtraction Module Laws
--
-- > (a + b) .- c == a + (b .- c)
-- > (a + b) .- c == (a .- c) + b
-- > a .- zero == a
-- > a .- b == negate b +. a
class (AdditiveGroup a b r t) =>
      AdditiveGroupModule r a b t where
  infixl 6 .-
  (.-) ::  a -> b -> Computation (GetScope b) t (D (GetScope a) r t)
  infixl 6 -.
  (-.) ::   a -> b -> Computation (GetScope b) t (D (GetScope a) r t)


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupModule (A.Array c s) (D sc (A.Array c s) Float) (D sc (A.Array c s) Float) Float where
  (.-) a b = do
    cb <- (negate b)
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupModule (A.Array c s) (D sc (A.Array c s) Float) (Computation sc Float  (D sc (A.Array c s) Float)) Float where
  (.-) a b = do
    cb <- negate b
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupModule (A.Array c s) (Computation sc Float  (D sc (A.Array c s) Float)) (D sc (A.Array c s) Float)  Float where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupModule (A.Array c s) (Computation sc Float (D sc (A.Array c s) Float)) (Computation sc Float (D sc (A.Array c s) Float)) Float where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb



instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupModule (A.Array c s) (D sc (A.Array c s) Double) (D sc (A.Array c s) Double) Double where
  (.-) a b = do
    cb <- (negate b)
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupModule (A.Array c s) (D sc (A.Array c s) Double) (Computation sc Double  (D sc (A.Array c s) Double)) Double where
  (.-) a b = do
    cb <- negate b
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupModule (A.Array c s) (Computation sc Double  (D sc (A.Array c s) Double)) (D sc (A.Array c s) Double)  Double where
  (.-) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb

instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupModule (A.Array c s) (Computation sc Double (D sc (A.Array c s) Double)) (Computation sc Double (D sc (A.Array c s) Double)) Double where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb

-- | element by element addition
--
-- > (a .+. b) .+. c == a .+. (b .+. c)
-- > zero .+. a = a
-- > a .+. zero = a
-- > a .+. b == b .+. a
class (Additive a b r t) =>
      AdditiveBasis r a b t where
  infixl 7 .+.
  (.+.) :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)

instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveBasis (A.Array c s) (D sc (A.Array c s) Double) (D sc (A.Array c s) Double) Double where
  (.+.) a b = 
    binOp Add a b


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveBasis (A.Array c s) (D sc (A.Array c s) Double) (Computation sc Double  (D sc (A.Array c s) Double)) Double where
  (.+.) a b = do
    cb <-  b
    binOp Add a cb


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveBasis (A.Array c s) (Computation sc Double  (D sc (A.Array c s) Double)) (D sc (A.Array c s) Double)  Double where
  (.+.) a b = do
    ca <-  a
    binOp Add ca b


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveBasis (A.Array c s) (Computation sc Double (D sc (A.Array c s) Double)) (Computation sc Double (D sc (A.Array c s) Double)) Double where
  (.+.) a b = do
    ca <- a
    cb <-  b
    binOp Add ca cb


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveBasis (A.Array c s) (D sc (A.Array c s) Float) (D sc (A.Array c s) Float) Float where
  (.+.) a b = 
    binOp Add a b


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveBasis (A.Array c s) (D sc (A.Array c s) Float) (Computation sc Float  (D sc (A.Array c s) Float)) Float where
  (.+.) a b = do
    cb <-  b
    binOp Add a cb


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveBasis (A.Array c s) (Computation sc Float  (D sc (A.Array c s) Float)) (D sc (A.Array c s) Float)  Float where
  (.+.) a b = do
    ca <-  a
    binOp Add ca b


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveBasis (A.Array c s) (Computation sc Float (D sc (A.Array c s) Float)) (Computation sc Float (D sc (A.Array c s) Float)) Float where
  (.+.) a b = do
    ca <- a
    cb <-  b
    binOp Add ca cb



-- | element by element subtraction
--
-- > a .-. a = singleton zero
class (AdditiveGroup a b r t ) =>
      AdditiveGroupBasis r a b t where
  infixl 6 .-.
  (.-.) :: a -> b -> Computation (GetScope b) t (D (GetScope a) r t)

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupBasis (A.Array c s) (D sc (A.Array c s) Float) (D sc (A.Array c s) Float) Float where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupBasis (A.Array c s) (D sc (A.Array c s) Float) (Computation sc Float  (D sc (A.Array c s) Float)) Float where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupBasis (A.Array c s) (Computation sc Float  (D sc (A.Array c s) Float)) (D sc (A.Array c s) Float)  Float where
  (.-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveGroupBasis (A.Array c s) (Computation sc Float (D sc (A.Array c s) Float)) (Computation sc Float (D sc (A.Array c s) Float)) Float where
  (.-.) a b = do
    ca <- a
    cb <-  negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupBasis (A.Array c s) (D sc (A.Array c s) Double) (D sc (A.Array c s) Double) Double where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupBasis (A.Array c s) (D sc (A.Array c s) Double) (Computation sc Double  (D sc (A.Array c s) Double)) Double where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupBasis (A.Array c s) (Computation sc Double  (D sc (A.Array c s) Double)) (D sc (A.Array c s) Double)  Double where
  (.-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints (A.Array c s) Double) =>
         AdditiveGroupBasis (A.Array c s) (Computation sc Double (D sc (A.Array c s) Double)) (Computation sc Double (D sc (A.Array c s) Double)) Double where
  (.-.) a b = do
    ca <- a
    cb <-  negate b
    binOp Add ca cb
