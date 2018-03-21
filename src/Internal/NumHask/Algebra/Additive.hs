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
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE OverloadedLists             #-}
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
import qualified NumHask.Array     as A
import           NumHask.Prelude   (Bool (..), Double, Float, Int, Integer,
                                    Show, pure, ($))
import qualified NumHask.Prelude   as P
import qualified NumHask.Prelude   as E
import qualified Numeric.Dimensions as Dim
import GHC.Exts

type AdditiveBasisConstraints c r t
   = ( E.Num t
     , Dim.Dimensions r
     , A.Container c
     , E.AdditiveBasis (A.Array c r) t
     , E.AdditiveInvertible ((A.Array c r) t)
     , E.AdditiveGroupBasis (A.Array c r) t
     , E.AdditiveGroupModule (A.Array c r) t
     , E.AdditiveModule (A.Array c r) t)
-- | 'plus' is used as the operator for the additive magma to distinguish from '+' which, by convention, implies commutativity
--
-- > ∀ a,b ∈ A: a `plus` b ∈ A
--
-- law is true by construction in Haskell
class ( SameContainer a b
      , Dim.Dimensions r
      , A.Container (GetContainer a)
      , A.Container (GetContainer b)
      , Operable (GetContainer a) r t
      , Operable (GetContainer b) r t
      ) =>
      AdditiveMagma a b r t | a b -> t, a -> t, b -> t
  --, a -> r, b -> r
                                                , a b -> r
          -- Fundep: r and t can be determined by a, b, or a and b:  scalar ops don't change shape and must have the same representation.
                                                                                                                                          where
  plus ::
       (GetContainer a ~ c, SameContainer a b)
    => a
    -> b
    -> Computation c t (D c r t)


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
  negate :: (GetContainer a ~ c) => a -> Computation c t (D c r t)


-- | Idempotent magma for addition.
--
-- > a `plus` a == a
class AdditiveMagma a b r t =>
      AdditiveIdempotent a b r t

-- | sum definition avoiding a clash with the Sum monoid in base

sum ::
     ( Additive a a r t
     , Additive a (Computation c t (D c r t)) r t
     , P.Foldable f
     , AdditiveUnital a r t
     )
  => f a
  -> Computation c t (D c r t)
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
  (+) :: (GetContainer a ~ c, SameContainer a b) => a -> b -> Computation c t (D c r t)
  a + b = plus a b



-- | Non-commutative left minus
--
-- > negate a `plus` a = zero
class ( AdditiveMagma a b r t
      , AdditiveMagma (Computation (GetContainer a) t (D (GetContainer a) r t)) a r t
      , AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveAssociative b r t
      , AdditiveInvertible b r t
      , SameContainer a b
      )
     =>
      AdditiveLeftCancellative a b r t where
  infixl 6 ~-
  (~-) :: (GetContainer b ~ c, SameContainer a b) => a -> b -> Computation c t (D c r t)
  (~-) a b = negate b `plus` a

-- | Non-commutative right minus
--
-- > a `plus` negate a = zero
class ( AdditiveUnital b r t
      , AdditiveAssociative a r t
      , AdditiveInvertible b r t
      , AdditiveMagma a (Computation (GetContainer b) t (D (GetContainer b) r t)) r t

      ) =>
      AdditiveRightCancellative a b r t where
  infixl 6 -~
  (-~) :: (GetContainer a ~ c, SameContainer a b) => a -> b -> Computation c t (D c r t)
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
      , AdditiveMagma a (Computation (GetContainer a) t (D (GetContainer b) r t)) r t

      ) =>
      AdditiveGroup a b r t where
  infixl 6 -
  (-) :: (SameContainer a b, GetContainer a ~ c) => a -> b -> Computation c t (D c r t)
  (-) a b = a `plus` negate b

data Add = Add deriving Show

data Negate = Negate deriving Show



instance (AdditiveBasisConstraints s r Float) => AdditiveMagma (Computation s Float (D s r Float)) (Computation s Float (D s r Float)) r Float where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance (AdditiveBasisConstraints s r Float) => AdditiveMagma (Computation s Float (D s r Float)) (D s r Float) r Float where
  plus a b = do
    aa <- a
    binOp Add aa b

instance (AdditiveBasisConstraints s r Float) => AdditiveMagma (D s r Float) (Computation s Float (D s r Float)) r Float where
  plus a b = do
    bb <- b
    binOp Add a bb

instance (AdditiveBasisConstraints s r Float) => AdditiveMagma (D s r Float) (D s r Float) r Float where
  plus= binOp Add

instance (AdditiveBasisConstraints s r Double) => AdditiveMagma (Computation s Double (D s r Double)) (Computation s Double (D s r Double)) r Double where
  plus a b = do
    aa <- a
    bb <- b
    binOp Add aa bb

instance (AdditiveBasisConstraints s r Double) => AdditiveMagma (Computation s Double (D s r Double)) (D s r Double) r Double where
  plus a b = do
    aa <- a
    binOp Add aa b

instance (AdditiveBasisConstraints s r Double) => AdditiveMagma (D s r Double) (Computation s Double (D s r Double)) r Double where
  plus a b = do
    bb <- b
    binOp Add a bb

instance (AdditiveBasisConstraints s r Double) => AdditiveMagma (D s r Double) (D s r Double) r Double where
  plus = binOp Add

instance (E.Additive a) => BinOp Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b `P.plus` a

-- instance (E.AdditiveBasis r a, E.AdditiveModule r a) => FfBin Add a r where
--   {-# INLINE rff_bin #-}
--   rff_bin _ a b = a E..+. b
--   {-# INLINE r_ff_bin #-}
--   r_ff_bin _ a b = a E..+ b
--   {-# INLINE _ff_bin #-}
--   _ff_bin _ a b = a E.+. b

instance (Operable s r a) => DfDaBin s Add r (D s r a) a where
  {-# INLINE df_da #-}
  df_da _ _ _ _ at = pure at


instance (Operable s r a) =>DfDbBin s Add r (D s r a) a where
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt = pure bt

instance (Operable s r a) =>DfBin s Add r (D s r a) (D s r a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Add a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Add at bt

instance  Trace s Add  r a where
  pushAlg (B _ a b) dA = pure [(dA, a), (dA, b), (dA, a), (dA, b)]
  resetAlg (B _ a b) = pure [a, b, a, b]


instance (AdditiveBasisConstraints [] r Double, Operable [] r Double) =>
         AdditiveUnital (D [] r Double) r Double where
  zero = D (E.map (E.const (0.0 :: Double)) [(0.0 ::Double)..] :: A.Array [] r Double)

instance (AdditiveBasisConstraints [] r Float) => AdditiveUnital  (D [] r Float) r Float where
  zero = D (E.map (E.const (0.0 :: Float)) [(0.0 ::Float)..] :: A.Array [] r Float)

instance (AdditiveBasisConstraints [] r Double) => AdditiveUnital  (Computation [] Double (D [] r Double)) r Double where
  zero = P.pure P.$ D (E.map (E.const (0.0 :: Double)) [(0.0 ::Double)..] :: A.Array [] r Double)

instance (AdditiveBasisConstraints [] r Float) => AdditiveUnital (Computation [] Float (D [] r Float)) r Float where
  zero = P.pure P.$ D (E.map (E.const (0.0 :: Float)) [(0.0 ::Float)..] :: A.Array [] r Float)


instance (AdditiveBasisConstraints s r Double) => AdditiveAssociative (D s r Double) r Double

instance (AdditiveBasisConstraints s r Double) => AdditiveAssociative (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints s r Float) => AdditiveAssociative (D s r Float) r Float

instance (AdditiveBasisConstraints s r Float) => AdditiveAssociative (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints s r Double) => AdditiveCommutative (D s r Double) r Double

instance (AdditiveBasisConstraints s r Float) => AdditiveCommutative (D s r Float) r Float

instance (AdditiveBasisConstraints s r Double) => AdditiveCommutative (Computation s Double (D s r Double)) r Double

instance (AdditiveBasisConstraints s r Float) => AdditiveCommutative (Computation s Float (D s r Float)) r Float

instance (AdditiveBasisConstraints s r Double) => AdditiveInvertible (Computation s Double (D s r Double)) r Double where
  negate a = do
    aa <- a
    monOp Negate aa

instance (AdditiveBasisConstraints s r Float) => AdditiveInvertible  (Computation s Float (D s r Float)) r Float where
  negate a = do
    aa <- a
    monOp Negate aa

instance (AdditiveBasisConstraints s r Double) => AdditiveInvertible  (D s r Double) r Double where
  negate = monOp Negate

instance (AdditiveBasisConstraints s r Float) => AdditiveInvertible   (D s r Float) r Float where
  negate = monOp Negate

instance (E.AdditiveInvertible a, E.Additive a) => FfMon Negate a where
  {-# INLINE ff #-}
  ff _ a = P.negate a

-- instance (E.AdditiveInvertible (r a)) => RffMon Negate r a where
--   {-# INLINE rff #-}
--   rff _ a = P.negate a

instance (E.AdditiveInvertible a, AdditiveInvertible (D s r a) r a ) => MonOp s Negate r a where
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at


instance (AdditiveInvertible (D s r a) r a) => Trace s Negate r a where
  pushAlg (U _ a) dA = do
    cda <- negate dA
    pure [(cda, a)]
  resetAlg (U _ a) = pure [a]


instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (D s r Double) r Double
         ) =>
         Additive (D s r Double) (D s r Double) r Double

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (Computation s Double (D s r Double)) r Double
         , AdditiveUnital (D s r Double) r Double
         ) =>
         Additive (Computation s Double (D s r Double)) (D s r Double) r Double

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (Computation s Double (D s r Double)) r Double
         , AdditiveUnital (D s r Double) r Double
         ) =>
         Additive (D s r Double) (Computation s Double (D s r Double)) r Double

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (D s r Float) r Float
         ) =>
         Additive (D s r Float) (D s r Float) r Float

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (D s r Float) r Float
         , AdditiveUnital (Computation s Float (D s r Float)) r Float
         ) =>
         Additive (D s r Float) (Computation s Float (D s r Float)) r Float

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (D s r Float) r Float
         , AdditiveUnital (Computation s Float (D s r Float)) r Float
         ) =>
         Additive (Computation s Float (D s r Float)) (D s r Float) r Float

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (Computation s Double (D s r Double)) r Double
         , AdditiveUnital (D s r Double) r Double
         ) =>
         Additive (Computation s Double (D s r Double)) (Computation s Double (D s r Double)) r Double


instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (Computation s Float (D s r Float)) r Float
         ) =>
         Additive (Computation s Float (D s r Float)) (Computation s Float (D s r Float)) r Float

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (D s r Double) r Double
         ) =>
         AdditiveGroup (D s r Double) (D s r Double) r Double

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (D s r Double) r Double
         , AdditiveUnital (Computation s Double (D s r Double)) r Double
         ) =>
         AdditiveGroup (Computation s Double (D s r Double)) (D s r Double) r Double

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (D s r Double) r Double
         , AdditiveUnital (Computation s Double (D s r Double)) r Double
         ) =>
         AdditiveGroup (D s r Double) (Computation s Double (D s r Double)) r Double

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (D s r Float) r Float
         ) =>
         AdditiveGroup (D s r Float) (D s r Float) r Float

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (D s r Float) r Float
         , AdditiveUnital (Computation s Float (D s r Float)) r Float
         ) =>
         AdditiveGroup (D s r Float) (Computation s Float (D s r Float)) r Float

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (D s r Float) r Float
         , AdditiveUnital (Computation s Float (D s r Float)) r Float
         ) =>
         AdditiveGroup (Computation s Float (D s r Float)) (D s r Float) r Float

instance ( AdditiveBasisConstraints s r Double
         , AdditiveUnital (Computation s Double (D s r Double)) r Double
         , AdditiveUnital (D s r Double) r Double
         ) =>
         AdditiveGroup (Computation s Double (D s r Double)) (Computation s Double (D s r Double)) r Double

instance ( AdditiveBasisConstraints s r Float
         , AdditiveUnital (Computation s Float (D s r Float)) r Float
         ) =>
         AdditiveGroup (Computation s Float (D s r Float)) (Computation s Float (D s r Float)) r Float


-- | Additive Module Laws
--
-- > (a + b) .+ c == a + (b .+ c)
-- > (a + b) .+ c == (a .+ c) + b
-- > a .+ zero == a
-- > a .+ b == b +. a
class (Additive a b r t) =>
      AdditiveModule r a b t where
  infixl 6 .+
  (.+) ::  a -> b -> Computation c t (D c r t)
  infixl 6 +.
  (+.) :: a -> b -> Computation c t (D c r t)


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule s (Computation c Double (D c s Double)) (D c s Double)  Double where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) a b = do
    ca <- a
    binOp Add ca b

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
  (.+) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb
  (+.) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule s (D c s Double) (D c s Double) Double where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) a b = do
    cb <- b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule s (D c s Float) (D c s Float) Float where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule s (D c s Float) (Computation sc Float  (D c s Float)) Float where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) a b = do
    cb <- b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule s (Computation sc Float  (D c s Float)) (D c s Float)  Float where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) a b = do
    ca <- a
    binOp Add ca b

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule s (Computation sc Float (D c s Float)) (Computation sc Float (D c s Float)) Float where
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
  (.-) ::  a -> b -> Computation c t (D c r t)
  infixl 6 -.
  (-.) ::   a -> b -> Computation c t (D c r t)


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule s (D c s Float) (D c s Float) Float where
  (.-) a b = do
    cb <- (negate b)
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule s (D c s Float) (Computation sc Float  (D c s Float)) Float where
  (.-) a b = do
    cb <- negate b
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule s (Computation sc Float  (D c s Float)) (D c s Float)  Float where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule s (Computation sc Float (D c s Float)) (Computation sc Float (D c s Float)) Float where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb



instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule s (D c s Double) (D c s Double) Double where
  (.-) a b = do
    cb <- (negate b)
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.-) a b = do
    cb <- negate b
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule s (Computation c Double  (D c s Double)) (D c s Double)  Double where
  (.-) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
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
  (.+.) :: a -> b -> Computation c t (D c r t)

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis s (D c s Double) (D c s Double) Double where
  (.+.) a b =
    binOp Add a b


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.+.) a b = do
    cb <-  b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis s (Computation c Double  (D c s Double)) (D c s Double)  Double where
  (.+.) a b = do
    ca <-  a
    binOp Add ca b


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
  (.+.) a b = do
    ca <- a
    cb <-  b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis s (D c s Float) (D c s Float) Float where
  (.+.) a b =
    binOp Add a b


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis s (D c s Float) (Computation sc Float  (D c s Float)) Float where
  (.+.) a b = do
    cb <-  b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis s (Computation sc Float  (D c s Float)) (D c s Float)  Float where
  (.+.) a b = do
    ca <-  a
    binOp Add ca b


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis s (Computation sc Float (D c s Float)) (Computation sc Float (D c s Float)) Float where
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
  (.-.) :: a -> b -> Computation c t (D c r t)

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis s (D c s Float) (D c s Float) Float where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis s (D c s Float) (Computation sc Float  (D c s Float)) Float where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis s (Computation sc Float  (D c s Float)) (D c s Float)  Float where
  (.-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis s (Computation sc Float (D c s Float)) (Computation sc Float (D c s Float)) Float where
  (.-.) a b = do
    ca <- a
    cb <-  negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis s (D c s Double) (D c s Double) Double where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis s (Computation c Double  (D c s Double)) (D c s Double)  Double where
  (.-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
  (.-.) a b = do
    ca <- a
    cb <-  negate b
    binOp Add ca cb
