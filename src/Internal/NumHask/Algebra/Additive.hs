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
  ( -- AdditiveMagma(..)
  -- , AdditiveUnital(..)
  -- , AdditiveAssociative
  -- , AdditiveCommutative
  AdditiveInvertible(..)
  -- , AdditiveIdempotent
  -- , sum
  -- , Additive(..)
  -- , AdditiveRightCancellative(..)
  -- , AdditiveLeftCancellative(..)
  -- , AdditiveGroup(..)
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


data Add = Add deriving Show

data Negate = Negate deriving Show

instance (E.Additive a) => BinOp Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b `P.plus` a

instance (E.AdditiveBasis r a, E.AdditiveModule r a) => FfBin Add a r where
  {-# INLINE rff_bin #-}
  rff_bin _ a b = a E..+. b
  {-# INLINE r_ff_bin #-}
  r_ff_bin _ a b = a E..+ b
  {-# INLINE _ff_bin #-}
  _ff_bin _ a b = a E.+. b

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


-- data Ladd = Ladd deriving Show

-- instance (E.Additive b, E.AdditiveGroup a) => BinOp Ladd a where
--   {-# INLINE ff_bin #-}
--   ff_bin _ a b = b P..+ a

-- instance (E.AdditiveBasis r a, E.AdditiveModule r a) => FfBin Add a r where
--   {-# INLINE rff_bin #-}
--   rff_bin _ a b = a E..+. b
--   {-# INLINE r_ff_bin #-}
--   r_ff_bin _ a b = a E..+ b
--   {-# INLINE _ff_bin #-}
--   _ff_bin _ a b = a E.+. b

-- instance (Operable s r a) => DfDaBin s Ladd r (D s r a) a where
--   {-# INLINE df_da #-}
--   df_da _ _ _ _ at = pure at


-- instance (Operable s r a) =>DfDbBin s Ladd r (D s r a) a where
--   {-# INLINE df_db #-}
--   df_db _ _ _ _ bt = pure bt

-- instance (Operable s r a) =>DfBin s Ladd r (D s r a) (D s r a) a where
--   {-# INLINE fd_bin #-}
--   fd_bin _ a b = binOp Add a b
--   {-# INLINE df_dab #-}
--   df_dab _ _ _ _ _ at _ bt = binOp Ladd at bt

-- instance  Trace s Ladd  r a where
--   pushAlg (B _ a b) dA = pure [(dA, a), (dA, b), (dA, a), (dA, b)]
--   resetAlg (B _ a b) = pure [a, b, a, b]

instance (E.AdditiveInvertible a, E.Additive a) => FfMon Negate a where
  {-# INLINE ff #-}
  ff _ a = P.negate a

instance (AdditiveBasisConstraints s r a) => MonOp s Negate r a where
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at

instance (E.AdditiveInvertible (A.Array c r a))=> RffMon Negate a (A.Array c r) where
  rff _ a = P.negate a

instance (AdditiveBasisConstraints s r a) => Trace s Negate r a where
  pushAlg (U _ a) dA = do
    cda <- monOp Negate dA
    pure [(cda, a)]
  resetAlg (U _ a) = pure [a]


class AdditiveInvertible c r a t | a -> t, a -> r where
  negate :: a -> Computation c t (D c r t)

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveInvertible c s (Computation c Double (D c s Double)) Double where
  negate a = do
    ca <- a
    monOp Negate ca

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveInvertible c s (Computation c Float (D c s Float)) Float where
  negate a = do
    ca <- a
    monOp Negate ca

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveInvertible c s (D c s Float) Float where
  negate a = monOp Negate a

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveInvertible c s (D c s Double) Double where
  negate a = monOp Negate a
    

-- | Additive Module Laws
--
-- > (a + b) .+ c == a + (b .+ c)
-- > (a + b) .+ c == (a .+ c) + b
-- > a .+ zero == a
-- > a .+ b == b +. a
class 
      AdditiveModule c r a b t | a -> t, b -> t, a b -> t, a -> r where
  infixl 6 .+
  (.+) ::  a -> b -> Computation c t (D c r t)
  infixl 6 +.
  (+.) :: b -> a -> Computation c t (D c r t)

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule c s (Computation c Double (D c s Double)) (D c s Double)  Double where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) b a = do
    ca <- a
    binOp Add ca b

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule c s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
  (.+) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb
  (+.) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule c s (D c s Double) (D c s Double) Double where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule c s  (D c s Double) Double Double where
  (.+) a b = binOp Add a (D b)
  (+.) a b = binOp Add (D a) b

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule c s (Computation c Double  (D c s Double)) Double Double where
  (.+) a b = do
    ca <- a
    binOp Add ca (D b)
  (+.) a b = do
    cb <- b
    binOp Add (D a) cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule c s  (D c s Float) Float Float where
  (.+) a b = binOp Add a (D b)
  (+.) a b = binOp Add (D a) b

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule c s (Computation c Float  (D c s Float)) Float Float where
  (.+) a b = do
    ca <- a
    binOp Add ca (D b)
  (+.) a b = do
    cb <- b
    binOp Add (D a) cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveModule c s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) b a = do
    cb <- b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule c s (D c s Float) (D c s Float) Float where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule c s (D c s Float) (Computation c Float  (D c s Float)) Float where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) b a = do
    cb <- b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule c s (Computation c Float  (D c s Float)) (D c s Float)  Float where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) b a = do
    ca <- a
    binOp Add ca b

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveModule c s (Computation c Float (D c s Float)) (Computation c Float (D c s Float)) Float where
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
class 
      AdditiveGroupModule c r a b t | a -> t, b -> t, a b -> t, a -> r where
  infixl 6 .-
  (.-) ::  a -> b -> Computation c t (D c r t)
  infixl 6 -.
  (-.) :: b  -> a -> Computation c t (D c r t)


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule c s (D c s Float) (D c s Float) Float where
  (.-) a b = do
    cb <- (negate b)
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule c s (D c s Float) (Computation c Float  (D c s Float)) Float where
  (.-) a b = do
    cb <-negate b
    binOp Add a cb
  (-.) b a = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule c s (Computation c Float  (D c s Float)) (D c s Float)  Float where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) b a = do
    ca <- a
    cb <- negate b
    binOp Add ca cb

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupModule c s (Computation c Float (D c s Float)) (Computation c Float (D c s Float)) Float where
  (.-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb
  (-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb



instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule c s (D c s Double) (D c s Double) Double where
  (.-) a b = do
    cb <- (negate b)
    binOp Add a cb
  (-.) a b = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule c s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.-) a b = do
    cb <- negate b
    binOp Add a cb
  (-.) b a = do
    cb <- negate b
    binOp Add a cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule c s (Computation c Double  (D c s Double)) (D c s Double)  Double where
  (.-) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb
  (-.) b a = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupModule c s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
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
class 
      AdditiveBasis c r a b t | a b -> r, a b -> t where
  infixl 7 .+.
  (.+.) :: a -> b -> Computation c t (D c r t)

instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis c s (D c s Double) (D c s Double) Double where
  (.+.) a b =
    binOp Add a b


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis c s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.+.) a b = do
    cb <-  b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis c s (Computation c Double  (D c s Double)) (D c s Double)  Double where
  (.+.) a b = do
    ca <-  a
    binOp Add ca b


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveBasis c s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
  (.+.) a b = do
    ca <- a
    cb <-  b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis c s (D c s Float) (D c s Float) Float where
  (.+.) a b =
    binOp Add a b


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis c s (D c s Float) (Computation c Float  (D c s Float)) Float where
  (.+.) a b = do
    cb <-  b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis c s (Computation c Float  (D c s Float)) (D c s Float)  Float where
  (.+.) a b = do
    ca <-  a
    binOp Add ca b


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveBasis c s (Computation c Float (D c s Float)) (Computation c Float (D c s Float)) Float where
  (.+.) a b = do
    ca <- a
    cb <-  b
    binOp Add ca cb



-- | element by element subtraction
--
-- > a .-. a = singleton zero
class 
      AdditiveGroupBasis c r a b t | a b -> r, a b -> t where
  infixl 6 .-.
  (.-.) :: a -> b -> Computation c t (D c r t)

instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis c s (D c s Float) (D c s Float) Float where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis c s (D c s Float) (Computation c Float  (D c s Float)) Float where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis c s (Computation c Float  (D c s Float)) (D c s Float)  Float where
  (.-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Float) =>
         AdditiveGroupBasis c s (Computation c Float (D c s Float)) (Computation c Float (D c s Float)) Float where
  (.-.) a b = do
    ca <- a
    cb <-  negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis c s (D c s Double) (D c s Double) Double where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis c s (D c s Double) (Computation c Double  (D c s Double)) Double where
  (.-.) a b = do
    cb <- negate b
    binOp Add a cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis c s (Computation c Double  (D c s Double)) (D c s Double)  Double where
  (.-.) a b = do
    ca <-  a
    cb <- negate b
    binOp Add ca cb


instance (AdditiveBasisConstraints c s Double) =>
         AdditiveGroupBasis c s (Computation c Double (D c s Double)) (Computation c Double (D c s Double)) Double where
  (.-.) a b = do
    ca <- a
    cb <-  negate b
    binOp Add ca cb
