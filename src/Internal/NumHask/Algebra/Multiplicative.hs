{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -freduction-depth=1000 #-}
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
  , MultiplicativeGroupModule(..)
  , MultiplicativeBasis(..)
  , BasisConstraints
  , Multiply(..)
  , Divide(..)
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           NumHask.Prelude                   (Bool (..), Double, Float,
                                                    Int, Integer, Show, pure,
                                                    ($))
import qualified Numeric.Dimensions as Dim
import qualified Numeric.Dimensions.Dim as Dim
import Data.Proxy (Proxy(..))
import qualified NumHask.Prelude                   as P
import qualified NumHask.Prelude                   as E
import qualified NumHask.Array as A
import GHC.Err

data Recip = Recip deriving Show

class ( Operable c (GetShape a) t
      , Operable c (GetShape b) t
      , BinOp c Multiply (GetShape a) (GetShape b) t
      , P.Monad m
      ) =>
      MultiplicativeMagma m c a b t | a b -> t, a -> t, b -> t, a b -> c where
  times ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)



class (Operable c (GetShape a) t, P.Monad m, IsMonOp Recip c (GetShape a) t) =>
      MultiplicativeInvertible m c a t | a -> t, a -> c where
  recip :: a -> ComputationT c t m (D c '[] t)

instance (P.Monad m, IsMonOp Recip c '[] t) =>
         MultiplicativeInvertible m c (D c '[] t) t where
  recip a = do
    monOp Recip a

instance (P.Monad m, IsMonOp Recip c '[] t, m ~ m') =>
         MultiplicativeInvertible m c (ComputationT c t m' (D c '[] t)) t where
  recip a = do
    ca <- a
    monOp Recip ca


instance (IsMonOp Recip s r a) => MonOp s Recip r a where
  {-# INLINE fd #-}
  fd _ a = monOp Recip a
  {-# INLINE df #-}
  df _ _ _ at = monOp Recip at

instance ( P.MultiplicativeInvertible t
         , P.Additive t
         , P.AdditiveInvertible t
         , Dim.Dimensions ar
         ) =>
         MonBaseOp Recip ar t where
  type MonCalcShape ar = ar
  baseOpMon _ (D v) = D $ P.recip v
  baseOpMon _ (Dm v) = Dm $ P.recip v

instance (Operable c r a) => Trace c Recip r a where
  pushAlg (U _ a) dA = P.pure [(SomeD dA, SomeD a)]

-- product ::
--      (Multiplicative m c a a t, P.Foldable f)
--   => f a
--   -> ComputationT c t m (D c r t)
-- product = P.foldr (*) P.one


class ( P.Monad m
      , BinOp c Multiply (GetShape a) (GetShape b) t
      , MultiplicativeMagma m c a b t
      ) =>
      Multiplicative m c a b t where
  infixl 7 *
  (*) ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)
  a * b = times a b

-- class (MultiplicativeMagma m c a b t, MultiplicativeInvertible m c a t) =>
--       MultiplicativeLeftCancellative m c a b t where
--   infixl 7 ~/
--   (~/) :: a -> b -> ComputationT c t m (D c r t)
--   a ~/ b = do
--     rb <- monOp Recip b
--     rb `times` a


-- class (MultiplicativeMagma m c a b t, MultiplicativeInvertible m c a t) =>
--       MultiplicativeRightCancellative m c a b t where
--   infixl 7 /~
--   (/~) :: a -> b -> ComputationT c t m (D c r t)
--   a /~ b = do
--     rb <- monOp Recip b
--     a `times` rb

class ( IsBinOp c Divide (GetShape a) (GetShape b) t
      , P.Monad m
      , BinOp c Multiply (GetShape a) (GetShape b) t
      ) =>
      MultiplicativeGroup m c a b t where
  infixl 7 /
  (/) ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)



data Multiply = Multiply deriving Show
data Divide = Divide deriving Show

instance (P.Monad m
         , Operable c ar t
         , Operable c br t
         , BinOp c Multiply ar br t
         , m ~ m'
         , m' ~ m''
         ) =>
         MultiplicativeMagma m c (ComputationT c t m' (D c ar t)) (ComputationT c t m' (D c br t)) t where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance ( P.Monad m
         , Operable c ar t
         , Operable c br t
         , BinOp c Multiply ar br t
         , m ~ m'
         ) =>
         MultiplicativeMagma m c (ComputationT c t m' (D c ar t)) (D c br t) t where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance ( P.Monad m
         , Operable c ar t
         , Operable c br t
         , BinOp c Multiply ar br t
         , m ~ m'
         ) =>
         MultiplicativeMagma m c (D c ar t) (ComputationT c t m' (D c br t)) t where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance (Scalar r, P.Monad m, Operable c ar t
         , Operable c br t, BinOp c Multiply ar br t) =>
         MultiplicativeMagma m c (D c ar t) (D c br t) t where
  times = binOp Multiply


instance ( P.Additive t
         , P.Multiplicative t
         , Dim.Dimensions ar
         , Dim.Dimensions br
         ) =>
         BinBaseOp Multiply ar br t where
  type BinCalcShape ar br = ScalarShapeAlg ar br
  baseOpBin _ (D a) (D b) = D $ a P.* b
  baseOpBin _ (Dm a) (D b) = Dm $ a P..* b
  baseOpBin _ (D a) (Dm b) = Dm $ a P.*. b
  baseOpBin _ (Dm a) (Dm b) =
    case Dim.sameDim (Dim.dim @ar) (Dim.dim @br) of
      P.Just Dim.Evidence -> Dm $ a P..*. b
      P.Nothing ->
        GHC.Err.error
          "Dimensions of arguments to binOp should have been equal: Please report this as a bug in diffhask."


instance ( Operable s ar a
         , Operable s br a
         , BinOp s Multiply ar br a
         , Trace s Multiply ar a
         , Trace s Multiply br a
         , Trace s Multiply (BinCalcShape ar br) a
         ) =>
         DfBin s Multiply ar br a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Multiply a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Multiply at bt

instance (DfOperable Multiply c ar br t, BinOp c Multiply ar br t) => DfDbBin c Multiply ar br t
  -- type DfDbShape ar br = ScalarShapeAlg ar br
                                                 where
  {-# INLINE df_db #-}
  df_db _ a _ _ bt = handleScalarBroadcast go a bt
    where
      go a bt = binOp Multiply a bt


instance ( DfOperable Multiply c ar br a
         , BinOp c Multiply br ar a
         , ScalarShapeAlg ar br ~ ScalarShapeAlg br ar
         ) =>
         DfDaBin c Multiply ar br a
  -- type DfDaShape ar br = ScalarShapeAlg ar br
                                                 where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = handleScalarBroadcast go b at
    where
      go b at = binOp Multiply b at


instance ( DfOperable Divide c ar br t
         , BinOp c Divide br ar t
         , ScalarShapeAlg ar br ~ ScalarShapeAlg br ar
         ) =>
         DfDaBin c Divide ar br t where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = handleScalarBroadcast go b at
    where
      go at b = binOp Divide at b

instance ( DfOperable Divide c ar br t
         --, BinOp c Divide (ScalarShapeAlg br ar) br t
         , P.Multiplicative t
         , P.AdditiveInvertible t
         , ScalarShapeAlg ar br ~ ScalarShapeAlg br ar
         , (ScalarShapeAlg br (ScalarShapeAlg (ScalarShapeAlg br ar) br) ~ ScalarShapeAlg br ar)
         ) =>
         DfDbBin c Divide ar br t where
  {-# INLINE df_db #-}
  df_db _ a cp bp bt = handleScalarBroadcast go a bt
    where
      go a bt = do
        bt' <- negate bt --(monOp Negate bt)
        cpbp <- (binOp Divide cp bp)
        binOp Divide bt' cpbp


instance (DfOperable Divide c ar br t) => DfBin c Divide ar br t where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Divide a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ cp ap at bp bt = do
    nbt <- binOp Negate bt
    catbt <- binOp Add at nbt
    ccp <- binOp Multiply catbt cp
    binOp Divide (ccp) bp

-- instance Trace c Divide r t where
--   pushAlg (B _ a b) dA = do
--     cdA <- pure dA
--     opa <- cdA / p b
--     opb <- cdA * (((negate (p a)) / p b) * p b)
--     arga <- cdA * b
--     argb <- cdA * a
--     pure [(opa, a), (opb, b), (arga, a), (argb, b)]
 

instance (DfOperable Multiply c ar br t) =>
         Multiplicative m c (D c ar t) (D c br t) t

instance (DfOperable Multiply c ar br t) =>
         Multiplicative m c (D c ar t) (ComputationT c t m (D c br t)) t

instance (DfOperable Multiply c ar br t) =>
         Multiplicative m c (ComputationT c t m (D c ar t)) (D c br t) t

instance (DfOperable Multiply c ar br t) =>
         Multiplicative m c (ComputationT c t m (D c ar t)) (ComputationT c t m (D c br t)) t

instance (DfOperable Multiply c ar br t) =>
         MultiplicativeGroup m c (D c ar t) (D c br t) t

instance (DfOperable Multiply c ar br t) =>
         MultiplicativeGroup m c (D c ar t) (ComputationT c t m (D c br t)) t

instance (DfOperable Multiply c ar br t) =>
         MultiplicativeGroup m c (ComputationT c t m (D c ar t)) (D c br t) t

-- instance (DfOperable Multiply c ar br t) =>
--          MultiplicativeGroup m c (ComputationT c t m (D c ar t)) (ComputationT c t m (D c br t)) t

instance (DfOperable Multiply c ar br t) =>
         MultiplicativeGroup m c (ComputationT c t m (D c ar t)) (ComputationT c t m (D c br t)) t


class (Multiplicative m c a b t, Scalar (GetShape b) ) =>
      MultiplicativeModule m c a b t where
  infixl 7 .*
  (.*) :: a -> b -> ComputationT c t m (D c r t)
  infixl 7 *.
  (*.) :: b -> a -> ComputationT c t m (D c r t)


instance (DfOperable Multiply c r '[] t) =>
         MultiplicativeModule m c (D c r t) (D c '[] t) t where
  (.*) a b = binOp Multiply a b
  (*.) b a = binOp Multiply a b

instance (DfOperable Multiply c r '[] t, m ~ m') =>
         MultiplicativeModule m c (D c r t) (ComputationT c a m' (D c '[] t)) t where
  (.*) a b = do
    cb <- b
    binOp Multiply a cb
  (*.) b a = do
    cb <- b
    binOp Multiply a cb

instance (DfOperable Multiply c r '[] t, m ~ m') =>
         MultiplicativeModule m c (ComputationT c a m' (D c r t)) (D c '[] t) t where
  (.*) a b = do
    ca <- a
    binOp Multiply ca b
  (*.) b a = do
    ca <- a
    binOp Multiply ca b

instance (DfOperable Multiply c r '[] t, m ~ m', m' ~ m'') =>
         MultiplicativeModule m c (ComputationT c a m' (D c r t)) (ComputationT c a m'' (D c '[] t)) t where
  (.*) a b = do
    ca <- a
    cb <- b
    binOp Multiply ca cb
  (*.) b a = do
    ca <- a
    cb <- b
    binOp Multiply ca cb


-- class (MultiplicativeGroup m c a b t, Scalar (GetShape b) ) =>
--       MultiplicativeGroupModule m c a b t where
--   infixl 7 ./
--   (./) :: a -> b -> ComputationT c t m (D c r t)
--   infixl 7 /.
--   (/.) :: b -> a -> ComputationT c t m (D c r t)


-- instance MultiplicativeGroupModule m c (D c r t) (D c '[] t) t where
--   (./) a b = do
--     cb <- (recip b)
--     binOp Multiply a cb
--   (/.) a b = do
--     cb <- recip b
--     binOp Multiply a cb

-- instance(m ~ m') =>  MultiplicativeGroupModule m c (D c r t) (ComputationT c a m' (D c '[] t)) t where
--   (./) a b = do
--     cb <- recip b
--     binOp Multiply a cb
--   (/.) a b = do
--     cb <- recip b
--     binOp Multiply a cb

-- instance (m ~ m') =>
--          MultiplicativeGroupModule m c (ComputationT c a m' (D c r t)) (D c '[] t) t where
--   (./) a b = do
--     ca <- a
--     cb <- recip b
--     binOp Multiply ca cb
--   (/.) a b = do
--     ca <- a
--     cb <- recip b
--     binOp Multiply ca cb

-- instance (m ~ m', m' ~ m'') =>
--          MultiplicativeGroupModule m c (ComputationT c a m' (D c r t)) (ComputationT c a m'' (D c '[] t)) t where
--   (./) a b = do
--     ca <- a
--     cb <- recip b
--     binOp Multiply ca cb
--   (/.) a b = do
--     ca <- a
--     cb <- recip b
--     binOp Multiply ca cb

-- class (Multiplicative m c a b t) =>
--       MultiplicativeBasis m c a b t where
--   infixl 7 .*.
--   (.*.) :: a -> b -> ComputationT c t m (D c r t)


-- instance MultiplicativeBasis m c (D c r t) (D c r t) t where
--   (.*.) a b = binOp Multiply a b

-- instance MultiplicativeBasis m c (D c r t) (ComputationT c a m (D c r t)) t where
--   (.*.) a b = do
--     cb <- b
--     binOp Multiply a cb


-- instance MultiplicativeBasis m c (ComputationT c a m (D c r t)) (D c r t) t where
--   (.*.) a b = do
--     ca <- a
--     binOp Multiply ca b


-- instance MultiplicativeBasis m c (ComputationT c a m (D c r t)) (ComputationT c a m (D c r t)) t where
--   (.*.) a b = do
--     ca <- a
--     cb <- b
--     binOp Multiply ca cb

-- | element by element division
--
-- > a ./. a == singleton one
-- class (MultiplicativeGroup m c a b t) =>
--       MultiplicativeGroupBasis m c a b t where
--   infixl 7 ./.
--   (./.) :: a -> b -> ComputationT c t m (D c r t)

-- instance MultiplicativeGroupBasis m c (D c r t) (D c r t) t where
--   (./.) a b = binOp Divide a b

-- instance MultiplicativeGroupBasis m c (D c r t) (ComputationT c a m (D c r t)) t where
--   (./.) a b = do
--     cb <- b
--     binOp Divide a cb


-- instance MultiplicativeGroupBasis m c (ComputationT c a m (D c r t)) (D c r t) t where
--   (./.) a b = do
--     ca <- a
--     binOp Divide ca b


-- instance MultiplicativeGroupBasis m c (ComputationT c a m (D c r t)) (ComputationT c a m (D c r t)) t where
--   (./.) a b = do
--     ca <- a
--     cb <- b
--     binOp Divide ca cb
