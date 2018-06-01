{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -freduction-depth=1000 #-}
-- | A magma heirarchy for multiplication. The basic magma structure is repeated and prefixed with 'Multiplicative-'.
module Internal.NumHask.Algebra.Multiplicative
  ( MultiplicativeMagma(..)
  -- , MultiplicativeUnital(..)
  -- , MultiplicativeAssociative
  -- , MultiplicativeCommutative
  , MultiplicativeInvertible(..)
  -- , product
  , Multiplicative(..)
  -- , MultiplicativeRightCancellative(..) 
  -- , MultiplicativeLeftCancellative(..)
  , MultiplicativeGroup(..)
  , MultiplicativeGroupModule(..)
  , MultiplicativeBasis(..)
  -- , BasisConstraints
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

class ( DArray c (GetShape a) t
      , DArray c (GetShape b) t
      , BinOp c Multiply (GetShape a) (GetShape b) t
      , P.Monad m
      ) =>
      MultiplicativeMagma m c a b t | a b -> t, a -> t, b -> t, a b -> c where
  times ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)



class (DArray c (GetShape a) t, P.Monad m, IsMonOp Recip c (GetShape a) t) =>
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

instance (DArray c r a) => Trace c Recip r a where
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
         , DArray c ar t
         , DArray c br t
         , BinOp c Multiply ar br t
         , m ~ m'
         , m' ~ m''
         , ScalarAlg ar br) =>
         MultiplicativeMagma m c (ComputationT c t m' (D c ar t)) (ComputationT c t m' (D c br t)) t where
  times a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance ( P.Monad m
         , DArray c ar t
         , DArray c br t
         , BinOp c Multiply ar br t
         , m ~ m'
         , ScalarAlg ar br) =>
         MultiplicativeMagma m c (ComputationT c t m' (D c ar t)) (D c br t) t where
  times a b = do
    aa <- a
    binOp Multiply aa b

instance ( P.Monad m
         , DArray c ar t
         , DArray c br t
         , BinOp c Multiply ar br t
         , m ~ m'
         , ScalarAlg ar br) =>
         MultiplicativeMagma m c (D c ar t) (ComputationT c t m' (D c br t)) t where
  times a b = do
    bb <- b
    binOp Multiply a bb

instance (IsScalar r, P.Monad m, DArray c ar t
         , DArray c br t, BinOp c Multiply ar br t) =>
         MultiplicativeMagma m c (D c ar t) (D c br t) t where
  times = binOp Multiply


instance ( P.Additive t
         , P.Multiplicative t
         , Dim.Dimensions ar
         , Dim.Dimensions br
         -- 
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


instance ( DArray s ar a
         , DArray s br a
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

instance ( DfOperable Multiply c ar br t
         , BinOp c Multiply ar br t
         , ScalarAlg ar br
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         ) =>
         DfDbBin c Multiply ar br t where
  {-# INLINE df_db #-}
  df_db _ a _ _ bt = handleScalarBroadcast go a bt
    where
      go a bt = binOp Multiply a bt


instance ( DfOperable Multiply c ar br a
         , BinOp c Multiply ar br a
         , ScalarAlg br ar
         , P.AdditiveInvertible a
         , P.MultiplicativeGroup a
         ) =>
         DfDaBin c Multiply ar br a where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = handleScalarBroadcast go b at
    where
      go b at = binOp Multiply b at


instance ( DfOperable Divide c ar br t
         , BinOp c Divide br ar t
         , ScalarAlg ar br
         ,  P.AdditiveInvertible t, P.MultiplicativeGroup t
         ) =>
         DfDaBin c Divide ar br t where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = handleScalarBroadcast go b at
    where
      go at b = binOp Divide at b

instance ( DfOperable Divide c ar br t
         , P.Multiplicative t
         , P.AdditiveInvertible t
         , ScalarAlg ar br
         ,  P.AdditiveInvertible t, P.MultiplicativeGroup t
         ) =>
         DfDbBin c Divide ar br t where
  {-# INLINE df_db #-}
  df_db _ a cp bp bt = handleScalarBroadcast go a bt
    where
      go a bt = do
        bt' <- negate bt --(monOp Negate bt)
        cpbp <- cp / bp -- (binOp Divide cp bp)
        bt' / cpbp -- binOp Divide bt' cpbp


instance ( DfOperable Divide c ar br t
         , IsBinOp c Divide (ScalarShapeAlg ar br) (ScalarShapeAlg ar br) t
         , IsBinOp c Divide ar ar t
         , IsBinOp c Divide br br t
         , P.Multiplicative t
         , P.AdditiveInvertible t
         
         , ScalarAlg ar br
         , P.MultiplicativeGroup t
         ) =>
         DfBin c Divide ar br t where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = a / b -- binOp Divide a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ cp ap at bp bt = do
    nbt <- negate bt -- binOp Negate bt
    catbt <- binOp Add at nbt
    ccp <- catbt * cp -- binOp Multiply catbt cp
    ccp / bp -- binOp Divide (ccp) bp

instance ( DArray c r t
         , P.Multiplicative t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         --
         ) =>
         Trace c Multiply r t where
  pushAlg ::
       (E.Monad m, BinOp c Multiply cr r t, DArray c cr t)
    => TraceStack c op r t
    -> D c cr t
    -> ComputationT c t m [(SomeD c t, SomeD c t)]
  pushAlg (B _ (a :: D c ar t) (b :: D c br t)) dA
    -- cdA <- pure dA
   = do
    opa <-  dA * (p b)
    opb <-  dA * (p a)
    arga <- scalarAlg (binOp Multiply) dA b
    argb <- scalarAlg (binOp Multiply) dA a
    pure
      [ (SomeD opa, SomeD a)
      , (SomeD opb, SomeD b)
      , (SomeD arga, SomeD a)
      , (SomeD argb, SomeD b)
      ]

instance ( DArray c r t
         , P.Multiplicative t
         , P.MultiplicativeGroup t
         , P.AdditiveInvertible t
         ) =>
         Trace c Divide r t where
  pushAlg (B _ a b) dA
    -- cdA <- pure dA
   = do
    opa <- dA / p b -- binOp Divide dA (p b) --
    pa' <- (negate (p a))
    a'b' <- (binOp Divide pa' (p b)) * p b
    opb <- binOp Multiply dA a'b'
    arga <- dA * b
    argb <- dA * a
    pure
      [ (SomeD opa, SomeD a)
      , (SomeD opb, SomeD b)
      , (SomeD arga, SomeD a)
      , (SomeD argb, SomeD b)
      ]

instance ( P.Multiplicative t
         , P.MultiplicativeGroup t
         , P.AdditiveInvertible t
         , DfOperable Multiply c ar br t
         , ScalarAlg ar br
         ) =>
         BinOp c Multiply ar br t 

instance ( P.Multiplicative t
         , P.MultiplicativeGroup t
         , P.AdditiveInvertible t
         , DfOperable Divide c ar br t
         , ScalarAlg ar br 
         ) =>
         BinOp c Divide ar br t

instance (P.Additive t, Dim.Dimensions ar, Dim.Dimensions br, P.Multiplicative t, P.MultiplicativeGroup t) => BinBaseOp Divide ar br t where
  type BinCalcShape ar br = ScalarShapeAlg ar br
  baseOpBin _ (D a) (D b) = D $ a P./ b
  baseOpBin _ (Dm a) (D b) = Dm $ a P../ b
  baseOpBin _ (D a) (Dm b) = Dm $ a P./. b
  baseOpBin _ (Dm a) (Dm b) =
    case Dim.sameDim (Dim.dim @ar) (Dim.dim @br) of
      P.Just Dim.Evidence -> Dm $ a P../. b
      P.Nothing ->
        GHC.Err.error
          "Dimensions of arguments to binOp should have been equal: Please report this as a bug in diffhask."


instance ( P.Monad m
         , DfOperable Divide c ar br t
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg ar br
         ) =>
         Multiplicative m c (D c ar t) (D c br t) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         Multiplicative m c (D c ar t) (ComputationT c t m (D c br t)) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         Multiplicative m c (ComputationT c t m (D c ar t)) (D c br t) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         Multiplicative m c (ComputationT c t m (D c ar t)) (ComputationT c t m (D c br t)) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         MultiplicativeGroup m c (D c ar t) (D c br t) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         MultiplicativeGroup m c (D c ar t) (ComputationT c t m (D c br t)) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         MultiplicativeGroup m c (ComputationT c t m (D c ar t)) (D c br t) t

instance ( P.Monad m
         , DfOperable Multiply c ar br t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         
         , ScalarAlg ar br) =>
         MultiplicativeGroup m c (ComputationT c t m (D c ar t)) (ComputationT c t m (D c br t)) t


class ('[] ~ (GetShape b)) =>
      MultiplicativeModule m c a b t where
  infixl 7 .*
  (.*) ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)
  infixl 7 *.
  (*.) ::
       b
    -> a
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)


instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg r '[] ~ ScalarAlg '[] r
         , ScalarAlg ar br) =>
         MultiplicativeModule m c (D c r t) (D c '[] t) t where
  (.*) a b = binOp Multiply a b
  (*.) b a = binOp Multiply a b

instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , m ~ m'
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg r '[] ~ ScalarAlg '[] r
         , ScalarAlg ar br) =>
         MultiplicativeModule m c (D c r t) (ComputationT c t m' (D c '[] t)) t where
  (.*) a b = do
    cb <- b
    binOp Multiply a cb
  (*.) b a = do
    cb <- b
    binOp Multiply a cb

instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , m ~ m'
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg r '[] ~ ScalarAlg '[] r
         , ScalarAlg ar br) =>
         MultiplicativeModule m c (ComputationT c t m' (D c r t)) (D c '[] t) t where
  (.*) a b = do
    ca <- a
    binOp Multiply ca b
  (*.) b a = do
    ca <- a
    binOp Multiply ca b

instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , m ~ m'
         , m' ~ m''
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg r '[] ~ ScalarAlg '[] r
         , ScalarAlg ar br) =>
         MultiplicativeModule m c (ComputationT c t m' (D c r t)) (ComputationT c t m'' (D c '[] t)) t where
  (.*) a b = do
    ca <- a
    cb <- b
    binOp Multiply ca cb
  (*.) b a = do
    ca <- a
    cb <- b
    binOp Multiply ca cb


class (P.Monad m, '[] ~ (GetShape b)) =>
      MultiplicativeGroupModule m c a b t where
  infixl 7 ./
  (./) ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)
  infixl 7 /.
  (/.) ::
       b
    -> a
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) ((GetShape b))) t)


instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg ar br) =>
         MultiplicativeGroupModule m c (D c r t) (D c '[] t) t where
  (./) a b = binOp Divide a b
  (/.) a b = binOp Divide a b

instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , ScalarAlg ar br) =>
         MultiplicativeGroupModule m c (D c r t) (ComputationT c t m' (D c '[] t)) t where
  (./) a b = do
    cb <- b
    binOp Divide a cb
  (/.) a b = do
    ca <- a
    binOp Divide ca b

instance (P.Monad m
         , DfOperable Multiply c r '[] t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t,
           m ~ m') =>
         MultiplicativeGroupModule m c (ComputationT c t m' (D c r t)) (D c '[] t) t where
  (./) a b = do
    ca <- a
    binOp Divide ca b
  (/.) a b = do
    cb <-  b
    binOp Divide a cb

instance ( P.Monad m
         , DfOperable Multiply c r '[] t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , m' ~ m''
         , ScalarAlg ar br) =>
         MultiplicativeGroupModule m c (ComputationT c t m' (D c r t)) (ComputationT c t m'' (D c '[] t)) t where
  (./) a b = do
    ca <- a
    cb <- b
    binOp Divide ca cb
  (/.) a b = do
    ca <- a
    cb <- b
    binOp Divide ca cb

class (P.Monad m, GetShape a ~ GetShape b) =>
      MultiplicativeBasis m c a b t where
  infixl 7 .*.
  (.*.) :: a -> b -> ComputationT c t m (D c (GetShape a) t)


instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , ScalarAlg ar br) =>
         MultiplicativeBasis m c (D c r t) (D c r t) t where
  (.*.) a b = binOp Multiply a b

instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , ScalarAlg ar br) =>
         MultiplicativeBasis m c (D c r t) (ComputationT c t m' (D c r t)) t where
  (.*.) a b = do
    cb <- b
    binOp Multiply a cb


instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , ScalarAlg ar br) =>
         MultiplicativeBasis m c (ComputationT c t m' (D c r t)) (D c r t) t where
  (.*.) a b = do
    ca <- a
    binOp Multiply ca b


instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , m' ~ m''
         , ScalarAlg ar br) =>
         MultiplicativeBasis m c (ComputationT c t m' (D c r t)) (ComputationT c t m'' (D c r t)) t where
  (.*.) a b = do
    ca <- a
    cb <- b
    binOp Multiply ca cb


class (P.Monad m, GetShape a ~ GetShape b) =>
      MultiplicativeGroupBasis m c a b t where
  infixl 7 ./.
  (./.) :: a -> b -> ComputationT c t m (D c (GetShape a) t)

instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t) => MultiplicativeGroupBasis m c (D c r t) (D c r t) t where
  (./.) a b = binOp Divide a b

instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , m' ~ m''
         ) => MultiplicativeGroupBasis m c (D c r t) (ComputationT c t m' (D c r t)) t where
  (./.) a b = do
    cb <- b
    binOp Divide a cb


instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , m' ~ m''
         ) => MultiplicativeGroupBasis m c (ComputationT c t m' (D c r t)) (D c r t) t where
  (./.) a b = do
    ca <- a
    binOp Divide ca b


instance ( P.Monad m
         , DfOperable Multiply c r r t
         , P.AdditiveInvertible t
         , P.MultiplicativeGroup t
         , m ~ m'
         , m' ~ m''
         ) => MultiplicativeGroupBasis m c (ComputationT c t m' (D c r t)) (ComputationT c t m'' (D c r t)) t where
  (./.) a b = do
    ca <- a
    cb <- b
    binOp Divide ca cb


