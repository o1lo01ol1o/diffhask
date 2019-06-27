{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE NoImplicitPrelude       #-}
{-# LANGUAGE OverloadedLists         #-}
{-# LANGUAGE Rank2Types              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeApplications              #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeOperators #-}
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
        , AdditiveGroup(..)
        , AdditiveGroupModule(..)
        , AdditiveBasis(..)
        , AdditiveModule(..)
        , Additive(..)
        , Add(..)
        , Negate(..)
        )
where
import           Internal.Internal
import qualified Numeric.Dimensions            as Dim
import           NumHask.Array                  ( )
import           NumHask.Prelude                ( Show
                                                , ($)
                                                )
import qualified NumHask.Prelude               as P
import qualified Numeric.Dimensions         as Dim
import qualified Numeric.Dimensions.Dim     as Dim


data Negate = Negate deriving Show


class (DArray c '[] t, P.Monad m) =>
      Additive m c a b t | a -> t, b -> t, a b -> t, a b -> c where
  (+) :: a -> b -> ComputationT c t m (D c '[] t)


class ( DArray c '[] t
      , P.Monad m
      , MonCalcShape '[] ~ '[]
      , IsMonOp Negate c '[] t
      ) =>
      AdditiveGroup m c a b t | a -> t, b -> t, a b -> t, a b -> c where
  (-) :: a -> b -> ComputationT c t m (D c '[] t)

instance ( DArray c '[] t
         , P.Monad m
         , MonCalcShape '[] ~ '[]
         , P.AdditiveInvertible t,IsMonOp Negate c '[] t
         ) =>
         AdditiveGroup m c (D c '[] t) (D c '[] t) t where

  (-) a b = do
    nb <- negate b
    binOp Add a nb

instance ( DArray c '[] t
         , P.Monad m
         , MonCalcShape '[] ~ '[]
         , P.AdditiveInvertible t,IsMonOp Negate c '[] t
         , m ~ m'
         ) =>
         AdditiveGroup m c (ComputationT c t m' (D c '[] t)) (D c '[] t) t where
  (-) a b = do
    nb <- negate b
    ca <- a
    binOp Add ca nb

instance ( DArray c '[] t
         , P.Monad m
         , MonCalcShape '[] ~ '[]
         , P.AdditiveInvertible t,IsMonOp Negate c '[] t
         , m ~ m'
         ) =>
         AdditiveGroup m c (D c '[] t) (ComputationT c t m' (D c '[] t)) t where
  (-) a b = do
    cb <- negate b
    binOp Add a cb

instance ( DArray c '[] t
         , P.Monad m
         , MonCalcShape '[] ~ '[]
         , P.AdditiveInvertible t,IsMonOp Negate c '[] t
         , m ~ m'
         , m ~ m''
         ) =>
         AdditiveGroup m c (ComputationT c t m' (D c '[] t)) (ComputationT c t m'' (D c '[] t)) t where
  (-) a b = do
    ca <- a
    cb <- negate b
    binOp Add ca cb

instance (IsMonOp Negate s r a) => MonOp s Negate r a where
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at


class (P.Monad m, P.AdditiveInvertible t, IsMonOp Negate c (GetShape a) t) =>
      AdditiveInvertible m c a t | a -> t, a -> c where
  negate :: a -> ComputationT c t m (D c (MonCalcShape (GetShape a)) t)


instance (P.Monad m, P.AdditiveInvertible t, IsMonOp Negate c r t, m ~ m') =>
         AdditiveInvertible m c (ComputationT c t m' (D c r t)) t where
  negate a = do
    ca <- a
    monOp Negate ca

instance (P.Monad m, P.AdditiveInvertible t, IsMonOp Negate c s t) =>
         AdditiveInvertible m c (D c s t) t where
  negate a = monOp Negate a


instance (P.Additive t, P.AdditiveInvertible t, Dim.Dimensions ar) =>
         MonBaseOp Negate ar t where
  type MonCalcShape ar = ar
  baseOpMon _ (D v)  = D $ P.negate v


instance (DArray c r a) => Trace c Negate r a where
  pushAlg (U _ a) dA = P.pure [(SomeD dA, SomeD a)]

class (P.Monad m, IsTensor (GetShape a), IsBinOp c Add (GetShape a) (GetShape b) t, GetShape b ~ '[]) =>
      AdditiveModule m c a b t | a -> t, b -> t, a b -> t, a b -> c where
  infixl 6 .+
  (.+) ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) (GetShape b)) t)
  infixl 6 +.
  (+.) ::
       b
    -> a
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) (GetShape b)) t)

instance (P.Monad m, IsBinOp c Add (ar : arr) '[] t, m ~ m') =>
         AdditiveModule m c (ComputationT c t m' (D c (ar : arr) t)) (D c '[] t) t where
  (.+) a b = do
    ca <- a
    binOp Add ca b
  (+.) b a = do
    ca <- a
    binOp Add ca b

instance (P.Monad m,  IsBinOp c Add (ar : arr) '[] t, m ~ m', m ~ m'') =>
         AdditiveModule m c (ComputationT c t m' (D c (ar : arr) t)) (ComputationT c t m'' (D c '[] t)) t where
  (.+) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb
  (+.) a b = do
    ca <- a
    cb <- b
    binOp Add cb ca

instance (P.Monad m, IsBinOp c Add (ar : arr) '[] t) =>
         AdditiveModule m c (D c (ar : arr) t) (D c '[] t) t where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add b a

instance (P.Monad m, IsBinOp c Add (ar : arr) '[] t,m ~ m') =>
         AdditiveModule m c (D c (ar : arr) t) (ComputationT c t m' (D c '[] t)) t where
  (.+) a b = do
    cb <- b
    binOp Add a cb
  (+.) b a = do
    cb <- b
    binOp Add a cb

class ( AdditiveModule m c a b t
      , AdditiveInvertible m c a t
      , AdditiveInvertible m c b t
      , GetShape b ~ '[]
      ) =>
      AdditiveGroupModule m c a b t | a -> t, b -> t, a b -> t, a b -> c where
  infixl 6 .-
  (.-) ::
       a
    -> b
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) (MonCalcShape (GetShape b))) t)
  infixl 6 -.
  (-.) ::
       b
    -> a
    -> ComputationT c t m (D c (BinCalcShape (GetShape a) (MonCalcShape (GetShape b))) t)


instance ( P.Monad m
         , IsMonOp Negate c (ar : arr) t
         , IsMonOp Negate c '[] t
         , IsBinOp c Add (ar : arr) '[] t
         , P.AdditiveInvertible t
         ) =>
         AdditiveGroupModule m c (D c (ar : arr) t) (D c '[] t) t where
  (.-) a b = do
    cb <- monOp Negate b
    binOp Add a cb
  (-.) a b = do
    cb <- monOp Negate b
    binOp Add a cb

instance ( P.Monad m
         , IsMonOp Negate c (ar : arr) t
         , IsMonOp Negate c '[] t
         , IsBinOp c Add (ar : arr) '[] t
         , P.AdditiveInvertible t
         , m ~ m') =>
         AdditiveGroupModule m c (D c (ar : arr) t) (ComputationT c t m' (D c '[] t)) t where
  (.-) a cb = do
    b <- cb
    nb <- monOp Negate b
    binOp Add a nb
  (-.) cb a = do
    b <- cb
    nb <- monOp Negate b
    binOp Add a nb

instance ( P.Monad m
         , IsMonOp Negate c (ar : arr) t
         , IsMonOp Negate c '[] t
         , IsBinOp c Add (ar : arr) '[] t
         , P.AdditiveInvertible t
         , m ~ m') =>
         AdditiveGroupModule m c (ComputationT c t m (D c (ar : arr) t)) (D c '[] t) t where
  (.-) a b = do
    ca <- a
    cb <- monOp Negate b
    binOp Add ca cb
  (-.) b a = do
    ca <- a
    cb <- monOp Negate b
    binOp Add ca cb

instance ( P.Monad m
         , IsMonOp Negate c (ar : arr) t
         , IsMonOp Negate c '[] t
         , IsBinOp c Add (ar : arr) '[] t
         , P.AdditiveInvertible t
         , m ~ m'
         , m ~ m'') =>
         AdditiveGroupModule m c (ComputationT c t m' (D c (ar : arr) t)) (ComputationT c t m'' (D c '[] t)) t where

  (.-) a cb = do
    ca <- a
    b <- cb
    nb <- monOp Negate b
    binOp Add ca nb
  (-.) cb a = do
    ca <- a
    b <- cb
    nb <- monOp Negate b
    binOp Add ca nb

class AdditiveBasis m c r a b t | a b -> r, a b -> t, a b -> c where
  infixl 7 .+.
  (.+.) :: a -> b -> ComputationT c t m (D c r t)

instance (P.Monad m, IsBinOp c Add (ar : arr) (ar : arr) t) =>
         AdditiveBasis m c (ar : arr) (D c (ar : arr) t) (D c (ar : arr) t) t where
  (.+.) a b = binOp Add a b


instance (P.Monad m, IsBinOp c Add (ar : arr) (ar : arr) t, m ~ m') =>
         AdditiveBasis m c (ar : arr) (D c (ar : arr) t) (ComputationT c t m' (D c (ar : arr) t)) t where
  (.+.) a b = do
    cb <- b
    binOp Add a cb


instance (P.Monad m, IsBinOp c Add (ar : arr) (ar : arr) t, m ~ m') =>
         AdditiveBasis m c (ar : arr) (ComputationT c t m' (D c (ar : arr) t)) (D c (ar : arr) t) t where

  (.+.) a b = do
    ca <- a
    binOp Add ca b


instance (P.Monad m, IsBinOp c Add (ar : arr) (ar : arr) t, m ~ m', m ~ m'') =>
         AdditiveBasis m c (ar : arr) (ComputationT c t m' (D c (ar : arr) t)) (ComputationT c t m'' (D c (ar : arr) t)) t where
  (.+.) a b = do
    ca <- a
    cb <- b
    binOp Add ca cb




-- | element by element subtraction
--
-- > a .-. a = singleton zero
class ( P.Monad m
     
      , AdditiveInvertible m c b t
      )=>
      AdditiveGroupBasis m c r a b t | a b -> r, a b -> t, a b -> c where
  infixl 6 .-.
  (.-.) :: a -> b -> ComputationT c t m (D c r t)

instance ( P.Monad m
         , IsBinOp c Add (ar : arr) (ar : arr) t
         , P.AdditiveInvertible t, IsMonOp Negate c (ar : arr) t
         ) =>
         AdditiveGroupBasis m c (ar : arr) (D c (ar : arr) t) (D c (ar : arr) t) t where
  (.-.) a b = do
    cb <- monOp Negate b
    binOp Add a cb


instance ( P.Monad m
         , IsBinOp c Add (ar : arr) (ar : arr) t
         , IsMonOp Negate c (ar : arr) t
         , P.AdditiveInvertible t
        
         , m ~ m'

         ) =>
         AdditiveGroupBasis m c (ar : arr) (D c (ar : arr) t) (ComputationT c t m' (D c (ar : arr) t)) t where
  (.-.) a cb = do
    b <- cb
    nb <- monOp Negate b
    binOp Add a nb


instance ( P.Monad m
         , IsBinOp c Add (ar : arr) (ar : arr) t
         , IsMonOp Negate c (ar : arr) t
         , P.AdditiveInvertible t
         , m ~ m'
         ) =>
         AdditiveGroupBasis m c (ar : arr) (ComputationT c t m' (D c (ar : arr) t)) (D c (ar : arr) t) t where

  (.-.) a b = do
    ca <- a
    cb <- monOp Negate b
    binOp Add ca cb


instance ( P.Monad m
         , IsBinOp c Add (ar : arr) (ar : arr) t
         , IsMonOp Negate c (ar : arr) t
         , P.AdditiveInvertible t
         , m ~ m'
         , m ~ m''
         ) =>
         AdditiveGroupBasis m c (ar : arr) (ComputationT c t m' (D c (ar : arr) t)) (ComputationT c t m'' (D c (ar : arr) t)) t where
  (.-.) a cb = do
    ca <- a
    b <- cb
    nb <- monOp Negate b
    binOp Add ca nb

-- sum ::
--      ( P.Foldable f
--      )
--   => f (D c (ar : arr) t)
--   -> (ComputationT c t m (D c (ar : arr) t))
-- sum = P.foldr (.+.) zrs
--   where
--     zrs :: forall s r a. (DArray s r a) => D s r a
--     zrs = let (p :: P.Proxy r) = (P.Proxy :: P.Proxy r)
--       in case Dim.sameDim (Dim.dim @r) (Dim.dim @('[] :: [Dim.Nat])) of
--        P.Just Dim.Evidence -> P.zero :: D s r a
--        P.Nothing -> (fromList $ repeat P.zero) :: D s r a


