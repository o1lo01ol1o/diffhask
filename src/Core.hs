{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Core
    ( module Core
    ) where

import           Control.Monad.State.Strict (State, evalState, get, gets,
                                             modify, put, runState, (>=>))
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import           Prelude                    hiding (abs, signum, (*), (+), (-), negate, (/))
import qualified Prelude                    as P

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts
-- >>> :set -XNoImplicitPrelude
-- >>> let b = D 2 :: (D Float)
-- >>> let a = D 3 :: (D Float)

data Noop = Noop

data Add = Add

data Abs = Abs

data Sign = Sign

data Subtract = Subtract

data Negate = Negate

data Multiply = Multiply

data Divide = Divide

-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace op a where
  N :: op -> DualTrace op a
  U :: op -> D a -> DualTrace op a
  B :: op -> D a -> D a -> DualTrace op a
  IxU :: op -> D a -> [Int]  -> DualTrace op a
  FxP :: op ->  FptNode a -> DualTrace op a

instance (Show op, Show a) => Show (DualTrace op a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d


type FptNode a = (D a, D a, D a, D a) -- nodes needed for a fixpoint evaluation


newtype Tag = Tag Int
  deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)


type Fanouts = M.Map UID Tag

type Adjoints a = M.Map UID (D a)


data ComputationState a = ComputationState
  { _nextTag   :: !Tag
  , _nextUID   :: !UID
  , _adjoints  :: Adjoints a
  , _fanouts   :: Fanouts
  , _fpEps     :: a
  , _maxFpIter :: Int
  }

type Computation a = State (ComputationState a)

data D a where
  D :: (P.Num a) => a -> D a
  DF :: (P.Num a) => Primal a -> Tangent a -> Tag -> D a
  DR :: (P.Num a, Trace op a) => D a -> DualTrace op a -> Tag -> UID -> D a

instance (Show a, Show Tag, Show UID ) => Show (D a) where
  show (D a) = "D " ++ show a
  show (DF p t ti) = "DF " ++ show p ++ show t ++ show ti
  show (DR p dt ti uid) = "DR " ++ show p ++ "-- fixme --" ++ show ti ++ show uid

type Primal a = D a
type Tangent a = D a


-- the accumulated adjoint at a given node in reverse-mode is aliased as a Delta
data Delta a
  = X (D a)
  | XNeg (D a)
  deriving (Show)

-- FIXME: singleton types on the DualTrace / Arity combination would restrict at least resetEl to a single possible implementation.
class Trace op a where
  resetEl :: DualTrace op a -> Computation a [D a]
  pushEl :: DualTrace op a -> D a -> Computation a [(Delta a, D a)]
  {-# MINIMAL (resetEl, pushEl) #-}

makeLenses ''ComputationState

getNextTag :: Computation a (Tag)
getNextTag = do
  st <- get
  let tg@(Tag t) = st ^. nextTag
  put (st & nextTag .~ (Tag (t P.+ 1)))
  return tg

getNextUID :: Computation a (UID)
getNextUID = do
  st <- get
  let tg@(UID t) = st ^. nextUID
  put (st & nextUID .~ (UID (t P.+ 1)))
  return tg


instance (Eq a) => Eq (D a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

--Core operations;  FIXME:   Move these to a real numeric hierarchy when things are working.

class (Show t) => BinCore a b t | a b -> t, a -> t, b -> t where
  (+) :: a -> b -> Computation t (D t)
  (-) :: a -> b -> Computation t (D t)
  (*) :: a -> b -> Computation t (D t)
  (/) :: a -> b -> Computation t (D t)

class (Show t) => MonCore a t | a -> t where
  abs :: a -> Computation t (D t)
  signum :: a -> Computation t (D t)
  negate :: a -> Computation t (D t)

class (Show t, Num t) => UnitalCore t where
  zero :: (D t)
  one :: (D t)

type CoreConstraintsBin a b c
   = ( BinOp Add a b c
     , Num c
     , BinOp Subtract a b c
     , BinOp Multiply a b c
     , DfDaBin Add a c
     , DfDbBin Add b c
     , DfDaBin Subtract a c
     , DfDbBin Subtract b c
     , DfDaBin Multiply a c
     , DfDbBin Multiply b c
     , Trace Add c
     , Trace Subtract c
     , Trace Multiply c
     , Ord c)

type CoreConstraintsMon a = (MonOp Abs a, MonOp Sign a)

instance (CoreConstraintsBin (D Float) (D Float) Float) =>
         BinCore (Computation Float (D Float)) (Computation Float (D Float)) Float where
  (+) a b = do
    aa <- a
    bb <- b
    binOp Add aa bb
  (-) a b = do
    aa <- a
    bb <- b
    binOp Subtract aa bb
  (*) a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb
  (/) a b = do
    aa <- a
    bb <- b
    binOp Divide aa bb

instance ( CoreConstraintsBin (D Float) (D Float) Float
         , CoreConstraintsMon (D Float)
         ) =>
         MonCore (Computation Float (D Float)) Float where
  abs a = do
    aa <- a
    monOp Abs aa
  signum a = do
    aa <- a
    monOp Sign aa
  negate a = do
    aa <- a
    monOp Negate aa

instance (CoreConstraintsBin (D Double) (D Double) Double) =>
         BinCore (Computation Double (D Double)) (Computation Double (D Double)) Double where
  (+) a b = do
    aa <- a
    bb <- b
    binOp Add aa bb
  (-) a b = do
    aa <- a
    bb <- b
    binOp Subtract aa bb
  (*) a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb
  (/) a b = do
    aa <- a
    bb <- b
    binOp Divide aa bb

instance ( CoreConstraintsBin (D Double) (D Double) Double
         , CoreConstraintsMon (D Double)
         ) =>
         MonCore (Computation Double (D Double)) Double where
  abs a = do
    aa <- a
    monOp Abs aa
  signum a = do
    aa <- a
    monOp Sign aa
  negate a = do
    aa <- a
    monOp Negate aa

instance (Show a, Num a, RealFloat a) => UnitalCore a where
  zero = D 0
  one = D 1

instance ( CoreConstraintsBin (D Float) (D Float) Float
         ) =>
         BinCore (D Float) (D Float) Float where
  (+) a b = binOp Add a b
  (-) a b = binOp Subtract a b
  (*) a b = binOp Multiply a b
  (/) a b = binOp Divide a b

instance (
         CoreConstraintsBin (D Float) (D Float) Float
         ) =>
         MonCore (D Float) Float where
  abs a = monOp Abs a
  signum a = monOp Sign a
  negate a = monOp Negate a


instance (CoreConstraintsBin (D Double)  (D Double) Double
         ) => BinCore (D Double)  (D Double) Double where
  (+) a b = binOp Add a b
  (-) a b = binOp Subtract a b
  (*) a b = binOp Multiply a b
  (/) a b = binOp Divide a b

instance (
          CoreConstraintsBin (D Double) (D Double) Double
         ) => MonCore (D Double) Double where
  abs a = monOp Abs a
  signum a = monOp Sign a
  negate = monOp Negate


instance (CoreConstraintsBin (D Float) (D Float) Float) => BinCore  (Computation Float (D Float))  (D Float) Float where

  (+) a b = do
    aa <- a
    binOp Add aa b
  (-) a b = do
    aa <- a
    binOp Subtract aa b
  (*) a b = do
    aa <- a
    binOp Multiply aa b
  (/) a b = do
    aa <- a
    binOp Divide aa b


instance (CoreConstraintsBin (D Double) (D Double) Double) => BinCore (Computation Double (D Double))  (D Double) Double where
  (+) a b = do
    aa <- a
    binOp Add aa b
  (-) a b = do
    aa <- a
    binOp Subtract aa b
  (*) a b = do
    aa <- a
    binOp Multiply aa b
  (/) a b = do
    aa <- a
    binOp Divide aa b

instance (CoreConstraintsBin (D Float) (D Float) Float) => BinCore (D Float)  (Computation Float (D Float))  Float where
  (+) a b = do
    bb <- b
    binOp Add a bb
  (-) a b = do
    bb <- b
    binOp Subtract a bb
  (*) a b = do
    bb <- b
    binOp Multiply a bb
  (/) a b = do
    bb <- b
    binOp Divide a bb

instance (CoreConstraintsBin (D Double) (D Double) Double) => BinCore  (D Double) (Computation Double (D Double)) Double where
  (+) a b = do
    bb <- b
    binOp Add a bb
  (-) a b = do
    bb <- b
    binOp Subtract a bb
  (*) a b = do
    bb <- b
    binOp Multiply a bb
  (/) a b = do
    bb <- b
    binOp Divide a bb

initCompFloat :: (RealFloat a)=> ComputationState a
initCompFloat = ComputationState (Tag 0) (UID 0) M.empty M.empty 1.0e-6 1000


-- Make a reverse node
r :: (P.Num a, Trace op a) => D a -> DualTrace op a -> Tag  -> Computation a (D a)
r d op ai = do
  uid <- getNextUID
  return $ DR d op ai uid

-- Get Primal
p :: D a -> D a
p =
  \case
    D v -> D v
    DF d _ _ -> d
    DR d _ _ _ -> d

-- Get deepest primal
pD :: D a -> D a
pD =
  \case
    D v -> D v
    DF d _ _ -> pD d
    DR d _ _ _ -> pD d

toNumeric :: D a -> a

toNumeric d =
  let (D n) = pD d
  in n

-- Get Tangent
t :: (RealFloat a, Show a) => D a -> Computation a (Tangent a)
t =
  \case
    D _ -> pure zero
    DF _ at _ -> pure at
    DR {} -> error "Can't get tangent of a reverse node"

mkForward :: (P.Num a) => Tag -> Tangent a -> Primal a  -> D a
mkForward i tg d  = DF d tg i


mkReverse :: (P.Num a, Trace Noop a) => Tag -> D a -> Computation a (D a)
mkReverse i d = r d (N Noop) i

class MonOp op a where
  ff ::( Computation a ~ m) => op -> a -> a
  fd :: ( Computation a ~ m) =>  op -> D a -> m (D a)
  df :: ( Computation a ~ m) =>  op -> D a -> D a -> D a ->m( D a)

monOp' :: (Trace op a, Computation a ~ m) =>
     op
  -> D a
  -> (a -> a)
  -> (D a -> m (D a))
  -> (D a -> D a -> D a -> m (D a))
  -> (D a -> DualTrace op a)
  -> Computation a (D a)
monOp' _ a ff fd df r_ =
  case a of
    D ap -> return . D $ ff ap
    DF ap at ai -> do
      cp <- fd ap
      cdf <- df cp ap at
      return $ DF cp cdf ai
    DR ap _ ai _ ->do
      cp <- fd ap
      r cp (r_ a) ai

monOp :: (MonOp op a, (Trace op a)) => op -> D a -> Computation a (D a)
monOp op a =
  let r_d =   U op
  in monOp' op a (ff op) (fd op) (df op) r_d


binOp' ::
     (Num a, Trace op a, Computation a ~ m)
  => op
  -> (D a)
  -> (D a)
  -> (a -> a -> a)
  -> (D a -> D a -> m (D a))
  -> (D a -> D a -> D a -> m (D a))
  -> (D a -> D a -> D a -> m (D a))
  -> (D a -> D a -> D a -> D a -> D a -> m (D a))
  -> (D a -> D a -> DualTrace op a)
  -> (D a -> D a -> DualTrace op a)
  -> (D a -> D a -> DualTrace op a)
  -> m (D a)
binOp' _ a b ff_fn fd df_da df_db df_dab r_d_d r_d_c r_c_d = do
  case a of
    D ap ->
      case b of
        D bp -> return . D $ ff_fn ap bp
        DF bp bt bi -> do
          cp <- fd a bp
          cdf <- df_db cp bp bt
          return $ DF cp cdf bi
        DR bp _ bi _ -> do
          cfd <- fd a bp
          r (cfd) (r_c_d a b) bi
    DF ap at ai ->
      case b of
        D _ -> do
          cp <- fd ap b
          cdf <- df_da cp ap at
          return $ DF cp (cdf) ai
        DF bp bt bi ->
          case compare ai bi of
            EQ -> do
              cp <- fd ap bp
              cdf <- df_dab cp ap at bp bt
              return $ DF cp (cdf) ai
            LT -> do
              cp <- fd a bp
              cdf <- df_db cp bp bt
              return $ DF cp (cdf) bi
            GT -> do
              cp <- fd ap b
              cdf <- df_da cp ap at
              return $ DF cp (cdf) ai
        DR bp _ bi _ ->
          case compare ai bi of
            LT -> do
              fdb <- fd a bp
              r (fdb) (r_c_d a b) bi
            GT -> do
              cp <- fd ap b
              cdf <- df_da cp ap at
              return $ DF cp (cdf) ai
            EQ -> error "Forward and reverse AD cannot run on the same level."
    DR ap _ ai _ ->
      case b of
        D _ -> do
          fda <- fd ap b
          r (fda) (r_d_c a b) ai
        DF bp bt bi ->
          case compare ai bi of
            EQ -> error "Forward and reverse AD cannot run on the same level."
            LT -> do
              cp <- fd a bp
              cdf <- df_db cp bp bt
              return $ DF cp (cdf) bi
            GT -> do
              fdb <- fd ap b
              r (fdb) (r_d_c a b) ai
        DR bp _ bi _ ->
          case compare ai bi of
            EQ -> do
              fdap <- fd ap bp
              r (fdap) (r_d_d a b) ai
            LT -> do
              fdab <- fd a bp
              r (fdab) (r_c_d a b) bi
            GT -> do
              fdab <- fd ap b
              r (fdab) (r_d_c a b) ai



class (Num c) => FFBin op c where
  ff_bin :: op -> c -> c -> c
  binOp :: (Trace op c, BinOp op (D c) (D c) c, DfDaBin op (D c) c, DfDbBin op (D c) c) => op -> D c -> D c -> Computation c (D c)
  binOp op a b =
    let traceOp = B op
        r_d_d = traceOp
        r_d_c = traceOp
        r_c_d = traceOp
    in binOp'
         op
         a
         b
         (ff_bin op )
         (fd_bin op)
         (df_da op b)
         (df_db op a)
         (df_dab op a b)
         r_d_d
         r_d_c
         r_c_d

class DfDaBin op b c | b -> c where
  df_da :: (Computation c ~ m) => op -> b -> D c -> D c -> D c -> m (D c)

class DfDbBin op a c | a -> c where
  df_db :: (Computation c ~ m) => op -> a -> D c -> D c -> D c -> m (D c)


class BinOp op a b c | a b -> c where
  fd_bin :: (Computation c ~ m) => op -> a -> b -> m (D c)
  df_dab ::
       (Computation c ~ m)
    => op
    -> a
    -> b
    -> (D c)
    -> (D c)
    -> (D c)
    -> (D c)
    -> (D c)
    -> m (D c)



instance Trace Noop a where
  pushEl _ _ = pure []
  resetEl _ = pure []

-- | Addition
-- >>> compute $ diff' (\x -> x + a) a
-- (D 6.0,D 1.0)
instance (P.Num a) => FFBin Add a where
    {-# INLINE ff_bin #-}
    ff_bin  _ a b = b P.+ a

instance DfDaBin Add (D a) a where
    {-# INLINE df_da #-}
    df_da  _ _ _ _ at = pure at

instance  DfDbBin Add (D a) a where
    {-# INLINE df_db #-}
    df_db _ _ _ _ bt = pure bt

instance (Num a) =>
         BinOp Add (D a) (D a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Add a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Add at bt

instance Trace Add a where
  pushEl (B _ a b) dA =
    pure [(X dA, a), (X dA, b), (X dA, a), (X dA, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

-- | Subtraction
-- >>> compute $ diff' (\x -> x - a) a
-- (D 0.0,D 1.0)
instance (P.Num a) => FFBin Subtract a where
    {-# INLINE ff_bin #-}
    ff_bin  _ a b = a P.- b


instance  DfDaBin Subtract (D a) a where
    {-# INLINE df_da #-}
    df_da _  _ _ _ at = pure at

instance (Num a, MonCore (D a) a) => DfDbBin Subtract (D a) a where
    {-# INLINE df_db #-}
    df_db _  _ _ _ bt = monOp Negate bt

instance (Num a, MonCore (D a) a) => BinOp Subtract (D a) (D a) a where

  {-# INLINE fd_bin #-}
  fd_bin _ a b =  binOp Subtract a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Subtract at bt

instance Trace Subtract a where
  pushEl (B _ a b) dA =
    pure [(X dA, a), (XNeg dA, b), (X dA, a ), (XNeg dA,b )]
  resetEl (B _ a b) = pure [a, b, a, b]

instance (P.Num a, RealFloat a, Show a) => MonOp Sign a where
  {-# INLINE ff #-}
  ff _ a = P.signum a
  {-# INLINE fd #-}
  fd _ a = monOp Sign a
  {-# INLINE df #-}
  df _ _ _ _ = pure zero


instance (RealFloat a, Show a) => Trace Sign a where
  pushEl (U _ a) dA = do
    pure [(X zero, a)]
  resetEl (U _ a ) = pure [a]



-- | Abs
--  compute $ diff' abs a
-- (D 3.0, D 1.0)
instance ( P.Num a
         , RealFloat a
         , BinCore (D a) (D a) a
         , BinCore (Computation a (D a)) (Computation a (D a)) a
         ) =>
         MonOp Abs a where
  {-# INLINE ff #-}
  ff _ a = P.abs a
  {-# INLINE fd #-}
  fd _ a =
    if a >= D 0
      then pure a
      else monOp Negate a
  {-# INLINE df #-}
  df _ _ ap at = do
    sap <- monOp Sign ap
    binOp Multiply at sap

instance ( P.Num a, MonCore (D a) a, BinCore (D a) (D a) a) => Trace Abs a where
  pushEl (U _ a) dA = do
    cdA <- pure dA
    sp <-  signum (p a)
    dl <- cdA * sp
    pure [(X dl, a)]
  resetEl (U _ a ) = pure [a]

instance ( P.Num a) => MonOp Negate a where
  {-# INLINE ff #-}
  ff _ a = P.negate a
  {-# INLINE fd #-}
  fd _ a = monOp Negate a
  {-# INLINE df #-}
  df _ _ _ at = monOp Negate at

instance ( P.Num a) => Trace Negate a where
  pushEl (U _ a) dA = do
    pure [(XNeg dA, a)]
  resetEl (U _ a ) = pure [a]

-- | Multiplication
-- >>> compute $ diff' (\x -> x * a) a
-- (D 9.0,D 3.0)
instance (P.Num a) => FFBin Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.* a


type WhatICanWorkWith a
   = ( BinCore (Computation a (D a)) (Computation a (D a)) a
     , BinCore (D a) (D a) a
     , BinCore (Computation a (D a)) (D a) a
     , BinCore (D a) (Computation a (D a)) a
     , MonCore (D a) a
     , MonCore (Computation a (D a)) a
     , RealFloat a
     , (P.Num a))
     
instance (BinCore (D a) (D a) a) => DfDaBin Multiply (D a) a where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = at * b

instance (BinCore (D a) (D a) a) => DfDbBin Multiply (D a) a where
  {-# INLINE df_db #-}
  df_db _ a _ _ bt =  bt * a



instance ( BinCore (Computation a (D a)) (Computation a (D a)) a
         , BinCore (D a) (D a) a
         ) =>
         BinOp Multiply (D a) (D a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = a * b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ ap at bp bt = (at * bp) + (ap * bt)


instance (BinCore (D a) (D a) a) => Trace Multiply a where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA * p b
    opb <- cdA * p a
    arga <- cdA * b
    argb <- cdA * a
    pure [(X opa, a), (X opb, b), (X arga, a), (X argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]


-- | Division
-- >>> compute $ diff' (\x -> x / a) a
-- (D 1.0,D 3.0)

-- | Division
-- >>> compute $ grad' (\x -> x / a) a
-- (D 1.0,D 1.0)

instance (P.Num a, P.RealFloat a) => FFBin Divide a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b = b P./ a

     
instance ( MonCore (D a) a
         , BinCore (D a) (Computation a (D a)) a
         , BinCore (D a) (D a) a
         , BinCore (Computation a (D a)) (D a) a
         , RealFloat a
         , BinCore (Computation a (D a)) (Computation a (D a)) a
         ) =>
         DfDaBin Divide (D a) a where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = binOp Divide at b

instance ( MonCore (D a) a
          , BinCore (D a) (Computation a (D a)) a
         , BinCore (D a) (D a) a
         , BinCore (Computation a (D a)) (D a) a
         , BinCore (Computation a (D a)) (Computation a (D a)) a
         , RealFloat a
         ) =>
         DfDbBin Divide (D a) a where
  {-# INLINE df_db #-}
  df_db _ a cp bp bt = do
    cbt <- (monOp Negate bt)
    ccpbp <- (binOp Divide cp bp)
    binOp Divide cbt ccpbp


--fixme probably need groups of constraints for each group of numerics for all combos of type classes:  Additives
instance ( BinCore (Computation a (D a)) (Computation a (D a)) a
         , BinCore (D a) (Computation a (D a)) a
         , BinCore (D a) (D a) a
         , BinCore (Computation a (D a)) (D a) a
         , RealFloat a
         , MonCore (D a) a
         ) =>
         BinOp Divide (D a) (D a) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = binOp Divide a b
  {-# INLINE df_dab #-}
  df_dab _ _ _ cp ap at bp bt = do
    catbt <- binOp Subtract at bt
    ccp <- binOp Multiply catbt cp
    binOp Divide (ccp) bp 


instance ( MonCore (D a) a
         , BinCore (D a) (Computation a (D a)) a
         , BinCore (D a) (D a) a
         , BinCore (Computation a (D a)) (D a) a
         ) =>
         Trace Divide a where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA / p b
    opb <- cdA * (((negate (p a)) / p b) * p b)
    arga <- cdA * b
    argb <- cdA * a
    pure [(X opa, a), (X opb, b), (X arga, a), (X argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

  
eval :: (MonCore (D a) a) => Delta a -> Computation a (D a)
eval dl =
  case dl of
    X v    -> pure v
    XNeg v -> negate v

applyDelta ::
     (MonCore (D a) a, BinCore (D a) (D a) a)
  => UID
  -> Delta a
  -> Adjoints a
  -> (Maybe (Computation a (D a)))
applyDelta tag dlta adjs=
  case M.lookup tag adjs of
    Just v -> Just $ do
      e <- eval dlta
      r <- v + e
      modify (\st -> st & adjoints .~ M.update (const . Just $ r) tag adjs)
      return r
    Nothing -> Nothing

decrementFanout :: UID -> Fanouts -> (Maybe Tag, Fanouts)
decrementFanout =
  M.updateLookupWithKey (\_ (Tag v) -> Just . Tag $ v P.- 1)

incrementFanout :: UID -> Computation a Tag
incrementFanout u = do
  st <- get
  let (mf, a) =
        M.updateLookupWithKey (\_ (Tag f) -> Just . Tag $ f P.+ 1) u (st ^. fanouts)

  (case mf of
      Nothing -> do
        put (st & fanouts %~ M.insert u (Tag 1))
        return $ Tag 1
      Just f -> do
        put (st & fanouts %~ const a)
        return f)


reset :: (RealFloat a, Show a) => [D a] -> Computation a ()
reset l =
  case l of
    [] -> return ()
    (da:xs) ->
      case da of
        DR _ o _ uniq -> do
          fanout <- incrementFanout uniq
          if fanout == Tag 1 then
            do
              modify (\st -> st & adjoints %~ M.insert uniq zero)
              x <- resetEl o
              reset $ x `mappend` xs -- verify this
            else reset xs
          reset xs
        _ -> reset xs

-- recursively pushes nodes onto the reverse mode stack and evaluates partials
push :: (MonCore (D a) a, BinCore (D a) (D a) a) => [(Delta a, D a)] -> Computation a ()
push l =
  case l of
    [] -> return ()
    ((dl, da):xs) ->
      case da of
        DR _ o _ uniq -> do
          st <- gets ( ^. adjoints )
          let mv = applyDelta uniq dl st
          case mv of
            Just cdA -> do
              dA <- cdA
              nst1 <- get
              let (Just fn, aa) = decrementFanout uniq (nst1 ^. fanouts)
              put (nst1 & fanouts .~ aa)
              if fn == Tag 0 then
                do
                  pd <- pushEl o dA
                  push $ pd `mappend` xs
                else push xs
            Nothing -> error "key not found in adjoints!"
        _ -> push xs

reverseReset ::( RealFloat a, Show a) => D a -> Computation a ()
reverseReset d = do
  modify (& fanouts .~ M.empty )
  reset [d]

reverseProp :: ( RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a) => D a -> D a -> Computation a ()
reverseProp  v d = do
  reverseReset  d
  push [(X v, d)]

{-# INLINE primalTanget #-}
primalTanget :: (RealFloat a, Show a) => D a -> Computation a (D a, Tangent a)
primalTanget d = do
  ct <- t d
  pure (p d, ct)

adjoint :: (RealFloat a, Show a) =>  D a -> Computation a (D a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a  -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> pure zero

runComputation :: (RealFloat a) => State s a -> s -> (a, s)
runComputation = runState

compute :: (RealFloat a) => Computation a (b) -> b
compute f = evalState f initCompFloat

{-# INLINE computeAdjoints' #-}
computeAdjoints' :: (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a) => D a -> Computation a ()
computeAdjoints' d = do
  modify (\st -> st & adjoints .~ M.empty)
  o <- pure one
  reverseProp o d

{-# INLINE computeAdjoints #-}
computeAdjoints :: (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a) => D a -> Computation a (Adjoints a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' ::
     (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a)
  => (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, Tangent a)
diff' f x = do
  n <- getNextTag
  o <- pure one
  fout <- f $ mkForward n o x
  primalTanget fout
{-# INLINE diff #-}

diff ::
     (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a)
  => (D a -> Computation a (D a))
  -> D a
  -> Computation a (Tangent a)
diff f x =
  snd <$> diff' f x

{-# INLINE diffn #-}
diffn ::
     (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a)
  => Int
  -> (D a -> Computation a (D a))
  -> D a
  -> Computation a (Tangent a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go ::
         (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a)
      => Int
      -> (D a -> Computation a (D a))
      -> D a
      -> Computation a (Tangent a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn' ::
     (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a)
  => Int
  -> (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, (Tangent a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  return (it, again)
  
-- | Reverse Multiplication
-- >>> compute $ grad' (\x -> x * a) a
-- (D 9.0,D 1.0)
{-# INLINE grad' #-}
grad' ::
     (Trace Noop a, RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a)
  => (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, (D a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  z <- f xa
  computeAdjoints' z
  adj <- adjoint z
  return (p z, adj)

{-# INLINE grad #-}
grad ::
     (Trace Noop a, RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a) =>
   (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: (RealFloat a, Show a, MonCore (D a) a, BinCore (D a) (D a) a) =>
     (D a -> Computation a (D a)) -> Tangent a -> Primal a -> Computation a (D a, Tangent a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  primalTanget fout

jacobian ::
     (Show a, RealFloat a, MonCore (D a) a, BinCore (D a) (D a) a)
  => (D a -> Computation a (D a))
  -> Tangent a
  -> Primal a
  -> Computation a (Tangent a)
jacobian f x v = snd <$> jacobian' f x v
