{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE RankNTypes           #-}

{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilyDependencies   #-}

module Internal.Internal (module Internal.Internal) where
import           Control.Monad.State.Strict (State, evalState, get, gets,
                                             modify, put, runState, (>=>))
import qualified Data.Dependent.Map                   as DM (DMap, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import           Prelude                    hiding (abs, negate, signum, (*),
                                             (+), (-), (/), )
import qualified Protolude                    as P


import Data.Dependent.Sum
import Data.Functor.Identity
import Data.GADT.Show
import Data.GADT.Show.TH
import Data.GADT.Compare
import Data.GADT.Compare.TH


data ComputationState r a = ComputationState
  { _nextTag   :: !Tag
  , _nextUID   :: !UID
  , _adjoints  :: Adjoints r a
  , _fanouts   :: Fanouts
  , _fpEps     :: a
  , _maxFpIter :: Int
  }

type Computation r a = State (ComputationState r a)

data D r a where
  D :: a -> D r a -- scalar
  Dm :: r a -> D r a -- array
  DF :: Primal r a -> Tangent r a -> Tag -> D r a
  DR :: (Show op) => D r a -> DualTrace op r a -> Tag -> UID -> D r a

instance (Show a, Show Tag, Show UID, Show (r a)) => Show (D r a) where
  show (D a) = "D " ++ show a
  show (Dm a) = "D " ++ show (a)
  show (DF p t ti) = "DF " ++ show p ++ show t ++ show ti
  show (DR p dt ti uid) = "DR " ++ show p ++ show dt ++ show ti ++ show uid

type Primal r a = D r a
type Tangent r a = D r a

type FptNode r a = (D r a, D r a, D r a, D r a) -- nodes needed for a fixpoint evaluation

-- FIXME: singleton types on the DualTrace / Arity combination would restrict at least resetEl to a single possible implementation.
class Trace op r a where
  resetEl :: DualTrace op r a -> Computation r a [D r a]
  resetEl (U _ a) = pure [a]
  resetEl (B _ a b) = pure [a, b, a, b]
  resetEl (IxU _ a _) = pure [a]
  pushEl :: DualTrace op r a -> D r a -> Computation r a [(D r a, D r a)]
  {-# MINIMAL (resetEl, pushEl) #-}

data Noop = Noop deriving Show

-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace op r a where
  N :: op -> DualTrace op r a
  U ::  op -> D r a -> DualTrace op r a
  B :: op -> D r a -> D r a -> DualTrace op r a
  IxU :: op -> D r a -> [Int]  -> DualTrace op r a
  FxP :: op -> FptNode r a -> DualTrace op r a

instance (Show op, Show a, Show (r a)) => Show (DualTrace op r a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d

type Fanouts = M.Map UID Tag

type Adjoints r a = M.Map UID (D r a)

newtype Tag = Tag Int
  deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)

makeLenses ''ComputationState

getNextTag :: Computation r a (Tag)
getNextTag = do
  st <- get
  let tg@(Tag t) = st ^. nextTag
  put (st & nextTag .~ (Tag (t P.+ 1)))
  return tg

getNextUID :: Computation r a (UID)
getNextUID = do
  st <- get
  let tg@(UID t) = st ^. nextUID
  put (st & nextUID .~ (UID (t P.+ 1)))
  return tg


-- Make a reverse node
r :: (Trace op r a, Show op)
  => D r a
  -> DualTrace op r a
  -> Tag
  -> Computation r a (D r a)
r d op ai = do
  uid <- getNextUID
  return $ DR d op ai uid

-- Get Primal
p :: D r a -> D r a
p =
  \case
    D v -> D v
    Dm v -> Dm v
    DF d _ _ -> d
    DR d _ _ _ -> d

-- Get deepest primal
pD :: D r a -> D r a
pD =
  \case
    D v -> D v
    Dm v -> Dm v
    DF d _ _ -> pD d
    DR d _ _ _ -> pD d

instance (Eq a) => Eq (D r a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D r a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

-- toNumeric :: D r a -> b

-- toNumeric d =
--   case pD d of
--     D v -> v
--     Dm v -> v


monOp ::
     (MonOp op r a, FfMon op a, (Trace op r a), Show op)
  => op
  -> D r a
  -> Computation r a (D r a)
monOp op a =
  let r_d =   U op
  in monOp' op a (ff op) (rff op) (fd op) (df op) r_d

monOp' ::
     (Trace op r a, Computation r a ~ m, Show op)
  => op
  -> D r a
  -> ( a -> a)
  -> (r a ->r a)
  -> (D r a -> m (D r a))
  -> (D r a -> D r a -> D r a -> m (D r a))
  -> (D r a -> DualTrace op r a)
  -> Computation r a (D r a)
monOp' _ a ff rff fd df r_ =
  case a of
    D ap -> return . D $ ff ap
    Dm ap -> return . Dm $ rff ap
    DF ap at ai -> do
      cp <- fd ap
      cdf <- df cp ap at
      return $ DF cp cdf ai
    DR ap _ ai _ ->do
      cp <- fd ap
      r cp (r_ a) ai

binOp' ::
     (Num a, Trace op r a, Computation r a ~ m, Show op)
  => op
  -> (D r a)
  -> (D r a)
  -> (a -> a ->  a)
  -> (r a ->r a -> r a)
  -> (D r a -> D r a -> m (D r a))
  -> (D r a -> D r a -> D r a -> m (D r a))
  -> (D r a -> D r a -> D r a -> m (D r a))
  -> (D r a -> D r a -> D r a -> D r a -> D r a -> m (D r a))
  -> (D r a -> D r a -> DualTrace op r a)
  -> (D r a -> D r a -> DualTrace op r a)
  -> (D r a -> D r a -> DualTrace op r a)
  -> m (D r a)


binOp' _ a b ff_fn rff_fn fd df_da df_db df_dab r_d_d r_d_c r_c_d = do
  case a of
    D ap ->
      case b of
        D bp -> return . D $ ff_fn ap bp
        Dm bp -> return . Dm $ rff_fn ap bp
        DF bp bt bi -> do
          cp <- fd a bp
          cdf <- df_db cp bp bt
          return $ DF cp cdf bi
        DR bp _ bi _ -> do
          cfd <- fd a bp
          r (cfd) (r_c_d a b) bi
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
    Dm ap ->
      case b of
        Dm bp -> return . Dm $ rff_fn ap bp
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
            EQ -> error "Forward and reverse AD r cannot run on the same level."
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



class (Num c, Show op) =>
      FFBin op c where
  ff_bin :: op -> c -> c -> c
 
  binOp ::
       ( Trace op r c
       , BinOp op r (D r c) (D r c) c
       , DfDaBin op r (D r c) c
       , DfDbBin op r (D r c) c
       )
    => op
    -> D r c
    -> D r c
    -> Computation r c (D r c)
  binOp op a b =
    let traceOp = B op
        r_d_d = traceOp
        r_d_c = traceOp
        r_c_d = traceOp
    in binOp'
         op
         a
         b
         (ff_bin op)
         (rff_bin op)
         (fd_bin op)
         (df_da op b)
         (df_db op a)
         (df_dab op a b)
         r_d_d
         r_d_c
         r_c_d

class FfMon op a where
  ff :: op -> a -> a
  
  
class MonOp op r a where
  rff :: op -> r a -> r a
  fd :: (Computation r a ~ m) => op -> D r a -> m (D r a)
  df :: (Computation r a ~ m) => op -> D r a -> D r a -> D r a -> m (D r a)
  
class DfDaBin op r b c | b -> c where
  df_da ::
       (Computation r c ~ m) => op -> b -> D r c -> D r c -> D r c -> m (D r c)

class DfDbBin op r a c | a -> c where
  df_db ::
       (Computation r c ~ m) => op -> a -> D r c -> D r c -> D r c -> m (D r c)

class FfBin op a r where
  rff_bin :: op -> r a -> r a -> r a
  r_ff_bin :: op -> r a -> a -> r a

class BinOp op r a b c | a b -> c where
  fd_bin :: (Computation r c ~ m) => op -> a -> b -> m (D r c)
  
  df_dab ::
       (Computation r c ~ m)
    => op
    -> a
    -> b
    -> (D r c)
    -> (D r c)
    -> (D r c)
    -> (D r c)
    -> (D r c)
    -> m (D r c)
