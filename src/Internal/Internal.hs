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
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}

{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Internal.Internal (module Internal.Internal) where
import           Control.Monad.State.Strict (State, evalState, get, gets,
                                             modify, put, runState, (>=>))
import qualified Data.Dependent.Map         as DM (DMap, empty, insert, lookup,
                                                   update, updateLookupWithKey)
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import           Prelude                    hiding (abs, negate, signum, (*),
                                             (+), (-), (/))
import qualified Protolude                  as P


import           Data.Dependent.Sum
import           Data.Functor.Identity
import           Data.GADT.Compare
import           Data.GADT.Compare.TH
import           Data.GADT.Show
import           Data.GADT.Show.TH


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
  show (D a)            = "D " ++ show a
  show (Dm a)           = "D " ++ show (a)
  show (DF p t ti)      = "DF " ++ show p ++ show t ++ show ti
  show (DR p dt ti uid) = "DR " ++ show p ++ show dt ++ show ti ++ show uid

type Primal r a = D r a
type Tangent r a = D r a

type FptNode r a = (D r a, D r a, D r a, D r a) -- nodes needed for a fixpoint evaluation

-- FIXME: singleton types on the DualTrace / Arity combination would restrict at least resetEl to a single possible implementation.
class Trace op r a where
  resetEl :: DualTrace op r a -> Computation r a [D r a]
  resetEl (U _ a)     = pure [a]
  resetEl (B _ a b)   = pure [a, b, a, b]
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
class FfMon op a where
  ff :: op -> a -> a

class MonOp op r a where
  rff :: op -> r a -> r a
  fd :: (Computation r a ~ m) => op -> D r a -> m (D r a)
  df :: (Computation r a ~ m) => op -> D r a -> D r a -> D r a -> m (D r a)

monOp ::
     (MonOp op r a, FfMon op a, (Trace op r a), Show op)
  => op
  -> D r a
  -> Computation r a (D r a)
monOp op a =
  case a of
    D ap -> return . D $ ff op ap
    Dm ap -> return . Dm $ rff op ap
    DF ap at ai -> do
      cp <- fd op ap
      cdf <- df op cp ap at
      return $ DF cp cdf ai
    DR ap _ ai _ -> do
      cp <- fd op ap
      r cp (U op a) ai

class DfDaBin op r b c | b -> c where
  df_da ::
       (Computation r c ~ m) => op -> b -> D r c -> D r c -> D r c -> m (D r c)

class DfDbBin op r a c | a -> c where
  df_db ::
       (Computation r c ~ m) => op -> a -> D r c -> D r c -> D r c -> m (D r c)

class FfBin op a r where
  rff_bin :: op -> r a -> r a -> r a -- Forward mode function for arrays
  r_ff_bin :: op -> r a -> a -> r a -- For scalar x arrays
  _ff_bin :: op -> a -> r a -> r a -- For scalar x arrays

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

class (Num a, Show op) =>
      FFBin op a where
  ff_bin :: op -> a -> a -> a
  binOp ::
       ( Num a
       , Trace op r a
       , Computation r a ~ m
       , Show op
       , Trace op r a
       , BinOp op r (D r a) (D r a) a
       , DfDaBin op r (D r a) a
       , DfDbBin op r (D r a) a
       , FfBin op a r
       )
    => op
    -> (D r a)
    -> (D r a)
    -> m (D r a)
  binOp op a b = do
    case a of
      D ap ->
        case b of
          D bp -> return . D $ ff_bin op ap bp
          Dm bp -> return . Dm $ _ff_bin op ap bp
          DF bp bt bi -> do
            cp <- fd_bin op a bp
            cdf <- df_db op a cp bp bt
            return $ DF cp cdf bi
          DR bp _ bi _ -> do
            cfd <- fd_bin op a bp
            r (cfd) (B op a b) bi
      Dm ap ->
        case b of
          D bp -> return . Dm $ r_ff_bin op ap bp
          Dm bp -> return . Dm $ rff_bin op ap bp
          DF bp bt bi -> do
            cp <- fd_bin op a bp
            cdf <- df_db op a cp bp bt
            return $ DF cp cdf bi
          DR bp _ bi _ -> do
            cfd <- fd_bin op a bp
            r (cfd) (B op a b) bi
      DF ap at ai ->
        case b of
          D _ -> do
            cp <- fd_bin op ap b
            cdf <- df_da op b cp ap at
            return $ DF cp (cdf) ai
          Dm _ -> do
            cp <- fd_bin op ap b
            cdf <- df_da op b cp ap at
            return $ DF cp (cdf) ai
          DF bp bt bi ->
            case compare ai bi of
              EQ -> do
                cp <- fd_bin op ap bp
                cdf <- df_dab op a b cp ap at bp bt
                return $ DF cp (cdf) ai
              LT -> do
                cp <- fd_bin op a bp
                cdf <- df_db op a cp bp bt
                return $ DF cp (cdf) bi
              GT -> do
                cp <- fd_bin op ap b
                cdf <- df_da op b cp ap at
                return $ DF cp (cdf) ai
          DR bp _ bi _ ->
            case compare ai bi of
              LT -> do
                fdb <- fd_bin op a bp
                r (fdb) (B op a b) bi
              GT -> do
                cp <- fd_bin op ap b
                cdf <- df_da op b cp ap at
                return $ DF cp (cdf) ai
              EQ ->
                error "Forward and reverse AD r cannot run on the same level."
      DR ap _ ai _ ->
        case b of
          D _ -> do
            fda <- fd_bin op ap b
            r (fda) (B op a b) ai
          Dm _ -> do
            fda <- fd_bin op ap b
            r (fda) (B op a b) ai
          DF bp bt bi ->
            case compare ai bi of
              EQ -> error "Forward and reverse AD cannot run on the same level."
              LT -> do
                cp <- fd_bin op a bp
                cdf <- df_db op a cp bp bt
                return $ DF cp (cdf) bi
              GT -> do
                fdb <- fd_bin op ap b
                r (fdb) (B op a b) ai
          DR bp _ bi _ ->
            case compare ai bi of
              EQ -> do
                fdap <- fd_bin op ap bp
                r (fdap) (B op a b) ai
              LT -> do
                fdab <- fd_bin op a bp
                r (fdab) (B op a b) bi
              GT -> do
                fdab <- fd_bin op ap b
                r (fdab) (B op a b) ai
