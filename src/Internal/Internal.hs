{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE OverloadedLists        #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Internal.Internal (module Internal.Internal) where
import           Control.Monad.State.Strict (State, StateT, evalState, get,
                                             gets, modify, put, runState, (>=>))
import qualified Data.Dependent.Map         as DM (DMap, GOrdering (..), empty,
                                                   insert, lookup, update,
                                                   updateLookupWithKey)
import           Data.GADT.Compare          ((:~:) (..), GCompare (..),
                                             GEq (..))
import qualified Data.HKey                  as HM
import qualified Data.HMap                  as HM
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Data.Type.Equality         (testEquality)
import           Data.Unique
import           GHC.Err
import           GHC.Show
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import qualified NumHask.Array              as A
import           NumHask.Prelude            hiding (Show, State, StateT,
                                             TypeRep, abs, negate, show, signum,
                                             (*), (+), (-), (/))
import qualified NumHask.Prelude            as E
import qualified NumHask.Prelude            as P
import           Protolude.Error
import           Type.Reflection            (SomeTypeRep (..), TypeRep)
-- import           Data.Dependent.Sum
-- import           Data.Functor.Identity
-- import           Data.GADT.Compare
-- import           Data.GADT.Compare.TH
-- import           Data.GADT.Show
-- import           Data.GADT.Show.TH


type family Container c where
  Container (A.Array c s) = c



data ComputationState s a = ComputationState
  {
   _nextTag    :: !Tag
  , _nextUID   :: !UID
  , _uidKeyMap :: UIDKeyMap s a
  , _adjoints  :: Adjoints
  , _fanouts   :: Fanouts s a
  , _fpEps     :: a
  , _maxFpIter :: Int
  }

type Computation s a =  HM.KeyT s (State (ComputationState s a))

type family GetScope a where
  GetScope (D s r t) = s
  GetScope (Computation s t a) = s

data D s (r :: * -> *) a where
  D :: a -> D s r a -- scalar
  Dm :: r a -> D s r a -- array
  DF :: Primal s r a -> Tangent s r a -> Tag  -> D s r a
  DR :: (Show op, Trace op s r a) => D s r a -> DualTrace op s r a -> Tag -> UID -> D s r a

instance (Show a, Show (r a), Show UID) => Show (D s r a) where
  show (D a)            = "D " ++ GHC.Show.show a
  show (Dm a)           = "D " ++  GHC.Show.show (a)
  show (DF p t ti)      = "DF " ++  GHC.Show.show p ++ GHC.Show.show t ++ (" Tag  ")
  show (DR p dt ti uid) = "DR " ++  GHC.Show.show p ++  GHC.Show.show dt ++  (" Tag  ")  ++  GHC.Show.show uid

type Primal s r a = D s r a
type Tangent s r a = D s r a

type FptNode s r a = (D s r a, D s r a, D s r a, D s r a) -- nodes needed for a fixpoint evaluation

-- FIXME: singleton types on the DualTrace / Arity combination would restrict at least resetAlg to a single possible implementation.
class Trace op s r a where
  resetAlg :: DualTrace op s r a -> Computation s a [D s r a]
  resetAlg (U _ a)     = pure [a]
  resetAlg (B _ a b)   = pure [a, b, a, b]
  resetAlg (IxU _ a _) = pure [a]
  pushAlg :: DualTrace op s r a -> D s r a -> Computation s a [(D s r a, D s r a)]
  {-# MINIMAL (resetAlg, pushAlg) #-}

data Noop = Noop deriving Show

-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace op s r a where
  N :: op -> DualTrace op s r a
  U ::  op -> D s r a -> DualTrace op s r a
  B :: op -> D s r a -> D s r a -> DualTrace op s r a
  IxU :: op -> D s r a -> [Int]  -> DualTrace op s r a
  FxP :: op -> FptNode s r a -> DualTrace op s r a

instance (Show op, Show (r a), Show a) => Show (DualTrace op s r a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d

type family Fst (ab :: (k1, k2)) :: k1 where
  Fst '(a, b) = a

type family Snd (ab :: (k1, k2)) :: k2 where
  Snd '(a, b) = b

newtype Uncurry f ab =
  Uncurry (f (Fst ab) (Snd ab))


instance GEq TypeRep where
  geq = testEquality

instance GCompare TypeRep where
  gcompare t1 t2 =
    case testEquality t1 t2 of
      Just Refl -> DM.GEQ
      Nothing ->
        case compare (SomeTypeRep t1) (SomeTypeRep t2) of
          LT -> DM.GLT
          GT -> DM.GGT
          EQ ->
            GHC.Err.error
              "impossible: 'testEquality' and 'compare' \
                         \are inconsistent for TypeRep; report this \
                         \as a GHC bug"

newtype Packed s a r =
  Packed (D s r a)

type family Unpacked a where
  Unpacked (Packed (D s r a)) = D s r a

type Fanouts s a = M.Map UID TypeRep

type Adjoints  s a = M.Map UID (DM.DMap TypeRep (Packed s a))

newtype Tag  = Tag Int deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)

makeLenses ''ComputationState

cGet :: Computation s a (ComputationState s a)
cGet = lift get
cPut :: (ComputationState s a) -> Computation s a ()
cPut = lift . put

getNextTagKey :: Computation s a (Tag)
getNextTagKey = do
  st <- cGet
  let tg@(Tag i) = st ^. nextTag
  -- nk <- HM.getKey
  cPut
    (st & nextTag .~ ((Tag $ i P.+ 1))
     -- & uidKeyMap .~
     -- (M.insert tg (SomeKey nk) (st ^. uidKeyMap))
    )
  return tg

getNextUID :: Computation s a (UID)
getNextUID = do
  st <- cGet
  let tg@(UID t) = st ^. nextUID
  nk <- HM.getKey
  cPut
    (st & nextUID .~ (UID (t P.+ 1)) & uidKeyMap .~
     (M.insert tg (SomeKey nk) (st ^. uidKeyMap)))
  return tg


-- Make a reverse node
r :: (Trace op s r a, Show op)
  => D s r a
  -> DualTrace op s r a
  -> Tag
  -> Computation s a (D s r a)
r d op ai = do
  uid <- getNextUID
  return $ DR d op ai uid

-- Get Primal
p :: D s r a -> D s r a
p =
  \case
    D v -> D v
    Dm v -> Dm v
    DF d _ _ -> d
    DR d _ _ _ -> d

-- Get deepest primal
pD :: D s r a -> D s r a
pD =
  \case
    D v -> D v
    Dm v -> Dm v
    DF d _ _ -> pD d
    DR d _ _ _ -> pD d

instance (Eq a) => Eq (D s r a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D s r a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

-- toNumeric :: D s r a -> b

-- toNumeric d =
--   case pD d of
--     D v -> v
--     Dm v -> v
class FfMon op a where
  ff :: op -> a -> a

class RffMon op r a where
  rff :: op -> r a -> r a

class MonOp op s r a where

  fd :: (Computation s a ~ m) => op -> D s r a -> m (D s r a)
  df ::
       (Computation s a ~ m)
    => op
    -> D s r a
    -> D s r a
    -> D s r a
    -> m (D s r a)
-- {-#INLINE monOp #-}
monOp ::
     (MonOp op s r a, FfMon op a, (Trace op s r a), Show op, RffMon op r a)
  => op
  -> D s r a
  -> Computation s a (D s r a)
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

class DfDaBin op s r b c | b -> c where
  df_da ::
       (Computation s a ~ m)
    => op
    -> b
    -> D s r c
    -> D s r c
    -> D s r c
    -> m (D s r c)

class DfDbBin op s r a c | a -> c where
  df_db ::
       (Computation s c ~ m)
    => op
    -> a
    -> D s r c
    -> D s r c
    -> D s r c
    -> m (D s r c)

class (Show op, E.AdditiveBasis r a, E.AdditiveModule r a) =>
      FfBin op a r where
  rff_bin :: op -> r a -> r a -> r a -- Forward mode function for arrays
  rff_bin op _ _ =
    GHC.Err.error $
    "array x array operation is not defined for " ++ (GHC.Show.show op)
  r_ff_bin :: op -> r a -> a -> r a -- For scalar x arrays
  r_ff_bin op _ _ =
    GHC.Err.error $
    "array x scalar operation is not defined for " ++ (GHC.Show.show op)
  _ff_bin :: op -> a -> r a -> r a -- For scalar x arrays
  _ff_bin op _ _ =
    GHC.Err.error $
    "scalar x array operation is not defined for " ++ (GHC.Show.show op)


class DfBin op s r a b c | a b -> c where
  type BinOpShape a
  fd_bin :: (Computation s c ~ m) => op -> a -> b -> m (D s r c)
  df_dab ::
       (Computation s c ~ m)
    => op
    -> a
    -> b
    -> (D s r c)
    -> (D s r c)
    -> (D s r c)
    -> (D s r c)
    -> (D s r c)
    -> m (D s r c)

class (Show op) =>
      BinOp op a where
  ff_bin :: op -> a -> a -> a
  binOp ::
       ( Trace op s r a
       , Computation s a ~ m
       , Show op
       , Trace op s r a
       , DfBin op s r (D s r a) (D s r a) a
       , DfDaBin op s r (D s r a) a
       , DfDbBin op s r (D s r a) a
       , FfBin op a r
       )
    => op
    -> (D s r a)
    -> (D s r a)
    -> m (D s r a)
  -- {-#INLINE binOp #-}
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
                GHC.Err.error
                  "Forward and reverse AD s r cannot run on the same level."
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
              EQ ->
                GHC.Err.error
                  "Forward and reverse AD cannot run on the same level."
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
