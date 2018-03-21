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
-- import qualified Data.Dependent.Map         as DM (DMap, GOrdering (..), empty,
--                                                    insert, lookup, update,
--                                                    updateLookupWithKey)
-- import           Data.GADT.Compare          ((:~:) (..), GCompare (..),
--                                              GEq (..))
--import qualified Data.HKey                  as HM
--import qualified Data.HMap                  as HM
import qualified Numeric.Dimensions as Dim
import qualified Numeric.Dimensions.Dim as Dim
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
-- import           Data.Type.Equality         (testEquality)
-- import           Data.Unique
import           GHC.Err
import           GHC.Show
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import qualified NumHask.Array              as A
import NumHask.Array ()
import           NumHask.Prelude            hiding (Show, State, StateT,
                                             TypeRep, abs, negate, show, signum,
                                             (*), (+), (-), (/))
import qualified NumHask.Prelude            as E
import qualified NumHask.Prelude            as P
import           Protolude.Error
--import           Type.Reflection            (SomeTypeRep (..), TypeRep)
-- import           Data.Dependent.Sum
-- import           Data.Functor.Identity
-- import           Data.GADT.Compare
-- import           Data.GADT.Compare.TH
-- import           Data.GADT.Show
-- import           Data.GADT.Show.TH



data ComputationState c a = ComputationState
  {
   _nextTag    :: !Tag
  , _nextUID   :: !UID
  , _adjoints  :: Adjoints c a
  , _fanouts   :: Fanouts c a
  , _fpEps     :: a
  , _maxFpIter :: Int
  }

type Computation c a  = StateT (ComputationState c a) Identity

type Operable c r a  = (E.Additive a, Dim.Dimensions r, A.Container c)

data D c r a where
  D :: (Show (A.Array c r a), Operable c r a) => A.Array c r a -> D c r a
  --Dm :: (Show (A.Array c s a)) => A.Array c s a -> D c s a
  DF :: Primal c r a -> Tangent c r a -> Tag -> D c r a
  DR
    :: (Show op, Trace c op r a)
    => D c r a
    -> DualTrace c op r a
    -> Tag
    -> UID
    -> D c r a

type family GetContainer a where
  GetContainer (D c _ _) = c
  GetContainer (Computation c a _) = c

type SameContainer a b = (GetContainer a ~ GetContainer b)



instance (Show a, Show UID) => Show (D c r a) where
  show (D a)            = "D " ++ GHC.Show.show a
  -- show (Dm a)           = "D " ++  GHC.Show.show (a)
  show (DF p t ti)      = "DF " ++  GHC.Show.show p ++ GHC.Show.show t ++ (" Tag  ")
  show (DR p dt ti uid) = "DR " ++  GHC.Show.show p ++  GHC.Show.show dt ++  (" Tag  ")  ++  GHC.Show.show uid

type Primal c r a = D c r a
type Tangent c r a = D c r a

type FptNode c r a = (D c r a, D c r a, D c r a, D c r a) -- nodes needed for a fixpoint evaluation

-- FIXME: singleton types on the DualTrace / Arity combination would restrict at least resetAlg to a single possible implementation.
class Trace c op r a where
  resetAlg :: DualTrace c op r a -> Computation c a [D c r a]
  resetAlg (U _ a)     = pure [a]
  resetAlg (B _ a b)   = pure [a, b, a, b]
  resetAlg (IxU _ a _) = pure [a]
  pushAlg :: DualTrace c op r a -> D c r a -> Computation c a [(D c r a, D c r a)]
  {-# MINIMAL (resetAlg, pushAlg) #-}

data Noop = Noop deriving Show

-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace c op r a where
  N :: op -> DualTrace c op r a
  U ::  op -> D c r a -> DualTrace c op r a
  B :: op -> D c r a -> D c r a -> DualTrace c op r a
  IxU :: op -> D c r a -> [Int]  -> DualTrace c op r a
  FxP :: op -> FptNode c r a -> DualTrace c op r a

instance (Show op,  Show a) => Show (DualTrace c op r a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d

data SomeD c a where
  SomeD :: (A.Container c, Dim.Dimensions r) => D c r a -> SomeD c a

type Fanouts c a = M.Map UID (SomeD c a)

type Adjoints c a = M.Map UID (SomeD c a)

newtype Tag  = Tag Int deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)

makeLenses ''ComputationState


getNextTagKey :: Computation c a (Tag)
getNextTagKey = do
  st <- get
  let tg@(Tag i) = st ^. nextTag
  put
    (st & nextTag .~ ((Tag $ i P.+ 1))
    )
  return tg

getNextUID :: Computation c a (UID)
getNextUID = do
  st <- get
  let tg@(UID t) = st ^. nextUID
  put
    (st & nextUID .~ (UID (t P.+ 1)) )
  return tg


-- Make a reverse node
r :: (Trace c op r a, Show op)
  => D c r a
  -> DualTrace c op r a
  -> Tag
  -> Computation c a (D c r a)
r d op ai = do
  uid <- getNextUID
  return $ DR d op ai uid

-- Get Primal
p :: D c r a -> D c r a
p =
  \case
    D v -> D v
    -- Dm v -> Dm v
    DF d _ _ -> d
    DR d _ _ _ -> d

-- Get deepest primal
pD :: D c r a -> D c r a
pD =
  \case
    D v -> D v
    --  Dm v -> Dm v
    DF d _ _ -> pD d
    DR d _ _ _ -> pD d

instance (Eq a) => Eq (D c r a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D c r a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

toNumeric :: D c r a -> A.Array c r a

toNumeric d =
  case pD d of
    D v -> v
    -- Dm v -> v

class (E.Additive a) => FfMon op a where
  ff :: op -> a ->  a

-- class RffMon op a r where
--   rff :: op -> r a -> r a

class (Operable c r a) => MonOp c op r a where

  fd :: (Computation c a ~ m) => op -> D c r a -> m (D c r a)
  df ::
       (Computation c a ~ m)
    => op
    -> D c r a
    -> D c r a
    -> D c r a
    -> m (D c r a)
-- {-#INLINE monOp #-}
monOp :: 
     (MonOp c op r a, FfMon op a, (Trace c op r a), Show op,  FfMon op (A.Array c r a))
  => op
  -> D c r a
  -> Computation c a (D c r a)
monOp op a =
  case a of
    D ap -> return . D $ ff op ap
    -- Dm ap -> return . Dm $ rff op ap
    DF ap at ai -> do
      cp <- fd op ap
      cdf <- df op cp ap at
      return $ DF cp cdf ai
    DR ap _ ai _ -> do
      cp <- fd op ap
      r cp (U op a) ai

class (Operable c r a) => DfDaBin c op r b a | b -> a where
  df_da ::
       (Computation c a ~ m)
    => op
    -> b
    -> D c r a
    -> D c r a
    -> D c r a
    -> m (D c r a)

class (Operable c r b) => DfDbBin c op r a b | a -> b where
  df_db ::
       (Computation c b ~ m)
    => op
    -> a
    -> D c r b
    -> D c r b
    -> D c r b
    -> m (D c r b)

-- class (Show op, E.AdditiveBasis r a, E.AdditiveModule r a) =>
--       FfBin c op a r where
--   rff_bin :: op -> r a -> r a -> r a -- Forward mode function for arrays
--   rff_bin op _ _ =
--     GHC.Err.error $
--     "array x array operation is not defined for " ++ (GHC.Show.show op)
--   r_ff_bin :: op -> r a -> a -> r a -- For scalar x arrays
--   r_ff_bin op _ _ =
--     GHC.Err.error $
--     "array x scalar operation is not defined for " ++ (GHC.Show.show op)
--   _ff_bin :: op -> a -> r a -> r a -- For scalar x arrays
--   _ff_bin op _ _ =
--     GHC.Err.error $
--     "scalar x array operation is not defined for " ++ (GHC.Show.show op)


class (Operable c r d) => DfBin c op r a b d | a b -> d where
  fd_bin :: (Computation c d ~ m) => op -> a -> b -> m (D c r d)
  df_dab ::
       (Computation c d ~ m)
    => op
    -> a
    -> b
    -> (D c r d)
    -> (D c r d)
    -> (D c r d)
    -> (D c r d)
    -> (D c r d)
    -> m (D c r d)

class (Show op) =>
      BinOp op a where
  ff_bin :: op -> a -> a -> a
  binOp :: 
       ( Trace c op r a
       , DfBin c op r (D c r a) (D c r a) a
       , BinOp op (A.Array c r a)
       , DfDaBin c op r (D c r a) a
       , DfDbBin c op r (D c r a) a
       )
    => op
    -> (D c r a)
    -> (D c r a)
    -> Computation c a (D c r a)
  -- {-#INLINE binOp #-}
  binOp op a b = do
    case a of
      D ap ->
        case b of
          D bp -> return . D $ ff_bin op ap bp
          --Dm bp -> return . Dm $ _ff_bin op ap bp
          DF bp bt bi -> do
            cp <- fd_bin op a bp
            cdf <- df_db op a cp bp bt
            return $ DF cp cdf bi
          DR bp _ bi _ -> do
            cfd <- fd_bin op a bp
            r (cfd) (B op a b) bi
      -- Dm ap ->
      --   case b of
      --     D bp -> return . Dm $ r_ff_bin op ap bp
      --     Dm bp -> return . Dm $ rff_bin op ap bp
      --     DF bp bt bi -> do
      --       cp <- fd_bin op a bp
      --       cdf <- df_db op a cp bp bt
      --       return $ DF cp cdf bi
      --     DR bp _ bi _ -> do
      --       cfd <- fd_bin op a bp
      --       r (cfd) (B op a b) bi
      DF ap at ai ->
        case b of
          D _ -> do
            cp <- fd_bin op ap b
            cdf <- df_da op b cp ap at
            return $ DF cp (cdf) ai
          -- Dm _ -> do
          --   cp <- fd_bin op ap b
          --   cdf <- df_da op b cp ap at
          --   return $ DF cp (cdf) ai
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
                  "Forward and reverse AD c r aannot run on the same level."
      DR ap _ ai _ ->
        case b of
          D _ -> do
            fda <- fd_bin op ap b
            r (fda) (B op a b) ai
          -- Dm _ -> do
          --   fda <- fd_bin op ap b
          --   r (fda) (B op a b) ai
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
