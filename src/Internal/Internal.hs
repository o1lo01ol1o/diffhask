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
{-# LANGUAGE UndecidableInstances   #-}

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
  D :: a -> D a -- scalar
  DF :: Primal a -> Tangent a -> Tag -> D a
  DR :: (Show op) => D a -> DualTrace op a -> Tag -> UID -> D a



instance (Show a, Show Tag, Show UID ) => Show (D a) where
  show (D a) = "D " ++ show a
  show (DF p t ti) = "DF " ++ show p ++ show t ++ show ti
  show (DR p dt ti uid) = "DR " ++ show p ++ show dt ++ show ti ++ show uid

type Primal a = D a
type Tangent a = D a

type FptNode a = (D a, D a, D a, D a) -- nodes needed for a fixpoint evaluation

class AdditiveBox a b t | a b -> t where
  boxAdd :: a -> b -> Computation t (D t)

class AdditiveBoxModule r a b t | a b -> t where
  boxModuleAddL ::
       (ModuleShape a ~ r t) => a -> b -> Computation t (D (ModuleShape a))
  boxModuleAddR ::
       (ModuleShape b ~ r t) => a -> b -> Computation t (D (ModuleShape b))

class AdditiveBoxBasis a b m t | a b -> t, a -> t, b -> t where
  boxBasisAdd :: a -> b -> Computation t (D (m t))

type ScalarInABox a = (ModuleType (D a) ~ a, P.Num a, AdditiveBox (D a) (D a) a)

data Contents = Array | Scalar

data Box a where
  X
    :: (AdditiveBox (D a) (D a) (ModuleType (D a)), ModuleShape (D a) ~ a)
    => D a
    -> Box (ModuleType (D a))
  M
    :: ( AdditiveBoxModule r (D t) a t
       , AdditiveBoxModule r a (D t) t
       , AdditiveBoxBasis (D (r a)) (D (r a)) r t
       , t ~ ModuleType (D (r a))
       )
    => D (r a)
    -> Box t

-- class CDelta a t where
--   data Delta t v

type family IsScalar a where
  IsScalar (D (r a)) = 'False
  IsScalar (Computation t (D (r t))) = 'False
  IsScalar (D a) = 'True
  IsScalar (Computation t (D t)) = 'True

-- Helper to extract the module parameters while remainting polymorphic with respect to inputs of (D a) and (Computation t (D a)).
-- This could be made more general as an open type family and used in all NumHask signitures to deal with more expressive types of things that should be treated as numbers
-- ie, our state / D a pair.
type family ModuleShape a where
  ModuleShape (D (r t)) = r t
  ModuleShape (Computation t (D (r t))) = r t
  ModuleShape (D (t)) = t
  ModuleShape (Computation t (D (t))) = t

type family ModuleType a where
  ModuleType (D (r t)) = t
  ModuleType (Computation t (D (r t))) =  t
  ModuleType (D (t)) = t
  ModuleType (Computation t (D (t))) = t


type family ModuleTypes a b where
  ModuleTypes (D (r t)) _ = t
  ModuleTypes (Computation t (D (r t))) _ = t
  ModuleTypes _ (Computation t (D (r t))) = t
  ModuleTypes _ (D (r t)) = t
  ModuleTypes (D (t)) (D (t)) = t

type family AddModules a b where
  AddModules (D (r t)) _ = (D (r t))
  AddModules _ (D (r t)) = (D (r t))
  AddModules (D (t)) (D (t)) = (D (t))

-- FIXME: singleton types on the DualTrace / Arity combination would restrict at least resetEl to a single possible implementation.
class Trace op a where
  resetEl :: (ModuleType b ~ a) => DualTrace op a -> Computation a [Box b]
  pushEl ::
       (ModuleType (D a) ~ t)
    => DualTrace op a
    -> D a
    -> Computation t [(Box a, Box a)]
  {-# MINIMAL (resetEl, pushEl) #-}



data Noop = Noop deriving Show

data Add = Add deriving Show


data Subtract = Subtract deriving Show

data Negate = Negate deriving Show

data Multiply = Multiply deriving Show

data Divide = Divide deriving Show



-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace op a where
  N :: op -> DualTrace op a
  U ::  op -> D a -> DualTrace op a
  B :: op -> D a -> D a -> DualTrace op a
  IxU :: op -> D a -> [Int]  -> DualTrace op a
  FxP :: op ->  FptNode a -> DualTrace op a

instance (Show op, Show a) => Show (DualTrace op a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d

type Fanouts = M.Map UID Tag

type Adjoints a = M.Map UID (Box a)

newtype Tag = Tag Int
  deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)

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


-- Make a reverse node
r :: (Trace op a, Show op) => D a -> DualTrace op a -> Tag  -> Computation a (D a)
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

instance (Eq a) => Eq (D a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

toNumeric :: D a -> a

toNumeric d =
  let (D n) = pD d
  in n


monOp :: (MonOp op a, (Trace op a), Show op) => op -> D a -> Computation a (D a)
monOp op a =
  let r_d =   U op
  in monOp' op a (ff op) (fd op) (df op) r_d

monOp' :: (Trace op a, Computation a ~ m, Show op) =>
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

binOp' ::
     (Num a, Trace op a, Computation a ~ m, Show op)
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



class (Num c, Show op) => FFBin op c where
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
         
class MonOp op a where
  ff ::( Computation a ~ m) => op -> a -> a
  fd :: ( Computation a ~ m) =>  op -> D a -> m (D a)
  df :: ( Computation a ~ m) =>  op -> D a -> D a -> D a ->m( D a)
  

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
