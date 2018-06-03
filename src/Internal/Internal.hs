{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE NoMonomorphismRestriction          #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators               #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE UndecidableSuperClasses       #-}
-- # LANGUAGE IncoherentInstances       #

module Internal.Internal (module Internal.Internal) where
import Control.Monad.State.Strict (StateT, get, put)
import qualified Data.Map                   as M 
import           GHC.Err
import           GHC.Exts                   (Item (..))
import           GHC.Show
import           Lens.Micro                 ((&), (.~), (^.), Lens')
import qualified Numeric.Dimensions         as Dim

import           NumHask.Array              ()
import qualified NumHask.Array              as A
import           Unsafe.Coerce              (unsafeCoerce)

import NumHask.Prelude hiding (Show, State, StateT, show)
import qualified NumHask.Prelude            as P



data ComputationState c a = ComputationState
  {
   _nextTag    :: !Tag
  , _nextUID   :: !UID
  , _adjoints  :: Adjoints c a
  , _fanouts   :: Fanouts 
  , _fpEps     :: a
  , _maxFpIter :: Int
  }

type Computation c a = StateT (ComputationState c a) Identity


type ComputationT c a = StateT (ComputationState c a)


type C c r a = Computation c a (D c r a)

type CT c r a m = ComputationT c a m (D c r a) 

data Add = Add deriving Show

type DArray c (r :: [Nat]) a
   = ( P.Additive a
     , P.Foldable c
     , P.MultiplicativeUnital a
     , Dim.Dimensions r
     , A.Container c
     , Show a
     , Show (Item (c a))
     , Item (c a) ~ a
     , IsList (c a)
     )

type WrappedOperable c a
   = ( P.Additive a
     , P.MultiplicativeUnital a
     , A.Container c
     , P.Foldable c
     , Show a
     , Item (c a) ~ a
     , Show (Item (c a))
     , IsList (c a))
  
data D c r a where
  D :: (DArray c '[] a) => a -> D c '[] a
  Dm :: (DArray c r a, IsTensor r) => A.Array c r a -> D c r a
  DF :: (DArray c r a) => Primal c r a -> Tangent c r a -> Tag -> D c r a
  DR
    :: (Show op, Trace c op r a, DArray c r a)
    => D c r a
    -> TraceStack c op r a
    -> Tag
    -> UID
    -> D c r a

getDims :: (DArray c r a) => D c r a -> Dim.Dim r
getDims = \case
  (_ :: D c r a) -> Dim.dim @r

data SomeD c a where
  SomeD :: (DArray c r a) => D c r a -> SomeD c a

instance Show (SomeD c a) where
  show (SomeD d) = P.show d

  
type family GetContainer a where
  GetContainer (D c _ _) = c
  GetContainer (ComputationT c _ _ _) = c

type family GetShape a where
  GetShape (D c r a) = r
  GetShape (ComputationT _ _ _ (D c r a)) = r

type family IsTensor' (a:: [Nat]) where
  IsTensor' '[]= 'False
  IsTensor'  (Dim.Cons n ns) = 'True

type family IsScalar' (a :: [Nat]) where
  IsScalar' '[] = 'True
  IsScalar' (Dim.Cons n ns) = 'False

type IsScalar (a) = ('[] ~ a)
type IsTensor a = (IsTensor' a ~ 'True)

inferTensor :: Dim.Dim ns -> Maybe (Dim.Evidence (IsTensor ns))
inferTensor (_ Dim.:* _) = Just Dim.Evidence
inferTensor _ = Nothing

instance (Show UID, Show (A.Array c r a)) => Show (D c r a) where
  show (D a)            = "D " ++ P.show a
  show (Dm a)           = "Dm " ++  P.show (a)
  show (DF p t ti)      = "DF " ++  P.show p ++ P.show t ++ (" Tag  ")
  show (DR p dt ti uid) = "DR " ++  P.show p ++  P.show dt ++  (" Tag  ")  ++  P.show uid

type Primal c r a = D c r a
type Tangent c r a = D c r a
 
type FptNode c r a = (D c r a, D c r a, D c r a, D c r a) -- nodes needed for a fixpoint evaluation

dmToDs_ :: (IsTensor r, Show (D c r a)) =>  D c r a -> [D c '[] a]
dmToDs_ (Dm (A.Array ar)) = fmap D (P.toList ar)
dmToDs_ a = GHC.Err.error $ "dmToDs_ should have recived a tensor! " ++ show a


class (DArray c r a) =>
      Trace c op r a where
  resetAlg :: (Monad m) => TraceStack c op r a -> ComputationT c a m [SomeD c a]
  resetAlg (U _ a) = pure [SomeD a]
  resetAlg (B _ a b) = pure [SomeD a, SomeD b, SomeD a, SomeD b]
  resetAlg (IxU _ a _) = pure [SomeD a]
  pushAlg :: 
       (Monad m)
    => TraceStack c op r a
    -> D c r a
    -> ComputationT c a m [(SomeD c a, SomeD c a)] -- (delta, node)
  {-# MINIMAL (resetAlg, pushAlg) #-}


instance (DArray c r a, IsTensor r) => Trace c MkDm_of_Ds r a where
  resetAlg (MkDm_of_Ds ds) = pure $ fmap SomeD ds
  pushAlg (MkDm_of_Ds _) dA =
    pure $
    zipWith
      (\i d -> (SomeD $ unsafeMkDfromDmAt dA i, SomeD d))
      [0 ..]
      (dmToDs_ dA) -- dA must be a tensor if it's to necessary to broadcast a scalar to match it's dimension.

instance (DArray c r a) => Trace c Add r a where
  pushAlg (B _ a b) dA =
    pure
      [ (SomeD dA, SomeD a)
      , (SomeD dA, SomeD b)
      , (SomeD dA, SomeD a)
      , (SomeD dA, SomeD b)
      ]

-- | Scalar shape algebra

type family ScalarShapeAlg ar br :: [Nat] where
  ScalarShapeAlg a a = a
  ScalarShapeAlg '[] b = b
  ScalarShapeAlg a '[] = a


data Noop = Noop deriving Show

class ( P.Additive t) => BinBaseOp op ar br t where
  type BinCalcShape ar br :: [Nat]
  baseOpBin :: op -> (D c ar t) -> (D c br t) -> (D c (BinCalcShape ar br) t)

class (P.Additive t) => MonBaseOp op ar t where
  type MonCalcShape ar  :: [Nat]
  baseOpMon :: op -> (D c ar t) -> (D c (MonCalcShape ar) t)
  
data MkDm_of_Ds = MkDm_of_DsCtor deriving Show -- FIXME: this dumb ctor name.

unsafeMkDfromDmAt :: (IsTensor r, DArray c r a) => D c r a -> Int -> D c '[] a
unsafeMkDfromDmAt dm i = case dm of
  Dm (A.Array m) ->  D $  m `A.idx` i
  _ -> GHC.Err.error $  "unsafeMkDfromDmAt was called on an edge that was not a Dm! " ++ (show dm)

-- type BinOpExtras c ar br a
--    = ( ScalarAlg ar br  -- ~ ScalarAlg ar br
--        , ScalarAlg (ScalarShapeAlg ar br) br
--        , ScalarAlg ar (ScalarShapeAlg ar ar) 
--      ) -- Put all Trace- related constraints here.

data TraceStack c op r a where
  N :: (DArray c r a) => op -> TraceStack c op r a
  U
    :: (MonOp c op r a, DArray c r a)
    => op
    -> D c r a
    -> TraceStack c op (MonCalcShape r) a
  B
    :: (BinOp c op ar br a, DArray c ar a, DArray c br a)
    => op
    -> D c ar a
    -> D c br a
    -> TraceStack c op (BinCalcShape ar br) a
  IxU :: (DArray c r a) => op -> D c r a -> [Int] -> TraceStack c op r a
  FxP :: (DArray c r a) => op -> FptNode c r a -> TraceStack c op r a
  MkDm_of_Ds :: (DArray c r a) => [D c '[] a] -> TraceStack c MkDm_of_Ds r a

instance (Show op, DArray c r a) => Show (TraceStack c op r a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d

type Fanouts = M.Map UID Tag

type Adjoints c a = M.Map UID (SomeD c a)

newtype Tag  = Tag Int deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)

nextTag :: Lens' (ComputationState c a) Tag
nextTag wrap (ComputationState nextTag nu a f fe mf) =
  fmap (\newnt -> ComputationState newnt nu a f fe mf) (wrap nextTag)

nextUID :: Lens' (ComputationState c a) UID
nextUID wrap (ComputationState nt nextUID a f fe mf) =
  fmap (\newnu -> ComputationState nt  newnu a f fe mf) (wrap nextUID)

adjoints :: Lens' (ComputationState c a) (Adjoints c a)
adjoints wrap (ComputationState nt nu adjoints f fe mf) =
  fmap (\new -> ComputationState nt nu new f fe mf) (wrap adjoints)

fanouts :: Lens' (ComputationState c a) Fanouts
fanouts wrap (ComputationState nt nu a fanouts fe mf) =
  fmap (\new -> ComputationState nt nu a new fe mf) (wrap fanouts)

fpEps :: Lens' (ComputationState c a) a
fpEps wrap (ComputationState nt nu a f fpEps mf) =
  fmap (\new -> ComputationState nt nu a f new mf) (wrap fpEps)

maxFpIter :: Lens' (ComputationState c a) Int
maxFpIter wrap (ComputationState nt nu a f fe maxFpIter) =
  fmap (\new -> ComputationState nt nu a f fe new) (wrap maxFpIter)

getNextTag :: (Monad m) => ComputationT c a m (Tag)
getNextTag = do
  st <- get
  let tg@(Tag i) = st ^. nextTag
  put
    (st & nextTag .~ ((Tag $ i P.+ 1))
    )
  pure tg

getNextUID :: (Monad m) =>  ComputationT c a m  (UID)
getNextUID = do
  st <- get
  let tg@(UID t) = st ^. nextUID
  put
    (st & nextUID .~ (UID (t P.+ 1)) )
  pure tg


-- Make a reverse node
r :: (Trace c op r a, Show op, Monad m)
  => D c r a
  -> TraceStack c op r a
  -> Tag
  -> ComputationT c a m (D c r a)
r d op ai = do
  uid <- getNextUID
  pure $ DR d op ai uid

-- Get Primal
p :: D c r a -> D c r a
p =
  \case
    D v -> D v
    Dm v -> Dm v
    DF d _ _ -> d
    DR d _ _ _ -> d

-- Get deepest primal
pD :: D c r a -> D c r a
pD =
  \case
    D v -> D v
    Dm v -> Dm v
    DF d _ _ -> pD d
    DR d _ _ _ -> pD d

-- Get Tangent
t :: D s r a
  -> Tangent s r a
t =
  \case
    D _ ->  (D zero)
    DF _ at _ ->  at
    DR {} -> GHC.Err.error "Can't get tangent of a reverse node"
    
instance (Eq a) => Eq (D c r a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D c r a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

toNumeric :: forall c r a. (DArray c r a) => D c r a -> A.Array c r a
toNumeric d =
  case pD d of
    D v -> (A.Array $ A.generate 1 (const v) :: A.Array c '[] a)
    Dm v -> v

toNumericScalar :: D c '[] a -> a
toNumericScalar d =
  case pD d of
    D v -> v
    _ -> GHC.Err.error "Impossible! Deepest primal of an argument toNumericScalar was not a scalar!"


instance (DArray c r a) => IsList (D c r a) where
  type Item (D c r a) = a
  fromList l@(_:_) =
    case inferTensor (Dim.dim @r) of
      Just Dim.Evidence -> Dm $ (A.Array . fromList $ l)
  fromList (x:[]) =
    case Dim.sameDim (Dim.dim @r) (Dim.dim @('[] :: [Nat])) of
      Just Dim.Evidence -> D x
  toList (Dm v) = GHC.Exts.toList v
  toList (D v) = [v]


ofList_ ::
     forall c r a m. (Trace c MkDm_of_Ds r a, P.Monad m, IsTensor r)
  => Proxy r
  -> [D c '[] a]
  -> ComputationT c a m (D c r a)
ofList_ pr l@(a:_) =
  case a of
    D _ -> pure $ fromList sc
    -- Dm _ -> pure . Dm $ fromList sc
    DF _ _ ai -> do
      cap <- ofList_ pr ap
      cat <- ofList_ pr at
      pure $ DF cap cat ai
    DR _ _ ai _ -> do
      ccp <- cp
      r ccp (MkDm_of_Ds l) ai
  where
    sc = map toNumericScalar l :: [a]
    ap = map p l
    at = map t l
    cp = ofList_ pr ap
      
type IsMonOp op c r a = (DArray c r a
      , DArray c (MonCalcShape r) a
      , MonBaseOp op r a
      , MonOp c op r a
      , Show op
      , Trace c op (MonCalcShape r) a
      , Trace c op r a)

class ( DArray c r a
      , DArray c (MonCalcShape r) a
      , MonBaseOp op r a
      , Show op
      , Trace c op (MonCalcShape r) a
      , Trace c op r a
      ) =>
      MonOp c op r a where
  fd ::
       (ComputationT c a m ~ mm, Monad m)
    => op
    -> D c r a
    -> mm (D c (MonCalcShape r) a)
  df ::
       (Monad m)
    => op
    -> D c (MonCalcShape r) a
    -> D c r a
    -> D c r a
    -> ComputationT c a m (D c (MonCalcShape r) a)
  monOp ::
       (Monad m) => op -> D c r a -> ComputationT c a m (D c (MonCalcShape r) a)
  monOp op a =
    case a of
      D _ -> pure $ baseOpMon op a
      Dm _ -> pure $ baseOpMon op a
      DF ap at ai -> do
        cp <- fd op ap
        cdf <- df op cp ap at
        pure $ DF cp cdf ai
      DR ap _ ai _ -> do
        cp <- fd op ap
        r cp (U op a) ai

type APrimal c r a = Primal c r a
type BPrimal c r a = Primal c r a
type CPrimal c r a = Primal c r a

type ATangent c r a = Tangent c r a
type BTangent c r a = Tangent c r a

class (DfOperable op c ar br a) =>
      DfDaBin c op ar br a where
  --type DfDaShape ar br :: [Nat]
  df_da ::
       (Monad m)
    => op
    -> D c br a
    -> CPrimal c (BinCalcShape ar br) a
    -> BPrimal c ar a
    -> BTangent c ar a
    -> ComputationT c a m (D c (BinCalcShape ar br) a)

scalarToTensorLike ::
     (DArray c t a, Monad m, IsTensor t)
  => D c '[] a
  -> Proxy t
  -> ComputationT c a m (D c t a)
scalarToTensorLike (D v) _ = pure . Dm . fromList $ repeat v

sameOrError ::
     (DArray c ar a, DArray c br a)
  => (D c ar a -> D c br a -> ComputationT c a m (D c cr a))
  -> D c ar a
  -> D c br a
  -> ComputationT c a m (D c cr a)
sameOrError f (da :: D c ar a) (db :: D c br a) =
  case Dim.sameDim (Dim.dim @br) (Dim.dim @ar) of
    Just Dim.Evidence -> f da db
    _ ->
      GHC.Err.error $
      "Expected dimensions to be the same!  This should be impossible: Please report this as a bug in diffhask! Values:" ++
      show da ++ "  " ++ show db



    
handleScalarBroadcast ::
     (P.Monad m)
  => (D c (ScalarShapeAlg ar br) a -> Tangent c (ScalarShapeAlg ar br) a -> ComputationT c a m (D c (ScalarShapeAlg ar br) a))
  -> D c ar a
  -> Tangent c br a
  -> ComputationT c a m (D c (ScalarShapeAlg ar br) a)
handleScalarBroadcast f a t =
  case (a, t) of
    (D _, D _ ) -> f a t
    (Dm _, D _) -> do
      ct <- scalarToTensorLike t (Proxy :: Proxy ar)
      f a ct
    (D _, Dm _) -> do
      ca <- scalarToTensorLike a (Proxy :: Proxy br)
      f ca t
    (Dm da :: D c ar a, Dm dt :: Tangent c br a) ->
      case Dim.sameDim (Dim.dim @ar) (Dim.dim @br) of
        Just Dim.Evidence -> f (Dm da) (Dm dt)
        _ ->
          GHC.Err.error $
          "Expected dimensions to be the same!  This should be impossible: Please report this as a bug in diffhask! Values:" ++
          show da ++ "  " ++ show dt

class (DfOperable op c ar br a) =>
      DfDbBin c op ar br a
  --type DfDbShape ar br :: [Nat]
                                  where
  df_db ::
       (Monad m)
    => op
    -> D c ar a
    -> CPrimal c (BinCalcShape ar br) a
    -> APrimal c br a
    -> ATangent c br a
    -> ComputationT c a m (D c (BinCalcShape ar br) a)


type DfOperable op c ar br a
   = (DArray c ar a, DArray c br a, IsBinOp c op ar br a)

instance (DfOperable Add c ar br a) =>
         DfDbBin c Add ar br a where
  --type DfDbShape ar br = ScalarShapeAlg ar br -- IfScalarThenMkTensor' br ar
  {-# INLINE df_db #-}
  df_db _ a _ _ bt =
    case (a, bt) of
      (Dm _, D _) -> scalarToTensorLike bt (Proxy :: Proxy ar)
      (D _, Dm _) -> scalarToTensorLike a (Proxy :: Proxy br)
      _ ->
        case Dim.sameDim (Dim.dim @br) (Dim.dim @ar) of
          Just Dim.Evidence -> pure bt
          _ ->
            GHC.Err.error $
            "Expected tangent value of `bt` to be a scalar or of the same dimension as `a` in call to `df_db`!  Please report this as a bug in diffhask! Values:" ++
            show bt ++ "  " ++ show a


instance (DArray c ar a, DArray c br a, IsBinOp c Add ar br a) =>
         DfDaBin c Add ar br a where
  --type DfDaShape ar br = ScalarShapeAlg ar br
  {-# INLINE df_da #-}
  df_da _ b _ _ at =
    case (b, at) of
      (Dm _, D _) -> scalarToTensorLike at (Proxy :: Proxy br)
      (D _, Dm _) -> scalarToTensorLike b (Proxy :: Proxy ar)
      _ ->
        case Dim.sameDim (Dim.dim @br) (Dim.dim @ar) of
          Just Dim.Evidence -> pure at
          _ ->
            GHC.Err.error $
            "Expected tangent value of `at` to be a scalar or of the same dimension as `b` in call to `df_db`!  Please report this as a bug in diffhask! Values:" ++
            show at ++ "  " ++ show b


type IsBinOp c op ar br a
   = ( P.Additive a
     , BinBaseOp op ar br a
     , Trace c op ar a
     , Trace c op br a
     , Trace c op (BinCalcShape ar br) a
     , DArray c (BinCalcShape ar br) a
     --, DArray c (ScalarShapeAlg ar br) a
     )



instance ( IsBinOp c Add ar br a
         
         --, BinOp c Add (BinCalcShape ar br) br a ~ BinOp c Add ar (BinCalcShape ar br) a
         ) =>
         BinOp c Add ar br a

instance (P.Additive t) => BinBaseOp Add ar br t where
  type BinCalcShape ar br = ScalarShapeAlg ar br
  baseOpBin _ (D a) (D b) = D $ a P.+ b
  baseOpBin _ (Dm a) (D b) = Dm $ a P..+ b
  baseOpBin _ (D a) (Dm b) = Dm $ a P.+. b
  baseOpBin _ (Dm a) (Dm b) =
    case Dim.sameDim (Dim.dim @ar) (Dim.dim @br) of
      Just Dim.Evidence -> Dm $ a P..+. b
      Nothing ->
        GHC.Err.error
          "Dimensions of arguments to binOp should have been equal: Please report this as a bug in diffhask."


instance ( DArray s ar a
         , DArray s br a
         , BinOp s Add ar br a
         , Trace s Add ar a
         , Trace s Add br a
         , Trace s Add (BinCalcShape ar br) a
         ) =>
         DfBin s Add ar br a where
  {-# inline fd_bin #-}
  fd_bin _ a b = binOp Add a b
  {-# inline df_dab #-}
  df_dab _ _ _ _ _ at _ bt = binOp Add at bt

class (DArray c ar t, DArray c br t) =>
      DfBin c op ar br t where
  fd_bin ::
       (Monad m)
    => op
    -> (D c ar t)
    -> (D c br t)
    -> ComputationT c t m (D c (BinCalcShape ar br) t)
  df_dab ::
       (Monad m)
    => op
    -> (D c ar t)
    -> (D c br t)
    -> (D c (BinCalcShape ar br) t)
    -> (D c ar t)
    -> (D c ar t)
    -> (D c br t)
    -> (D c br t)
    -> ComputationT c t m (D c (BinCalcShape ar br) t)



class ( Show op
      , BinBaseOp op ar br a
      , BinBaseOp op (BinCalcShape ar br) br a
      , BinBaseOp op ar (BinCalcShape ar br) a
      , Trace c op ar a
      , Trace c op br a
      , Trace c op (BinCalcShape ar br) a
      , DfBin c op ar br a
      , DfDbBin c op ar br a
      , DfDaBin c op ar br a
      ) =>
      BinOp c op ar br a where
  binOp :: (Monad m) =>
       op
    -> (D c ar a)
    -> (D c br a)
    -> ComputationT c a m (D c (BinCalcShape ar br) a)
  binOp = binOp'


{-# inline binOp' #-}
binOp' ::
     ( BinOp c op ar br a
     , BinBaseOp op ar br a
     , BinBaseOp op (BinCalcShape ar br) br a
     , BinBaseOp op ar (BinCalcShape ar br) a
     , Trace c op ar a
     , Trace c op br a
     , Trace c op (BinCalcShape ar br) a
     , DfBin c op ar br a
     , DfDbBin c op ar br a
     , DfDaBin c op ar br a
     , Monad m
     )
  => op
  -> (D c ar a)
  -> (D c br a)
  -> ComputationT c a m (D c (BinCalcShape ar br) a)

binOp' op a@(D ap) b@(D bp) = pure $ baseOpBin op a b

binOp' op a@(D ap) b@(Dm bp) = pure $ baseOpBin op a b

binOp' op a@(D ap) (DF bp bt bi) = do
  cp <- fd_bin op a bp
  cdf <- df_db op a cp bp bt
  pure $ DF cp cdf bi

binOp' op a@(D ap :: D c ar a) b@(DR bp _bt bi _btt :: D c br a) = do
  cfd <- fd_bin op a bp
  r (cfd) (B op (D ap) (DR bp _bt bi _btt)) bi

binOp' op a@(Dm ap) b@(D bp) = pure $ baseOpBin op a b

binOp' op a@(Dm ap) b@(Dm bp) = pure $ baseOpBin op a b

binOp' op a@(Dm ap) (DF bp bt bi) = do -- eq
  cp <- fd_bin op a bp -- br
  cdf <- df_db op a cp bp bt
  pure $ DF cp cdf bi
binOp' op a@(Dm ap) b@(DR bp _ bi _) = do
  cfd <- fd_bin op a bp
  r (cfd) (B op a b) bi

binOp' op a@(DF ap at ai) b@(D _ ) = do
  cp <- fd_bin op ap b
  cdf <- df_da op b cp ap at
  pure $ DF cp (cdf) ai

binOp' op a@(DF ap at ai) b@(Dm _ ) = do -- eq
  cp <- fd_bin op ap b --ar
  cdf <- df_da op b cp ap at
  pure $ DF cp (cdf) ai

binOp' op a@(DF ap at ai) b@(DF bp bt bi ) =
  case compare ai bi of
    EQ -> do
      cp <- fd_bin op ap bp
      cdf <- df_dab op a b cp ap at bp bt
      pure $ DF cp (cdf) ai
    LT -> do
      cp <- fd_bin op a bp
      cdf <- df_db op a cp bp bt
      pure $ DF cp (cdf) bi
    GT -> do
      cp <- fd_bin op ap b -- ar
      cdf <- df_da op b cp ap at
      pure $ DF cp (cdf) ai

binOp' op a@(DF ap at ai) b@(DR bp _ bi _) =
  case compare ai bi of
    LT -> do
      fdb <- fd_bin op a bp
      r (fdb) (B op a b) bi
    GT -> do
      cp <- fd_bin op ap b -- ar
      cdf <- df_da op b cp ap at
      pure $ DF cp (cdf) ai
    EQ ->
      GHC.Err.error "Forward and reverse AD c r aannot run on the same level."

binOp' op a@(DR ap _ ai _) b@(D _) = do
  fda <- fd_bin op ap b
  r (fda) (B op a b) ai

binOp' op a@(DR ap _ ai _) b@(Dm _) = do
  fda <- fd_bin op ap b
  r (fda) (B op a b) ai

binOp' op a@(DR ap _ ai _) b@(DF bp bt bi) =
  case compare ai bi of
    EQ -> GHC.Err.error "Forward and reverse AD cannot run on the same level."
    LT -> do
      cp <- fd_bin op a bp
      cdf <- df_db op a cp bp bt
      pure $ DF cp (cdf) bi
    GT -> do
      fdb <- fd_bin op ap b
      r (fdb) (B op a b) ai

binOp' op a@(DR ap _ ai _) b@(DR bp _ bi _) =
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

