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
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators               #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
module Internal.Internal (module Internal.Internal) where
import Control.Monad.State.Strict (StateT, get, put)
import qualified Data.Map                   as M 
import           GHC.Err
import           GHC.Exts                   (Item (..))
import           GHC.Show
import           Lens.Micro                 ((&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import qualified Numeric.Dimensions         as Dim
import           NumHask.Array              ()
import qualified NumHask.Array              as A
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


data Add = Add deriving Show

type Operable c r a
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
     , IsList (c a)
     )

data D c r a where
  D :: (Operable c '[] a) => a -> D c '[] a
  Dm :: (Operable c r a) => A.Array c r a -> D c r a
  DF :: (Operable c r a) => Primal c r a -> Tangent c r a -> Tag -> D c r a
  DR
    :: (Show op, Trace c op r a, Operable c r a)
    => D c r a
    -> TraceStack c op r a
    -> Tag
    -> UID
    -> D c r a

getDims :: (Dim.Dimensions r) => D c r a -> Dim.Dim r
getDims = \case
  (_ :: D c r a) -> Dim.dim @r

data SomeD c a where
  SomeD :: (Operable c r a) => D c r a -> SomeD c a

instance Show (SomeD c a) where
  show (SomeD d) = P.show d

  
type family GetContainer a where
  GetContainer (D c _ _) = c
  GetContainer (ComputationT c _ _ _) = c

type family GetShape a where
  GetShape (D c r a) = r
  GetShape (ComputationT _ _ _ (D c r a)) = r

type SameContainer a b = (GetContainer a ~ GetContainer b)
  
type family SameTransformer' a b m :: Bool where
  SameTransformer' (ComputationT _ _ m _) (D _ _ _) m = 'True
  SameTransformer' (D _ _ _) (ComputationT _ _ m _)  m = 'True
  SameTransformer' (D _ _ _) (D _ _ _)  m = 'True
  SameTransformer' (ComputationT _ _ m _) (ComputationT _ _ m _)  m = 'True
  SameTransformer' _ _ _ = 'False

type SameMonad a b m = (SameTransformer' a b m ~ 'True)


type family IsTensor a where
  IsTensor (x:xs) = 'True
  IsTensor '[] = 'False

instance (Show UID) => Show (D c r a) where
  show (D a)            = "D " ++ P.show a
  show (Dm a)           = "Dm " ++  P.show (a)
  show (DF p t ti)      = "DF " ++  P.show p ++ P.show t ++ (" Tag  ")
  show (DR p dt ti uid) = "DR " ++  P.show p ++  P.show dt ++  (" Tag  ")  ++  P.show uid

type Primal c r a = D c r a
type Tangent c r a = D c r a

type FptNode c r a = (D c r a, D c r a, D c r a, D c r a) -- nodes needed for a fixpoint evaluation

dmToDs_ :: (IsTensor r ~ 'True) =>  D c r a -> [D c '[] a]
dmToDs_ (Dm (A.Array ar)) = fmap D (P.toList ar)
dmToDs_ a = GHC.Err.error $ "dmToDs_ should have recived a tensor! " ++ show a


class ( Operable c r a
      ) =>
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


instance (Operable c r a, IsTensor r ~ 'True) => Trace c MkDm_of_Ds r a where
  resetAlg (MkDm_of_Ds ds) = pure $ fmap SomeD ds
  pushAlg (MkDm_of_Ds _) dA =
    pure $
    zipWith
      (\i d -> (SomeD $ unsafeMkDfromDmAt dA i, SomeD d))
      [0 ..]
      (dmToDs_ dA) -- dA must be a tensor if it's to necessary to broadcast a scalar to match it's dimension.

instance (Operable c r a) => Trace c Add r a where
  pushAlg (B _ a b) dA = pure [( SomeD dA, SomeD a), (SomeD dA, SomeD b), (SomeD dA, SomeD a), (SomeD dA, SomeD b)]


data Noop = Noop deriving Show

class (P.Additive t, Dim.Dimensions ar, Dim.Dimensions br) => BinBaseOp op (ar :: [Nat]) (br :: [Nat]) t where
  type BinCalcShape ar br :: [Nat]
  baseOpBin :: op -> (D c ar t) -> (D c br t) -> (D c (BinCalcShape ar br) t)

class (P.Additive t, Dim.Dimensions ar) => MonBaseOp op (ar :: [Nat]) t where
  type MonCalcShape ar :: [Nat]
  baseOpMon :: op -> (D c ar t) -> (D c (MonCalcShape ar) t)
  
data MkDm_of_Ds = MkDm_of_DsCtor deriving Show -- FIXME: this dumb ctor name.

unsafeMkDfromDmAt :: (IsTensor r ~ 'True) => D c r a -> Int -> D c '[] a
unsafeMkDfromDmAt dm i = case dm of
  Dm (A.Array m) ->  D $  m `A.idx` i
  _ -> GHC.Err.error $  "unsafeMkDfromDmAt was called on an edge that was not a Dm! " ++ (show dm)


data  TraceStack c op r a where
  N :: op -> TraceStack c op r a
  U :: (MonBaseOp op r a) => op -> D c r a -> TraceStack c op (MonCalcShape r) a
  B
    :: (BinBaseOp op ar br a)
    => op
    -> D c ar a
    -> D c br a
    -> TraceStack c op (BinCalcShape ar br) a
  IxU :: op -> D c r a -> [Int] -> TraceStack c op r a
  FxP :: op -> FptNode c r a -> TraceStack c op r a
  MkDm_of_Ds :: [D c '[] a] -> TraceStack c MkDm_of_Ds r a

instance (Show op) => Show (TraceStack c op r a) where
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

makeLenses ''ComputationState


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

toNumeric :: forall c r a. D c r a -> A.Array c r a
toNumeric d =
  case pD d of
    D v ->  (A.Array $ A.generate 1 (const v) :: A.Array c '[] a)
    Dm v -> v

toNumericScalar :: D c '[] a -> a
toNumericScalar d =
  case pD d of
    D v -> v
    _ -> GHC.Err.error "Impossible! Deepest primal of an argument toNumericScalar was not a scalar!"


instance (Operable c r a) => IsList (D c r a) where
  type Item (D c r a) = a
  fromList l = Dm (A.Array . fromList $ l)
  toList (Dm v) = GHC.Exts.toList v
  toList (D v) = [v]
  -- FIXME: resolve what to do here with other cases.

ofList_ ::
     forall c r a m. (Trace c MkDm_of_Ds r a, P.Monad m)
  => Proxy r
  -> [D c '[] a]
  -> ComputationT c a m (D c r a)
ofList_ pr l@(a:_) =
  case a of
    D _ -> pure $ fromList sc
    Dm _ -> pure . Dm $ (fromList) sc
    DF _ _ ai -> do
      cap <- ofList_ pr ap
      cat <- ofList_ pr at
      pure $ DF (cap) (cat) ai
    DR _ _ ai _ -> do
      ccp <- cp
      r ccp (MkDm_of_Ds l) ai
  where
    sc = map (toNumericScalar) l :: [a]
    ap = map p l
    at = map t l
    cp = ofList_ pr ap
      
type IsMonOp op c r a = (Operable c r a
      , Operable c (MonCalcShape r) a
      , MonBaseOp op r a
      , MonOp c op r a
      , Show op
      , Trace c op (MonCalcShape r) a
      , Trace c op r a)

class ( Operable c r a
      , Operable c (MonCalcShape r) a
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

class (Operable c ar a, Operable c br a, IsBinOp c op ar br a, (BinCalcShape ar br) ~ (DfDaShape ar br)) =>
      DfDaBin c op ar br a where
  type DfDaShape ar br :: [Nat]
  df_da ::
       (Monad m)
    => op
    -> D c br a
    -> CPrimal c (BinCalcShape ar br) a
    -> BPrimal c ar a
    -> BTangent c ar a
    -> ComputationT c a m (D c (DfDaShape ar br) a)

scalarToTensorLike :: (Operable c t a, Monad m) => D c '[] a -> Proxy t -> ComputationT c a m (D c t a)
scalarToTensorLike (D v) _ = pure. fromList $ repeat v
    

class (Operable c ar a, Operable c br a, IsBinOp c op ar br a, (BinCalcShape ar br) ~ (DfDbShape ar br)) =>
      DfDbBin c op ar br a where
  type DfDbShape ar br :: [Nat]
  df_db ::
       (Monad m)
    => op
    -> D c ar a
    -> CPrimal c (BinCalcShape ar br) a
    -> APrimal c br a
    -> ATangent c br a
    -> ComputationT c a m( D c (DfDbShape ar br) a)


instance (Operable c ar a, Operable c br a, IsBinOp c Add ar br a) =>
         DfDbBin c Add ar br a where
  type DfDbShape ar br = ScalarShapeAlg ar br -- IfScalarThenMkTensor' br ar
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


instance (Operable c ar a, Operable c br a, IsBinOp c Add ar br a) =>
         DfDaBin c Add ar br a where
  type DfDaShape ar br = ScalarShapeAlg ar br
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
     , Operable c (BinCalcShape ar br) a
     , Operable c (ScalarShapeAlg ar br) a)


instance (IsBinOp c Add ar br a) => BinOp c Add ar br a

instance (P.Additive t, Dim.Dimensions ar, Dim.Dimensions br) => BinBaseOp Add ar br t where
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


instance ( Operable s ar a
         , Operable s br a
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

class (Operable c ar t, Operable c br t) =>
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


type family ScalarShapeAlg (a :: [Nat]) (b :: [Nat]) :: [Nat] where
  ScalarShapeAlg '[] a = a
  ScalarShapeAlg a '[] = a
  ScalarShapeAlg a a = a

{-# inline binOp' #-}
binOp' ::
     ( BinOp c op ar br a
     , BinBaseOp op ar br a
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

binOp' op a@(D ap) b@(DR bp _ bi _) = do
  cfd <- fd_bin op a bp
  r (cfd) (B op a b) bi

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
