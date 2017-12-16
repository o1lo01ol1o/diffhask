{-#LANGUAGE LambdaCase#-}
{-#LANGUAGE GADTs #-}
{-#LANGUAGE TypeFamilies #-}
{-#LANGUAGE MultiParamTypeClasses#-}
{-#LANGUAGE FlexibleInstances #-}
{-#LANGUAGE FlexibleContexts #-}
{-#LANGUAGE ConstraintKinds #-}
{-#LANGUAGE PolyKinds #-}
{-#Language DataKinds #-}
{-#Language TemplateHaskell #-}
{-#Language NoImplicitPrelude #-}

{-#Language UndecidableInstances #-}
module Core
    ( module Core
    ) where

import qualified Data.Map as M (Map, updateLookupWithKey, insert, empty, lookup, update)
import Lens.Micro.TH (makeLenses)
import Prelude hiding ((+), (*), (-))
import qualified Prelude as P 
import Lens.Micro ((^.), (.~), (&), (%~))
import Control.Monad.State.Strict
       (State,  get, modify, put, gets, (>=>), evalState, runState)
import Ops (Noop(..), Add(..), Subtract(..), Multiply(..))


--The types of arity an operation can have

data Arity
  = Unary
  | Binary
  | Nil
  | SymmetricBinary
  | IndexedUnary
  | FxPoint


-- the tape at a binary operation will either have two expressions (one to each arugment of the op) or a single expression
type family OpArity op :: Arity -- Encodes the arity of the arguments of the op


-- type instance OpTapeArity op 
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
  { _nextTag :: !Tag
  , _nextUID :: !UID
  , _adjoints :: Adjoints a
  , _fanouts :: Fanouts
  , _fpEps :: a
  , _maxFpIter :: Int
  }

type Computation a = State (ComputationState a)

data D a where
  D :: a -> D a
  DF :: Primal a -> Tangent a -> Tag -> D a
  DR :: (Trace op a) => D a -> DualTrace op a -> Tag -> UID -> D a

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


class Core a where
  (+) :: D a -> D a -> Computation a (D a)
  (-) :: D a -> D a -> Computation a (D a)
  (*) :: D a -> D a -> Computation a (D a)
  abs :: D a -> Computation a (D a)
  signum :: D a -> Computation a (D a)
  zero :: D a
  one :: D a

type CoreConstraints a = (BinOp Add a, BinOp Subtract a, BinOp Multiply a, Trace Add a, Trace Subtract a, Trace Multiply a, Ord a)
instance (CoreConstraints Float) => Core Float where
  (+) a b = binOp Add a b
  (-) a b = binOp Subtract a b
  (*) a b = binOp Multiply a b
  zero = D 0
  one = D 1

instance (CoreConstraints Double) => Core Double where
  (+) a b = binOp Add a b
  (-) a b = binOp Subtract a b
  (*) a b = binOp Multiply a b
  zero = D 0
  one = D 1

initComp :: (Fractional a) => ComputationState a
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty (0.0000001) 1000


-- Make a reverse node
r :: (Trace op a) => D a -> DualTrace op a -> Tag  -> Computation a (D a)
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
t :: (Core a) => D a -> Tangent a
t =
  \case
    D _ -> zero
    DF _ at _ -> at
    DR {} -> error "Can't get tangent of a reverse node"

mkForward :: Tag -> Primal a -> Tangent a  -> D a
mkForward i d t = DF d t i


mkReverse :: (Trace Noop a) => Tag -> D a -> Computation a (D a)
mkReverse i d = do
  st <- get
  r d (N Noop) i

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
     (Trace op a, Computation a ~ m)
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
binOp' _ a b ff fd df_da df_db df_dab r_d_d r_d_c r_c_d = do
  case a of
    D ap ->
      case b of
        D bp -> return . D $ ff ap bp
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




binOp :: ( BinOp op a,(Trace op a), Computation a ~ m)
  =>
  op
  ->  (D a)
  ->  (D a)
  -> m (D a)
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
       (fd_bin op)
       (df_da op b)
       (df_db op a)
       (df_dab op)
       r_d_d
       r_d_c
       r_c_d

class BinOp op a where
  ff_bin :: (Computation a ~ m) => op -> a -> a ->  a
  fd_bin :: (Computation a ~ m) => op ->  (D a) -> (D a) ->  m (D a)
  df_db :: (Computation a ~ m) => op -> (D a) -> (D a) -> (D a) -> (D a) -> m (D a)
  df_da :: (Computation a ~ m) => op -> (D a) -> (D a) -> (D a) -> (D a) -> m (D a)
  df_dab ::
       (Computation a ~ m)
    => op
    -> (D a)
    -> (D a)
    -> (D a)
    -> (D a)
    -> (D a)
    -> m (D a)

eval :: (Core a) => Delta a -> Computation a (D a)
eval dl =
  case dl of
    X v -> pure v
    XNeg v -> zero - v


           
applyDelta :: (Core a) => UID -> Delta a -> Adjoints a -> (Maybe (Computation a (D a)))
applyDelta tag dlta adjs=
  case M.lookup tag adjs of
    Just v -> Just $ do
      e <- eval dlta
      r <- v + e
      modify (\st -> st & adjoints .~ M.update (const . Just $ r) tag adjs)
      return r
    Nothing -> Nothing
  -- M.updateLookupWithKey
  --   (\ k v -> Just $ go dlta k v)
  --   tag
  -- where
  --   go :: Delta a ->  UID -> D a -> (Computation a (D a))
  --   go dlta k v =  do
  --      e <- eval dlta
  --      r <- v + e
  --      return r

decrementFanout :: UID -> Fanouts -> (Maybe Tag, Fanouts)
decrementFanout =
  M.updateLookupWithKey (\k (Tag v) -> Just . Tag $ v P.- 1)  
  
-- updateStack ls = modify (\ st -> st & stack %~ mappend ls)
  
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
  

reset :: (Core a) => [D a] -> Computation a ()
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
        _ -> error "Can only reset reverse nodes!"

-- recursively pushes nodes onto the reverse mode stack and evaluates partials
push :: (Core a) =>[(Delta a, D a)] -> Computation a ()
push l =
  case l of
    [] -> return ()
    ((dl, da):xs) ->
      case da of
        DR _ o _ uniq -> do
          st <- gets (\ st -> st ^. adjoints )
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

reverseReset :: (Core a) => D a -> Computation a ()
reverseReset d = do
  modify (\st -> st & fanouts .~ M.empty )
  reset [d]

reverseProp :: (Core a) => D a -> D a -> Computation a ()
reverseProp  v d = do
  reverseReset  d
  push [(X v, d)]

{-# INLINE primalTanget #-}
primalTanget :: (Core a) => D a -> (D a, Tangent a)
primalTanget d = (p d, t d)

adjoint :: (Core a) => D a -> Computation a (D a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> return zero


runComputation f s = runState f s

compute f = evalState f initComp


{-# INLINE computeAdjoints' #-}
computeAdjoints' :: (Core a) => D a -> Computation a ()
computeAdjoints' d = do
  modify (\st -> st & adjoints .~ M.empty)
  reverseProp one d
  
{-# INLINE computeAdjoints #-}
computeAdjoints :: (Core a) => D a -> Computation a (Adjoints a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' :: (Core a) => (D a ->  Computation a (D a)) -> D a -> Computation a (D a, Tangent a)
diff' f x = do
  n <- getNextTag
  fout <- f $ mkForward n one x
  return $ primalTanget fout
{-# INLINE diff #-}

diff :: (Core a) => (D a -> Computation a (D a)) -> D a -> Computation a (Tangent a)
diff f x = 
  snd <$> diff' f x
  
{-# INLINE diffn #-}
diffn :: (Core a) => Int -> (D a -> Computation a (D a)) -> D a -> Computation a (Tangent a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go :: (Core a) => Int -> (D a -> Computation a (D a)) -> D a -> Computation a (Tangent a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn'
  :: (Core a) => Int -> (D a -> Computation a (D a)) -> D a -> Computation a (D a, (Tangent a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  return (it, again)
  
{-# INLINE grad' #-}
grad' ::
     (Trace Noop a, Core a) =>
  (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, (D a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  z <- f xa
  computeAdjoints' z
  adj <- adjoint xa
  return (p xa, adj)
  
{-# INLINE grad #-}
grad ::
     (Trace Noop a, Core a) =>
   (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: (Core a) =>
     (D a -> Computation a (D a)) -> Tangent a -> Primal a -> Computation a (D a, Tangent a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  return $ primalTanget fout

jacobian :: (Core a) => (D a -> Computation a (D a)) -> Tangent a -> Primal a -> Computation a (Tangent a)
jacobian f x v = snd <$> jacobian' f x v
