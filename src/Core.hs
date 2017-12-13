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
{-#LANGUAGE UndecidableInstances #-} -- FIXME: collapse type classes so we can drop this.

module Core
    ( module Core
    ) where

import qualified Data.Map as M (Map, updateLookupWithKey, insert, empty, lookup)
import Lens.Micro.TH (makeLenses)
import Lens.Micro ((^.), (.~), (&), (%~))
import Control.Monad.State.Strict
       (State,  get, modify, put, gets, (>=>))
import Ops (Noop(..), Add(..))


--The types of arity an operation can have

data Arity
  = Unary
  | Binary
  | Nil
  | SymmetricBinary
  | IndexedUnary
  | FxPoint


data DualExp (ar:: Arity) a where
  UExp:: UCons a -> DualExp 'Unary a
  SBExp :: BCons a -> DualExp 'SymmetricBinary a
  BExp:: BCons a -> BCons a -> DualExp ar a

-- the tape at a binary operation will either have two expressions (one to each arugment of the op) or a single expression
type family OpArity op :: Arity -- Encodes the arity of the arguments of the op


-- type instance OpTapeArity op 
-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace op a where
  N :: op -> DualTrace op a
  U :: op -> TNode a -> UCons a -> DualTrace op a
  B :: op -> TNode a -> TNode a -> BCons a -> BCons a -> DualTrace op a
  IxU :: op -> TNode a -> [Int] -> UCons a -> DualTrace op a
  FxP :: op ->  FptNode a -> DualTrace op a

type TNode a = D a -- output of an op

type UCons a = (D a -> D a) -- expression for the dual component of an Unary operator

type BCons a = (D a -> D a -> D a)  -- expression for the dual component of a Binary operator

type FptNode a = (TNode a, TNode a, TNode a, TNode a) -- nodes needed for a fixpoint evaluation

-- We're going to define duals as a type class because we need to keep track of their expressions in the tape
class Dual op a where
  dual :: op -> DualExp (OpArity op) a

newtype Tag = Tag Int
  deriving (Eq, Ord)

newtype UID = UID Int
  deriving (Eq, Ord)




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



  
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty 1e-6 1000



type Computation a = State (ComputationState a)

data D a where
  D :: a -> D a
  DF :: Primal a -> Tangent a -> Tag -> D a
  DR :: (Trace op a) => D a -> DualTrace op a -> Tag -> UID -> D a

type Primal a = D a
type Tangent a = D a



-- the accumulated adjoint at a given node in reverse-mode is aliased as a Delta
data Delta a
  = X (D a)
  | XNeg (D a)

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
  put (st & nextTag .~ (Tag (t + 1)))
  return tg
  
getNextUID :: Computation a (UID)
getNextUID = do
  st <- get
  let tg@(UID t) = st ^. nextUID
  put (st & nextUID .~ (UID (t + 1)))
  return tg


instance (Eq a) => Eq (D a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D a) where
  d1 `compare` d2 = pD d1 `compare` pD d2


class Unital a where -- Fixme:  figure out the numeric hierarchy we need.
  zero :: D a
  one :: D a

instance Unital Float where
  zero = D 0.0
  one = D 1.0

instance Unital Double where
  zero = D 0.0
  one = D 1.0

-- Integers are not differentiable


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

-- Get Tangent 
t :: (Unital a) => D a -> Tangent a
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
  ff :: op -> a -> a
  fd :: op -> D a -> D a
  df :: op -> D a -> D a -> D a -> D a

monOp' :: (Trace op a) =>
     op
  -> D a
  -> (a -> a)
  -> (D a -> D a)
  -> (D a -> D a -> D a -> D a)
  -> (D a -> DualTrace op a)
  -> Computation a (D a)
monOp' _ a ff fd df r_ =
  case a of
    D ap -> return . D $ ff ap
    DF ap at ai ->
      let cp = fd ap
      in return $ DF cp (df cp ap at) ai
    DR ap _ ai _ ->
      let cp = fd ap
      in r cp (r_ a) ai


duelExpMon :: (Dual op a, OpArity op ~ 'Unary) => op -> D a -> DualTrace op a
duelExpMon op a =
  case dual op of
    UExp exp -> U op a exp

    
monOp :: (MonOp op a, OpArity op ~ 'Unary, Dual op a, (Trace op a)) => op -> D a -> Computation a (D a)
monOp op a =
  let r_d = duelExpMon op
  in monOp' op a (ff op) (fd op) (df op) r_d


binOp' ::
     (Trace op a, Computation a ~ m)
  => op
  -> (D a)
  -> (D a)
  -> (a -> a -> a)
  -> (D a -> D a -> D a)
  -> (D a -> D a -> D a -> D a)
  -> (D a -> D a -> D a -> D a)
  -> (D a -> D a -> D a -> D a -> D a -> D a)
  -> (D a -> D a -> DualTrace op a)
  -> (D a -> D a -> DualTrace op a)
  -> (D a -> D a -> DualTrace op a)
  -> m (D a)
binOp' _ a b ff fd df_da df_db df_dab r_d_d r_d_c r_c_d = do
  case a of
    D ap ->
      case b of
        D bp -> return . D $ ff ap bp
        DF bp bt bi ->
          let cp = fd a bp
          in return $ DF cp (df_db cp bp bt) bi
        DR bp _ bi _ -> r (fd a bp) (r_c_d a b) bi
    DF ap at ai ->
      case b of
        D _ ->
          let cp = fd ap b
          in return $ DF cp (df_da cp ap at) ai
        DF bp bt bi ->
          case compare ai bi of
            EQ ->
              let cp = fd ap bp
              in return $ DF cp (df_dab cp ap at bp bt) ai
            LT ->
              let cp = fd a bp
              in return $ DF cp (df_db cp bp bt) bi
            GT ->
              let cp = fd ap b
              in return $ DF cp (df_da cp ap at) ai
        DR bp _ bi _ ->
          case compare ai bi of
            LT -> r (fd a bp) (r_c_d a b) bi
            GT ->
              let cp = fd ap b
              in return $ DF cp (df_da cp ap at) ai
            EQ -> error "Forward and reverse AD cannot run on the same level."
    DR ap _ ai _ ->
      case b of
        D _ -> r (fd ap b) (r_d_c a b) ai
        DF bp bt bi ->
          case compare ai bi of
            EQ -> error "Forward and reverse AD cannot run on the same level."
            LT ->
              let cp = fd a bp
              in return $ DF cp (df_db cp bp bt) bi
            GT -> r (fd ap b) (r_d_c a b) ai
        DR bp _ bi _ ->
          case compare ai bi of
            EQ -> r (fd ap bp) (r_d_d a b) ai
            LT -> r (fd a bp) (r_c_d a b) bi
            GT -> r (fd ap b) (r_d_c a b) ai
-- Creates the expressions for the dual components of the op

{-# INLINE duelExpBin #-}

duelExpBin ::
     (Dual op a)
  => op
  -> D a
  -> D a
  -> DualTrace op a
duelExpBin op a b =
  case dual op of
    SBExp ex -> B op a b ex ex -- if the expression in the same in each arguemnt
    BExp lexp rexp ->  B op a b lexp rexp -- if the expression differes for each arguemnt
    _ -> error "2-ary operations must have 2-ary duel expressions!"



binOp :: ( BinOp op a, Dual op a, (Trace op a), Computation a ~ m)
  =>
  op
  ->  (D a)
  ->  (D a)
  -> m (D a)
binOp op a b =
  let traceOp = duelExpBin op
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
  fd_bin :: (Computation a ~ m) => op ->  (D a) -> (D a) ->  (D a)
  df_db :: (Computation a ~ m) => op -> (D a) -> (D a) -> (D a) -> (D a) ->  (D a)
  df_da :: (Computation a ~ m) => op -> (D a) -> (D a) -> (D a) -> (D a) ->  (D a)
  df_dab ::
       (Computation a ~ m)
    => op
    -> (D a)
    -> (D a)
    -> (D a)
    -> (D a)
    -> (D a)
    -> (D a)

eval :: (Num a, Dual Add a, Num (D a), Unital a ) => Delta a -> D a
eval dl =
  case dl of
    X v -> v
    XNeg v -> zero - v
            
applyDelta :: (Num a, Dual Add a, Num (D a), Unital a) => UID -> Delta a -> Adjoints a -> (Maybe (D a), Adjoints a)
applyDelta tag dlta =
  M.updateLookupWithKey (\k v -> Just $ v + eval dlta) tag

decrementFanout :: UID -> Fanouts -> (Maybe Tag, Fanouts)
decrementFanout =
  M.updateLookupWithKey (\k (Tag v) -> Just . Tag $ v - 1)  
  
-- updateStack ls = modify (\ st -> st & stack %~ mappend ls)
  
incrementFanout :: UID -> Computation a Tag
incrementFanout u = do
  st <- get
  let (mf, a) =
        M.updateLookupWithKey (\_ (Tag f) -> Just . Tag $ f + 1) u (st ^. fanouts)
  
  (case mf of
      Nothing -> do
        put (st & fanouts %~ M.insert u (Tag 1))
        return $ Tag 1
      Just f -> do
        put (st & fanouts %~ const a)
        return f)
  

reset :: (Unital a) =>  [D a] -> Computation a ()
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
push :: (Num a, Dual Add a, Num (D a), Unital a) => [(Delta a, D a)] -> Computation a ()
push l =
  case l of
    [] -> return ()
    ((dl, da):xs) ->
      case da of
        DR _ o _ uniq -> do
          st <- get
          let (mv, a) = applyDelta uniq dl $ st ^. adjoints -- verify this
          case mv of
            Just dA -> do
              let nst1 = st & adjoints .~ a
              let (Just fn, aa) = decrementFanout uniq (nst1 ^. fanouts)
              put (st & fanouts .~ aa)
              if fn == Tag 0 then
                do
                  pd <- pushEl o dA
                  push $ pd `mappend` xs
                else push xs
            Nothing -> error "key not found in adjoints!"
        _ -> push xs

reverseReset :: (Unital a) => D a -> Computation a ()
reverseReset d = do
  modify (\st -> st & fanouts .~ M.empty )
  reset [d]

reverseProp :: (Num a, Dual Add a, Num (D a), Unital a) =>  D a -> D a -> Computation a ()
reverseProp  v d = do
  reverseReset  d
  push [(X v, d)]

{-# INLINE primalTanget #-}
primalTanget ::(Unital a) => D a -> (D a, Tangent a)
primalTanget d = (p d, t d)

adjoint :: (Unital a) => D a -> Computation a (D a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> return zero
    

{-# INLINE computeAdjoints' #-}
computeAdjoints' :: (Dual Add a, Num (D a), Num a, Unital a) => D a -> Computation a ()
computeAdjoints' d = do
  modify (\st -> st & adjoints .~ M.empty)
  reverseProp one d
  
{-# INLINE computeAdjoints #-}
computeAdjoints ::
     (Dual Add a, Num (D a), Num a, Unital a) => D a -> Computation a (Adjoints a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' ::(Unital a) => (D a -> D a) -> D a -> Computation a (D a, Tangent a)
diff' f x = do
  n <- getNextTag
  return . primalTanget . f $ mkForward n one x
{-# INLINE diff #-}

diff ::(Unital a) => (D a -> D a) -> D a -> Computation a (Tangent a)
diff f x = 
  snd <$> diff' f x
  
{-# INLINE diffn #-}
diffn :: (Unital a) => Int -> (D a -> D a) -> D a -> Computation a (Tangent a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then return $ f x
           else go n f x
  where
    go ::(Unital a) => Int -> (D a -> D a) -> D a -> Computation a (Tangent a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n - 1) f >=> diff f

{-# INLINE diffn' #-}
diffn'
  :: (Unital a) => Int -> (D a -> D a) -> D a -> Computation a (D a, (Tangent a))
diffn' n f x = do
  it <- return $ f x
  again <- diffn n f x
  return (it, again)
  
{-# INLINE grad' #-}
grad' ::
     (Trace Noop a, Dual Add a, Num (D a), Num a, Unital a)
  => (D a -> (D a))
  -> D a
  -> Computation a (D a, (D a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  let z = f xa
  computeAdjoints' z
  adj <- adjoint xa
  return (p xa, adj)
  
{-# INLINE grad #-}
grad ::
     (Num (D a), Num a, Dual Add a, Trace Noop a, Unital a)
  => (D a -> (D a))
  -> D a
  -> Computation a (D a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: (Unital a) =>
     (D a -> D a) -> Tangent a -> Primal a -> Computation a (D a, Tangent a)
jacobian' f x v = do
  ntg <- getNextTag
  return . primalTanget . f $ mkForward ntg v x

jacobian :: (Unital a) => (D a -> D a) -> Tangent a -> Primal a -> Computation a (Tangent a)
jacobian f x v = snd <$> jacobian' f x v
