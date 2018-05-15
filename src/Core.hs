{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}


module Core
    ( module Core
    ) where

import           Control.Monad.State.Strict (State, StateT, evalState,
                                             evalStateT, get, gets, modify, put,
                                             runState, (>=>))
import           Data.Constraint
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Data.Unique
import           GHC.Err
import           GHC.Exts
import           Internal.Internal          hiding (Differentiable (..))
import           Internal.NumHask.Prelude   hiding (State, StateT, diff,
                                             evalState, evalStateT, runState)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import qualified Numeric.Dimensions         as Dim
import qualified Numeric.Dimensions.Dim     as Dim
import qualified NumHask.Array              as A
import qualified NumHask.Prelude            as P
import           Prelude                    (error)
import           Unsafe.Coerce              (unsafeCoerce)

zero :: (DArray s '[] a) => D s '[] a
zero = D P.zero
one ::(DArray s '[] a) => D s '[] a
one = D P.one


zeros :: (DArray s r a) => D s r a
zeros = fromList $ repeat P.zero

ones :: (DArray s r a) => D s r a
ones = fromList $ repeat P.one


initComp :: forall a r. (P.Fractional a) => ComputationState r a
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty (1e-6 :: a) (P.sum $ P.replicate 1000 1)


mkForward :: (DArray s r a) => Tag -> Tangent s r a -> Primal s r a  -> D s r a
mkForward i tg d  = DF d tg i


mkReverse :: ( Trace s Noop r a, P.Monad m) => Tag -> D s r a -> ComputationT s a m (D s r a)
mkReverse i d = r d (N Noop) i

instance (DArray s r a) => Trace s Noop  r a where
  pushAlg _ _ = pure []
  resetAlg _ = pure []

addDeltas' ::
     ( P.Monad m
     )
  => D s ar a
  -> D s br a
  -> ComputationT s a m (D s (BinCalcShape ar br) a)
addDeltas' a b =
  case (a, b) of
    (D xa :: D s ar a, D xb :: D s br a) -> a + b
    (Dm ma :: D s ar a, D xb :: D s br a) -> a .+ b
    (D xa :: D s ar a, Dm mb :: D s br a) -> a +. b
    (Dm ma :: D s ar a, Dm mb :: D s br a) ->
      case checkSame (Dim.dim @br) (Dim.dim @ar) of
        Just Dim.Evidence -> a .+. b
        Nothing ->
          GHC.Err.error
            "Dimensions of arguments to binOp should have been equal: Please report this as a bug in diffhask."
  where
    checkSame :: Dim.Dim ar -> Dim.Dim br -> Maybe (Dim.Evidence (ar ~ br))
    checkSame = Dim.sameDim
    checkTensorScalar :: Dim.Dim ar -> Dim.Dim br -> Ordering
    checkTensorScalar = Dim.compareDim
    checkScalarTensor = checkTensorScalar

handleAnyD ::  SomeD c a -> (forall r. DArray c r a => D c r a -> rv) -> rv
handleAnyD =
  \case
    SomeD v -> flip ($) v

unsafeAddDeltas ::
     (P.Monad m)
  => SomeD s a
  -> SomeD s a
  -> ComputationT s a m (D s r a)
unsafeAddDeltas sa sb =
  case (sa, sb) of
    (SomeD (a :: D s ar a), SomeD (b :: D s br a)) -> do
      r <- addDeltas' a b
      pure (unsafeCoerce r :: D s r a)

-- addDeltas ::
--      (P.Monad m, WrappedOperable s a)
--   => SomeD s a
--   -> SomeD s a
--   -> ComputationT s a m (SomeD s a)
-- addDeltas sa sb =
--   handleAnyD sa $ \ (ca :: D s ar a) ->
--   handleAnyD sb $ \ (cb :: D s br a) -> do
--      r <- addDeltas' ca cb
--      pure $ SomeD r

  -- case (sa, sb) of
  --   (SomeD (a :: D s ar a), SomeD (b :: D s br a)) -> do
  --     r <- addDeltas' a b
  --     pure $ SomeD r


applyDelta ::  (DArray s r a, P.Monad m) => UID
  ->  SomeD s a
  ->  (ComputationT s a m (D s r a))
applyDelta uniq dlta = do
  st <- get
  let adjs = st ^. adjoints
  case M.lookup uniq adjs of
    Just v  -> (addIt adjs v)
    Nothing -> error "key not found in adjoints!"
  where
    addIt adjs v = do
      r <- unsafeAddDeltas v dlta -- FIXME: It should be possible to return SomeD without the coercion but at present I can't make GHC happy.
      modify (& adjoints .~ M.update (const . Just . SomeD $ r) uniq adjs)
      pure r

decrementFanout :: UID -> Fanouts -> (Maybe Tag, Fanouts)
decrementFanout = M.updateLookupWithKey (\_ (Tag v) -> Just . Tag $ v P.- 1)

incrementFanout :: (P.Monad m) =>UID -> ComputationT s a m Tag
incrementFanout u = do
  st <- get
  let (mf, a) =
        M.updateLookupWithKey (\_ (Tag f) -> Just . Tag $ f P.+ 1) u (st ^. fanouts)

  (case mf of
      Nothing -> do
        put (st & fanouts %~ M.insert u (Tag 1))
        pure $ Tag 1
      Just f -> do
        put (st & fanouts %~ const a)
        pure f)

zeroAdj :: (WrappedOperable s a, P.Monad m) => UID -> ComputationT s a m ()
zeroAdj uniq =
  modify (& adjoints %~ M.insert uniq (SomeD zero))

reset ::
     (WrappedOperable s a, P.Monad m) => [SomeD s a] -> ComputationT s a m ()
reset l =
  case l of
    [] -> pure ()
    (da:xs) ->
      case da of
        (SomeD (DR _ o _ uniq)) -> do
          fanout <- incrementFanout uniq
          if fanout == Tag 1
            then do
              zeroAdj uniq
              x <- resetAlg o
              reset $ x `mappend` xs -- verify this
            else reset xs
          reset xs
        _ -> reset xs

applyAndPush :: forall s r a m op.
     ( DArray s r a
     , WrappedOperable s a
     , P.Monad m
     , Trace s op r a
     )
  => UID
  -> TraceStack s op r a
  -> SomeD s a
  -> [(SomeD s a, SomeD s a)]
  -> ComputationT s a m ()
applyAndPush uniq o dl xs = do
  let cdA = applyDelta uniq dl
  dA <- cdA
  getAndDec uniq o dA xs
getAndDec ::forall s r a m op.
     ( DArray s r a
     , WrappedOperable s a
     , P.Monad m
     , Trace s op r a
     )
  => UID
  -> TraceStack s op r a
  -> D s r a
  -> [(SomeD s a, SomeD s a)]
  -> ComputationT s a m ()
getAndDec uniq o dA xs = do
  nst1 <- get
  let (Just fn, aa) = decrementFanout uniq (nst1 ^. fanouts)
  put (nst1 & fanouts .~ aa)
  if fn == Tag 0
    then pushit o dA xs
    else push xs
pushit ::
     ( DArray s r a
     , WrappedOperable s a
     , P.Monad m
     , Trace s op r a
     )
  => TraceStack s op r a
  -> D s r a
  -> [(SomeD s a, SomeD s a)]
  -> ComputationT s a m ()
pushit o dA xs = do
  pd <- pushAlg o dA
  push $ pd `mappend` xs

-- recursively pushes nodes onto the reverse mode stack and composes partials at node
push :: (P.Monad m, WrappedOperable s a) => [(SomeD s a, SomeD s a)]
  -> ComputationT s a m ()
push l =
  case l of
    [] -> pure ()
    ((dl, da):xs) ->
      case da of
        (SomeD (DR _ o _ uniq)) ->
          handleAnyD da $ \(DR _ o _ uniq) -> applyAndPush uniq o dl xs
        _ -> push xs



reverseReset ::
     ( WrappedOperable s a
     , P.Monad m
     )
  => SomeD s a
  -> ComputationT s a m ()
reverseReset d = do
  modify (& fanouts .~ M.empty )
  reset [ d]

reverseProp ::
     ( WrappedOperable s a
     , P.Monad m
     )
  => SomeD s a
  -> SomeD s a
  -> ComputationT s a m ()
reverseProp  v d = do
  reverseReset  d
  push [(  v,  d)]

{-# INLINE primalTanget #-}
primalTanget :: (P.Monad m, P.AdditiveUnital a) =>
     D s r a
  -> ComputationT s a m (D s r a, Tangent s r a)
primalTanget d = do
  let ct = t d
  pure (p d, ct)

adjoint :: (DArray s r a, P.Monad m) =>
      D s r a
  -> ComputationT s a m (SomeD s a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a  -> pure a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> pure $ SomeD zero


runComputation :: () => State s a -> s -> (a, s)
runComputation = runState

computeT ::
     (Monad m, Fractional a1) => StateT (ComputationState r a1) m a2 -> m a2
computeT f = evalStateT f initComp

compute :: (Fractional a1) => StateT (ComputationState r a1) Identity a2 -> a2
compute f = runIdentity $ evalStateT f initComp

-- compute :: (P.RealFrac a) => ComputationT s a m (b) -> b
-- compute f = evalState f initComp

{-# INLINE computeAdjoints' #-}
computeAdjoints' ::
     forall s r a m.
     (DArray s r a, P.Monad m)
  => D s r a
  -> ComputationT s a m ()
computeAdjoints' d = do
  modify (& adjoints .~ M.empty)
  o <- pure (ones :: D s r a)
  reverseProp (SomeD o) (SomeD d)

{-# INLINE computeAdjoints #-}
computeAdjoints ::
     ( P.Monad m
     , DArray s r a

     )
  => D s r a
  -> ComputationT s a m (Adjoints s a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  pure $ st ^. adjoints
{-# INLINE diff' #-}

diff' ::
     (P.Monad m, DArray s r a)
  => (D s r a -> ComputationT s a m (D s r a))
  -> D s r a
  -> ComputationT s a m (D s r a, Tangent s r a)
diff' f x = do
  n <- getNextTag
  fout <- f $ mkForward n ones x
  primalTanget fout
{-# INLINE diff #-}

diff :: (P.Monad m, DArray s r a) =>
     (D s r a -> ComputationT s a m (D s r a))
  -> D s r a
  -> ComputationT s a m (Tangent s r a)
diff f x =
  snd <$> diff' f x

{-# INLINE diffn #-}
diffn :: (P.Monad m, DArray s r a) =>
     Int
  -> (D s r a -> ComputationT s a m (D s r a))
  -> D s r a
  -> ComputationT s a m (Tangent s r a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go :: (P.Monad m, DArray s r a) =>
        Int
      -> (D s r a -> ComputationT s a m (D s r a))
      -> D s r a
      -> ComputationT s a m (Tangent s r a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn' :: (P.Monad m, DArray s r a) =>
     Int
  -> (D s r a -> ComputationT s a m (D s r a))
  -> D s r a
  -> ComputationT s a m (D s r a, (Tangent s r a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  pure (it, again)

{-# INLINE grad' #-}
grad' :: (P.Monad m, DArray s r a) =>
     (D s r a -> ComputationT s a m (D s r a))
  -> D s r a
  -> ComputationT s a m (D s r a, (SomeD s a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  z <- f xa
  computeAdjoints' z
  adj <- adjoint z
  pure (p z, adj)

{-# INLINE grad #-}
grad :: (P.Monad m, DArray s r a) =>
      (D s r a -> ComputationT s a m (D s r a))
  -> D s r a
  -> ComputationT s a m (SomeD s a)
grad f x = do
  (_, g)<- grad' f x
  pure g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: (P.Monad m, DArray s r a) =>
     (D s r a -> ComputationT s a m (D s r a))
  -> Tangent s r a
  -> Primal s r a
  -> ComputationT s a m (D s r a, Tangent s r a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  primalTanget fout

jacobian :: (P.Monad m, DArray s r a) =>
      (D s r a -> ComputationT s a m (D s r a))
  -> Tangent s r a
  -> Primal s r a
  -> ComputationT s a m (Tangent s r a)
jacobian f x v = snd <$> jacobian' f x v


