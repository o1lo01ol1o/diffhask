{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Core
    ( module Core
    ) where

import           Control.Monad.State.Strict (State, evalState, get, gets,
                                             modify, put, runState, (>=>))
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Internal.Internal          hiding (Differentiable (..))
import           Internal.NumHask.Prelude   hiding (State, diff, evalState,
                                             runState)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Prelude                    (error)
import qualified NumHask.Prelude                  as P
import Data.Unique

zero :: (P.AdditiveUnital a, Show a) => D s r a
zero = D P.zero
one ::(P.MultiplicativeUnital a, Show a) => D s r a
one = D P.one

-- Get Tangent
t :: forall s r a.
  D s r a
  -> Computation s a (Tangent s r a)
t =
  \case
    D _ -> pure (zero :: (Tangent s r a))
    DF _ at _ -> pure (at :: (Tangent s r a))
    DR {} -> error "Can't get tangent of a reverse node"


initComp :: forall a r. (P.Fractional a) => ComputationState r a
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty (1e-6 :: a) (P.sum $ P.replicate 1000 1)


mkForward :: () => Tag -> Tangent s r a -> Primal s r a  -> D s r a
mkForward i tg d  = DF d tg i


mkReverse :: ( Trace s Noop r a) => Tag -> D s r a -> Computation s a (D s r a)
mkReverse i d = r d (N Noop) i

instance Trace s Noop  r a where
  pushAlg _ _ = pure []
  resetAlg _ = pure []

addDeltas :: 
     D s r a
  -> D s rr a
  -> Computation s a (D s rrr a)
addDeltas a b =
  case (a, b) of
    (D xa, D xb)   -> a .+. b
    (Dm ma, D xb)  -> a .+ b
    (D xa, Dm mb)  -> a +. b
    (Dm ma, Dm mb) -> a .+. b -- can I just just use binOp Add a b and define the instance to be on the correct combination of dimensions?

applyDelta :: UID
  -> D s r a
  -> Maybe (Computation s a (D s rr a))
applyDelta uniq dlta = do
  st <- get
  let adjs = st ^. adjoints
  case M.lookup uniq adjs of
    Just (SomeD v) -> Just $ do
      e <- dlta
      r <- addDeltas v e
      modify (& adjoints .~ M.update (const . Just . SomeD $ r) uniq adjs)
      return r
    Nothing -> Nothing
  -- st <- cGet
  -- let adjs = st ^. adjoints
  -- let km = st ^. uidKeyMap
  -- case M.lookup uniq km of
  --   Just (sk) ->
  --     case sk of
  --       (SomeKey (k :: HM.HKey s (D s rk a))) ->
  --         case HM.lookup k adjs of
  --           Just (v :: (D s rk a)) -> do
  --             (r ::  (D s rd a)) <- addDeltas v dlta
  --             nk <- HM.getKey
  --             lift $
  --               modify
  --                 (\st ->
  --                    st & adjoints .~ HM.update (const . Just $ r) nk adjs &
  --                    uidKeyMap %~
  --                    (M.insert uniq (SomeKey nk)))
  --             pure r
  --           _ -> error "Couldn't find HKey in adjoints!"
  --   _ -> error $ "Couldn't find HKey for id " ++ show uniq
 

decrementFanout :: UID -> Fanouts s a -> (Maybe Tag, Fanouts s a)
decrementFanout =
  M.updateLookupWithKey (\_ (Tag v) -> Just . Tag $ v P.- 1)

incrementFanout :: UID -> Computation s a Tag
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

zeroAdj :: -- forall r s a. (AdditiveUnital (D s r a) r a)
  -- =>
  UID
  -> Computation s a ()
zeroAdj uniq =
  modify (& adjoints %~ M.insert uniq (SomeD zero))

reset :: [D s r a] -> Computation s a ()
reset l =
  case l of
    [] -> return ()
    (da:xs) ->
      case da of
        DR _ o _ uniq -> do
          fanout <- incrementFanout uniq
          if fanout == Tag 1 then
            do
              zeroAdj uniq
              x <- resetAlg o
              reset $ x `mappend` xs -- verify this
            else reset xs
          reset xs
        _ -> reset xs

-- recursively pushes nodes onto the reverse mode stack and composes partials at node
push :: [(D s r a, D s r a)]
  -> Computation s a ()
push l =
  case l of
    [] -> return ()
    ((dl, da):xs) ->
      case da of
        DR _ o _ uniq -> do
          let mv = applyDelta uniq dl
          case mv of
            Just cdA -> do
              dA <- cdA
              nst1 <- get
              let (Just fn, aa) = decrementFanout uniq (nst1 ^. fanouts)
              put (nst1 & fanouts .~ aa)
              if fn == Tag 0 then
                do
                  pd <- pushAlg o dA
                  push $ pd `mappend` xs
                else push xs
            Nothing -> error "key not found in adjoints!"
        _ -> push xs

reverseReset ::
     D s r a
  -> Computation s a ()
reverseReset d = do
  modify (& fanouts .~ M.empty )
  reset [ d]

reverseProp ::
     D s r a
  -> D s r a
  -> Computation s a ()
reverseProp  v d = do
  reverseReset  d
  push [( v,  d)]

{-# INLINE primalTanget #-}
primalTanget ::
     D s r a
  -> Computation s a (D s r a, Tangent s r a)
primalTanget d = do
  ct <- t d
  pure (p d, ct)

adjoint :: 
      D s r a
  -> Computation s a (D s rr a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just (SomeD a)  -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> pure zero


runComputation :: () => State s a -> s -> (a, s)
runComputation = runState

compute :: (P.RealFrac a) => Computation s a (b) -> b
compute f = evalState f initComp

{-# INLINE computeAdjoints' #-}
computeAdjoints' ::
     D s r a
  -> Computation s a ()
computeAdjoints' d = do
  modify (& adjoints .~ M.empty)
  o <- pure (one :: D s r a)
  reverseProp o d

{-# INLINE computeAdjoints #-}
computeAdjoints ::
     D s r a
  -> Computation s a (Adjoints s a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' :: (D s r a -> Computation s a (D s r a))
  -> D s r a
  -> Computation s a (D s r a, Tangent s r a)
diff' f x = do
  n <- getNextTag
  o <- pure (one :: D s r a)
  fout <- f $ mkForward n o x
  primalTanget fout
{-# INLINE diff #-}

diff ::
     (D s r a -> Computation s a (D s r a))
  -> D s r a
  -> Computation s a (Tangent s r a)
diff f x =
  snd <$> diff' f x

{-# INLINE diffn #-}
diffn ::
     Int
  -> (D s r a -> Computation s a (D s r a))
  -> D s r a
  -> Computation s a (Tangent s r a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go ::
        Int
      -> (D s r a -> Computation s a (D s r a))
      -> D s r a
      -> Computation s a (Tangent s r a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn' ::
     Int
  -> (D s r a -> Computation s a (D s r a))
  -> D s r a
  -> Computation s a (D s r a, (Tangent s r a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  return (it, again)

{-# INLINE grad' #-}
grad' ::
     (D s r a -> Computation s a (D s r a))
  -> D s r a
  -> Computation s a (D s r a, (D s r a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  z <- f xa
  computeAdjoints' z
  adj <- adjoint z
  return (p z, adj)

{-# INLINE grad #-}
grad ::
      (D s r a -> Computation s a (D s r a))
  -> D s r a
  -> Computation s a (D s r a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' ::
     (D s r a -> Computation s a (D s r a))
  -> Tangent s r a
  -> Primal s r a
  -> Computation s a (D s r a, Tangent s r a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  primalTanget fout

jacobian ::
      (D s r a -> Computation s a (D s r a))
  -> Tangent s r a
  -> Primal s r a
  -> Computation s a (Tangent s r a)
jacobian f x v = snd <$> jacobian' f x v
