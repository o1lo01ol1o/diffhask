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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Core
    ( module Core
    ) where

import           Control.Monad.State.Strict (State, evalState, get, gets,
                                             modify, put, runState, (>=>))
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Internal.Internal hiding (Differentiable(..))
import           Internal.NumHask.Prelude   hiding (State, diff, evalState,
                                             runState)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Prelude                    (error)
import qualified Protolude                  as P

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts
-- >>> :set -XNoImplicitPrelude
-- >>> let b = D 2 :: (D Float)
-- >>> let a = D 3 :: (D Float)

--FIXME: prune redundancy

type AdditiveDifferentiable t r
  = ( --AdditiveUnital (D r t) r t
     --, AdditiveUnital (Computation r t (D r t)) r t

     --,
     AdditiveMagma (D r t) (D r t) r t
     , AdditiveMagma (Computation r t (D r t)) (D r t) r t
     , AdditiveMagma (Computation r t (D r t)) (Computation r t (D r t)) r t
     , AdditiveMagma (D r t) (Computation r t (D r t)) r t

     , AdditiveAssociative (D r t) r t
     , AdditiveAssociative (Computation r t (D r t)) r t

     , AdditiveCommutative (D r t) r t
     , AdditiveCommutative (Computation r t (D r t)) r t

     , AdditiveInvertible (D r t) r t
     , AdditiveInvertible (Computation r t (D r t)) r t

     , AdditiveIdempotent (D r t) (D r t) r t
     , AdditiveIdempotent (Computation r t (D r t)) (D r t) r t
     , AdditiveIdempotent (Computation r t (D r t)) (Computation r t (D r t)) r t
     , AdditiveIdempotent (D r t) (Computation r t (D r t)) r t

     , Additive (D r t) (D r t) r t
     , Additive (Computation r t (D r t)) (D r t) r t
     , Additive (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Additive (D r t) (Computation r t (D r t)) r t

     , AdditiveLeftCancellative (D r t) (D r t) r t
     , AdditiveLeftCancellative (Computation r t (D r t)) (D r t) r t
     , AdditiveLeftCancellative (Computation r t (D r t)) (Computation r t (D r t)) r t
     , AdditiveLeftCancellative (D r t) (Computation r t (D r t)) r t

     , AdditiveGroup (D r t) (D r t) r t
     , AdditiveGroup (Computation r t (D r t)) (D r t) r t
     , AdditiveGroup (Computation r t (D r t)) (Computation r t (D r t)) r t
     , AdditiveGroup (D r t) (Computation r t (D r t)) r t
     )

type MultiplicativeDifferential t r
  = (MultiplicativeMagma (D r t) (D r t) r t
     , MultiplicativeMagma (Computation r t (D r t)) (D r t) r t
     , MultiplicativeMagma (Computation r t (D r t)) (Computation r t (D r t)) r t
     , MultiplicativeMagma (D r t) (Computation r t (D r t)) r t

     , MultiplicativeUnital (D r t) r t
     , MultiplicativeUnital (Computation r t (D r t)) r t

     , MultiplicativeAssociative (D r t) r t
     , MultiplicativeAssociative (Computation r t (D r t)) r t

     , MultiplicativeCommutative (D r t) r t
     , MultiplicativeCommutative (Computation r t (D r t)) r t

     , MultiplicativeInvertible (D r t) r t
     , MultiplicativeInvertible (Computation r t (D r t)) r t

     , Multiplicative (D r t) (D r t) r t
     , Multiplicative (Computation r t (D r t)) (D r t) r t
     , Multiplicative (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Multiplicative (D r t) (Computation r t (D r t)) r t

     , MultiplicativeLeftCancellative (D r t) (D r t) r t
     , MultiplicativeLeftCancellative (Computation r t (D r t)) (D r t) r t
     , MultiplicativeLeftCancellative (Computation r t (D r t)) (Computation r t (D r t)) r t
     , MultiplicativeLeftCancellative (D r t) (Computation r t (D r t)) r t

     , MultiplicativeRightCancellative (D r t) (D r t) r t
     , MultiplicativeRightCancellative (Computation r t (D r t)) (D r t) r t
     , MultiplicativeRightCancellative (Computation r t (D r t)) (Computation r t (D r t)) r t
     , MultiplicativeRightCancellative (D r t) (Computation r t (D r t)) r t

     , MultiplicativeGroup (D r t) (D r t) r t
     , MultiplicativeGroup (Computation r t (D r t)) (D r t) r t
     , MultiplicativeGroup (Computation r t (D r t)) (Computation r t (D r t)) r t
     , MultiplicativeGroup (D r t) (Computation r t (D r t)) r t)

type Differentiable t r
   = ( MultiplicativeDifferential t r
     , AdditiveDifferentiable t r
     , Distribution (D r t) (D r t) r t
     , Distribution (Computation r t (D r t)) (D r t) r t
     , Distribution (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Distribution (D r t) (Computation r t (D r t)) r t

     , Semifield (D r t) (D r t) r t
     , Semifield (Computation r t (D r t)) (D r t) r t
     , Semifield (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Semifield (D r t) (Computation r t (D r t)) r t

     , Field (D r t) (D r t) r t
     , Field (Computation r t (D r t)) (D r t) r t
     , Field (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Field (D r t) (Computation r t (D r t)) r t

     , ExpField (D r t) r t
     , ExpField (Computation r t (D r t)) r t

     , BoundedField (D r t) r t
     , BoundedField (Computation r t (D r t)) r t

     , TrigField (D r t) r t
     , TrigField (Computation r t (D r t)) r t

     , Signed (D r t) r t
     , Signed (Computation r t (D r t)) r t

     , Normed (D r t) r t
     , Normed (Computation r t (D r t)) r t

     , Metric (D r t) (D r t) r t
     , Metric (Computation r t (D r t)) (D r t) r t
     , Metric (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Metric (D r t) (Computation r t (D r t)) r t

     , Epsilon (D r t) (D r t) r t
     , Epsilon (Computation r t (D r t)) (D r t) r t
     , Epsilon (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Epsilon (D r t) (Computation r t (D r t)) r t

     , Ring (D r t) (D r t) r t
     , Ring (Computation r t (D r t)) (D r t) r t
     , Ring (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Ring (D r t) (Computation r t (D r t)) r t

     , CRing (D r t) (D r t) r t
     , CRing (Computation r t (D r t)) (D r t) r t
     , CRing (Computation r t (D r t)) (Computation r t (D r t)) r t
     , CRing (D r t) (Computation r t (D r t)) r t

     , StarSemiring (D r t) r t
     , StarSemiring (Computation r t (D r t)) r t

     , KleeneAlgebra (D r t) (D r t) r t
     , KleeneAlgebra (Computation r t (D r t)) (D r t) r t
     , KleeneAlgebra (Computation r t (D r t)) (Computation r t (D r t)) r t
     , KleeneAlgebra (D r t) (Computation r t (D r t)) r t

     )



-- Get Tangent
t :: forall a r. () => D r a -> Computation r a (Tangent r a)
t =
  \case
    D _ -> pure (zero :: D r a)
    DF _ at _ -> pure at
    DR {} -> error "Can't get tangent of a reverse node"


initComp :: (P.RealFrac a)=> ComputationState r a
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty (1e-6) 1000


mkForward :: () => Tag -> Tangent r a -> Primal r a  -> D r a
mkForward i tg d  = DF d tg i


mkReverse :: ( Trace Noop r a) => Tag -> D r a -> Computation r a (D r a)
mkReverse i d = r d (N Noop) i

instance Trace Noop r a where
  pushEl _ _ = pure []
  resetEl _ = pure []

addDeltas ::
     ( Additive (D r a) (D r a) r a
     , AdditiveModule r (D r a) (D r a) a
     , AdditiveBasis r (D r a) (D r a) a
     )
  => D r a
  -> D r a
  -> Computation r a (D r a)
addDeltas a b =
  case (a, b) of
    (D xa, D xb) -> a + b
    (Dm ma, D xb) -> a .+ b
    (D xa, Dm mb) -> a +. b
    (Dm ma, Dm mb) -> a .+. b

applyDelta :: () => UID
  -> D r a
  -> Adjoints r a
  -> Maybe (Computation r a (D r a))
applyDelta tag dlta adjs=
  case M.lookup tag adjs of
    Just v -> Just $ do
      e <- dlta
      r <- addDeltas v e
      modify (\st -> st & adjoints .~ M.update (const . Just  $ r) tag adjs)
      return r
    Nothing -> Nothing

decrementFanout :: UID -> Fanouts -> (Maybe Tag, Fanouts)
decrementFanout =
  M.updateLookupWithKey (\_ (Tag v) -> Just . Tag $ v P.- 1)

incrementFanout :: UID -> Computation r a Tag
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


reset :: ( Show a) => [D r a] -> Computation r a ()
reset l =
  case l of
    [] -> return ()
    (da:xs) ->
      case da of
        DR _ o _ uniq -> do
          fanout <- incrementFanout uniq
          if fanout == Tag 1 then
            do
              modify (\st -> st & adjoints %~ M.insert uniq  (X (zero :: D r a)))
              x <- resetEl o
              reset $ x `mappend` xs -- verify this
            else reset xs
          reset xs
        _ -> reset xs

-- recursively pushes nodes onto the reverse mode stack and evaluates partials
push :: () => [(D r a, D r a)] -> Computation r a ()
push l =
  case l of
    [] -> return ()
    ((dl, da):xs) ->
      case da of
        DR _ o _ uniq -> do
          st <- gets ( ^. adjoints )
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

reverseReset :: ( Show a) => D r a -> Computation r a ()
reverseReset d = do
  modify (& fanouts .~ M.empty )
  reset [ d]

reverseProp :: (  Show a) => D r a -> D r a -> Computation r a ()
reverseProp  v d = do
  reverseReset  d
  push [( v,  d)]

{-# INLINE primalTanget #-}
primalTanget :: ( Show a) => D r a -> Computation r a (D r a, Tangent r a)
primalTanget d = do
  ct <- t d
  pure (p d, ct)

adjoint :: forall a r. ( Show a) =>  D r a -> Computation r a (D r a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a  -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> pure (zero :: D r a)


runComputation :: () => State s a -> s -> (a, s)
runComputation = runState

compute :: (P.RealFrac a) => Computation r a (b) -> b
compute f = evalState f initComp

{-# INLINE computeAdjoints' #-}
computeAdjoints' :: forall a r. ( Show a) => D r a -> Computation r a ()
computeAdjoints' d = do
  modify (\st -> st & adjoints .~ M.empty)
  o <- pure (one :: D r a)
  reverseProp o d

{-# INLINE computeAdjoints #-}
computeAdjoints :: ( Show a) => D r a -> Computation r a (Adjoints r a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' :: forall a r.
     ( Show a)
  => (D r a -> Computation r a (D r a))
  -> D r a
  -> Computation r a (D r a, Tangent r a)
diff' f x = do
  n <- getNextTag
  o <- pure (one :: D r a)
  fout <- f $ mkForward n o x
  primalTanget fout
{-# INLINE diff #-}

diff ::
     ( Show a)
  => (D r a -> Computation r a (D r a))
  -> D r a
  -> Computation r a (Tangent r a)
diff f x =
  snd <$> diff' f x

{-# INLINE diffn #-}
diffn ::
     ( Show a)
  => Int
  -> (D r a -> Computation r a (D r a))
  -> D r a
  -> Computation r a (Tangent r a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go ::
         ( Show a)
      => Int
      -> (D r a -> Computation r a (D r a))
      -> D r a
      -> Computation r a (Tangent r a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn' ::
     ( Show a)
  => Int
  -> (D r a -> Computation r a (D r a))
  -> D r a
  -> Computation r a (D r a, (Tangent r a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  return (it, again)

-- | Reverse Multiplication
-- >>> compute $ grad' (\x -> x * a) a
-- (D 9.0,D 1.0)
{-# INLINE grad' #-}
grad' ::
     (Trace Noop r a,  Show a)
  => (D r a -> Computation r a (D r a))
  -> D r a
  -> Computation r a (D r a, (D r a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  z <- f xa
  computeAdjoints' z
  adj <- adjoint z
  return (p z, adj)

{-# INLINE grad #-}
grad ::
     (Trace Noop r a,  Show a) =>
   (D r a -> Computation r a (D r a))
  -> D r a
  -> Computation r a (D r a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: ( Show a) =>
     (D r a -> Computation r a (D r a)) -> Tangent r a -> Primal r a -> Computation r a (D r a, Tangent r a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  primalTanget fout

jacobian ::
     (Show a)
  => (D r a -> Computation r a (D r a))
  -> Tangent r a
  -> Primal r a
  -> Computation r a (Tangent r a)
jacobian f x v = snd <$> jacobian' f x v
