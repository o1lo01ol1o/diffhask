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

type AdditiveDifferentiable t
  = ( --AdditiveUnital (D t) t
     --, AdditiveUnital (Computation t (D t)) t

     --,
     AdditiveMagma (D t) (D t) t
     , AdditiveMagma (Computation t (D t)) (D t) t
     , AdditiveMagma (Computation t (D t)) (Computation t (D t)) t
     , AdditiveMagma (D t) (Computation t (D t)) t

     , AdditiveAssociative (D t) t
     , AdditiveAssociative (Computation t (D t)) t

     , AdditiveCommutative (D t)  t
     , AdditiveCommutative (Computation t (D t))  t

     , AdditiveInvertible (D t) t
     , AdditiveInvertible (Computation t (D t)) t

     , AdditiveIdempotent (D t) (D t) t
     , AdditiveIdempotent (Computation t (D t)) (D t) t
     , AdditiveIdempotent (Computation t (D t)) (Computation t (D t)) t
     , AdditiveIdempotent (D t) (Computation t (D t)) t

     , Additive (D t) (D t) t
     , Additive (Computation t (D t)) (D t) t
     , Additive (Computation t (D t)) (Computation t (D t)) t
     , Additive (D t) (Computation t (D t)) t

     , AdditiveLeftCancellative (D t) (D t) t
     , AdditiveLeftCancellative (Computation t (D t)) (D t) t
     , AdditiveLeftCancellative (Computation t (D t)) (Computation t (D t)) t
     , AdditiveLeftCancellative (D t) (Computation t (D t)) t

     , AdditiveGroup (D t) (D t) t
     , AdditiveGroup (Computation t (D t)) (D t) t
     , AdditiveGroup (Computation t (D t)) (Computation t (D t)) t
     , AdditiveGroup (D t) (Computation t (D t)) t
     )

type MultiplicativeDifferential t
  = (MultiplicativeMagma (D t) (D t) t
     , MultiplicativeMagma (Computation t (D t)) (D t) t
     , MultiplicativeMagma (Computation t (D t)) (Computation t (D t)) t
     , MultiplicativeMagma (D t) (Computation t (D t)) t

     , MultiplicativeUnital (D t) t
     , MultiplicativeUnital (Computation t (D t)) t

     , MultiplicativeAssociative (D t) t
     , MultiplicativeAssociative (Computation t (D t)) t

     , MultiplicativeCommutative (D t) t
     , MultiplicativeCommutative (Computation t (D t)) t

     , MultiplicativeInvertible (D t) t
     , MultiplicativeInvertible (Computation t (D t)) t

     , Multiplicative (D t) (D t) t
     , Multiplicative (Computation t (D t)) (D t) t
     , Multiplicative (Computation t (D t)) (Computation t (D t)) t
     , Multiplicative (D t) (Computation t (D t)) t

     , MultiplicativeLeftCancellative (D t) (D t) t
     , MultiplicativeLeftCancellative (Computation t (D t)) (D t) t
     , MultiplicativeLeftCancellative (Computation t (D t)) (Computation t (D t)) t
     , MultiplicativeLeftCancellative (D t) (Computation t (D t)) t

     , MultiplicativeRightCancellative (D t) (D t) t
     , MultiplicativeRightCancellative (Computation t (D t)) (D t) t
     , MultiplicativeRightCancellative (Computation t (D t)) (Computation t (D t)) t
     , MultiplicativeRightCancellative (D t) (Computation t (D t)) t

     , MultiplicativeGroup (D t) (D t) t
     , MultiplicativeGroup (Computation t (D t)) (D t) t
     , MultiplicativeGroup (Computation t (D t)) (Computation t (D t)) t
     , MultiplicativeGroup (D t) (Computation t (D t)) t)

type Differentiable t
   = ( MultiplicativeDifferential t
     , AdditiveDifferentiable t
     , Distribution (D t) (D t) t
     , Distribution (Computation t (D t)) (D t) t
     , Distribution (Computation t (D t)) (Computation t (D t)) t
     , Distribution (D t) (Computation t (D t)) t

     , Semifield (D t) (D t) t
     , Semifield (Computation t (D t)) (D t) t
     , Semifield (Computation t (D t)) (Computation t (D t)) t
     , Semifield (D t) (Computation t (D t)) t

     , Field (D t) (D t) t
     , Field (Computation t (D t)) (D t) t
     , Field (Computation t (D t)) (Computation t (D t)) t
     , Field (D t) (Computation t (D t)) t

     , ExpField (D t) t
     , ExpField (Computation t (D t)) t

     , BoundedField (D t) t
     , BoundedField (Computation t (D t)) t

     , TrigField (D t) t
     , TrigField (Computation t (D t)) t

     , Signed (D t) t
     , Signed (Computation t (D t)) t

     , Normed (D t) t
     , Normed (Computation t (D t)) t

     , Metric (D t) (D t) t
     , Metric (Computation t (D t)) (D t) t
     , Metric (Computation t (D t)) (Computation t (D t)) t
     , Metric (D t) (Computation t (D t)) t

     , Epsilon (D t) (D t) t
     , Epsilon (Computation t (D t)) (D t) t
     , Epsilon (Computation t (D t)) (Computation t (D t)) t
     , Epsilon (D t) (Computation t (D t)) t

     , Ring (D t) (D t) t
     , Ring (Computation t (D t)) (D t) t
     , Ring (Computation t (D t)) (Computation t (D t)) t
     , Ring (D t) (Computation t (D t)) t

     , CRing (D t) (D t) t
     , CRing (Computation t (D t)) (D t) t
     , CRing (Computation t (D t)) (Computation t (D t)) t
     , CRing (D t) (Computation t (D t)) t

     , StarSemiring (D t) t
     , StarSemiring (Computation t (D t)) t

     , KleeneAlgebra (D t) (D t) t
     , KleeneAlgebra (Computation t (D t)) (D t) t
     , KleeneAlgebra (Computation t (D t)) (Computation t (D t)) t
     , KleeneAlgebra (D t) (Computation t (D t)) t

     )



-- Get Tangent
t :: forall a. (Differentiable a) => D a -> Computation a (Tangent a)
t =
  \case
    D _ -> pure (zero :: D a)
    DF _ at _ -> pure at
    DR {} -> error "Can't get tangent of a reverse node"


initComp :: (P.RealFrac a, Differentiable a)=> ComputationState a
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty (1e-6) 1000


mkForward :: (Differentiable a) => Tag -> Tangent a -> Primal a  -> D a
mkForward i tg d  = DF d tg i


mkReverse :: (Differentiable a, Trace Noop a) => Tag -> D a -> Computation a (D a)
mkReverse i d = r d (N Noop) i

instance Trace Noop a where
  pushEl _ _ = pure []
  resetEl _ = pure []

addDeltas :: (ModuleTypes a b ~ t) => Box a -> Box b -> Computation t (Box (AddModules a b))
addDeltas a b =
  case (a, b) of
    (X xa, X xb) -> fmap X (boxAdd xa xb)
    (M ma, X xb) -> fmap M (boxModuleAddL ma xb)
    (X xa, M mb) -> fmap M (boxModuleAddR xa mb)
    (M ma, M mb) -> fmap M (boxBasisAdd ma mb)

applyDelta :: (Differentiable a) => UID
  -> Box a
  -> Adjoints a
  -> Maybe (Computation a (D a))
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


reset :: forall a. (Differentiable a, Show a) => [Box a] -> Computation a ()
reset l =
  case l of
    [] -> return ()
    (da:xs) ->
      case da of
        DR _ o _ uniq -> do
          fanout <- incrementFanout uniq
          if fanout == Tag 1 then
            do
              modify (\st -> st & adjoints %~ M.insert uniq  (X (zero :: D a)))
              x <- resetEl o
              reset $ x `mappend` xs -- verify this
            else reset xs
          reset xs
        _ -> reset xs

-- recursively pushes nodes onto the reverse mode stack and evaluates partials
push :: (Differentiable a) => [(Box a, Box a)] -> Computation a ()
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

reverseReset :: (Differentiable a, Show a) => Box a -> Computation a ()
reverseReset d = do
  modify (& fanouts .~ M.empty )
  reset [ d]

reverseProp :: ( Differentiable a, Show a) => Box a -> Box a -> Computation a ()
reverseProp  v d = do
  reverseReset  d
  push [( v,  d)]

{-# INLINE primalTanget #-}
primalTanget :: (Differentiable a, Show a) => D a -> Computation a (D a, Tangent a)
primalTanget d = do
  ct <- t d
  pure (p d, ct)

adjoint :: forall a. (Differentiable a, Show a) =>  D a -> Computation a (Box a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a  -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> pure (zero :: D a)


runComputation :: (Differentiable a) => State s a -> s -> (a, s)
runComputation = runState

compute :: (P.RealFrac a, Differentiable a) => Computation a (b) -> b
compute f = evalState f initComp

{-# INLINE computeAdjoints' #-}
computeAdjoints' :: forall a. (Differentiable a, Show a) => D a -> Computation a ()
computeAdjoints' d = do
  modify (\st -> st & adjoints .~ M.empty)
  o <- pure (one :: D a)
  reverseProp o d

{-# INLINE computeAdjoints #-}
computeAdjoints :: (Differentiable a, Show a) => D a -> Computation a (Adjoints a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' :: forall a.
     (Differentiable a, Show a)
  => (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, Tangent a)
diff' f x = do
  n <- getNextTag
  o <- pure (one :: D a)
  fout <- f $ mkForward n o x
  primalTanget fout
{-# INLINE diff #-}

diff ::
     (Differentiable a, Show a)
  => (D a -> Computation a (D a))
  -> D a
  -> Computation a (Tangent a)
diff f x =
  snd <$> diff' f x

{-# INLINE diffn #-}
diffn ::
     (Differentiable a, Show a)
  => Int
  -> (D a -> Computation a (D a))
  -> D a
  -> Computation a (Tangent a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go ::
         (Differentiable a, Show a)
      => Int
      -> (D a -> Computation a (D a))
      -> D a
      -> Computation a (Tangent a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn' ::
     (Differentiable a, Show a)
  => Int
  -> (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, (Tangent a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  return (it, again)

-- | Reverse Multiplication
-- >>> compute $ grad' (\x -> x * a) a
-- (D 9.0,D 1.0)
{-# INLINE grad' #-}
grad' ::
     (Trace Noop a, Differentiable a, Show a)
  => (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, (D a))
grad' f x = do
  ntg <- getNextTag
  xa <- mkReverse ntg x
  z <- f xa
  computeAdjoints' z
  adj <- adjoint z
  return (p z, adj)

{-# INLINE grad #-}
grad ::
     (Trace Noop a, Differentiable a, Show a) =>
   (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: (Differentiable a, Show a) =>
     (D a -> Computation a (D a)) -> Tangent a -> Primal a -> Computation a (D a, Tangent a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  primalTanget fout

jacobian ::
     (Show a, Differentiable a)
  => (D a -> Computation a (D a))
  -> Tangent a
  -> Primal a
  -> Computation a (Tangent a)
jacobian f x v = snd <$> jacobian' f x v
