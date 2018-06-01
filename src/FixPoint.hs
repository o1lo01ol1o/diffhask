{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
module FixPoint (module FixPoint) where
import           Control.Monad.State.Strict (State, get, gets, join, liftM,
                                             liftM2, modify, put, (>=>))
import           Core
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Internal.NumHask.Prelude            hiding (State, diff, evalState,
                                             runState)
import qualified NumHask.Prelude  as P
import Internal.Internal

data FixPoint = FixPoint deriving Show

fpPush ::
     ( Ord a
     , Show a
     , AdditiveUnital (D c r a) a
     , MultiplicativeUnital (D c r a) a
     , Additive (D c r a) (D c r a) a
     , AdditiveModule r (D c r a) (D c r a) a
     , AdditiveBasis r (D c r a) (D c r a) a
     , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) a
     )
  => D c r a
  -> D c r a
  -> D c r a
  -> D c r a
  -> D c r a
  -> Computation r a [(D c r a, D c r a)]
fpPush b bfirst aprev alast dA = do
  reverseProp dA alast
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  go mxitr (D eps) 0 alast aprev dA
  adjBf <- adjoint bfirst
  pure [(adjBf, b)]
  where
    go ::
         ( Ord a
         , Show a
         , AdditiveUnital (D c r a) a
         , MultiplicativeUnital (D c r a) a
         , Additive (D c r a) (D c r a) a
         , AdditiveModule r (D c r a) (D c r a) a
         , AdditiveBasis r (D c r a) (D c r a) a
         , Signed (D c r a) a
         , AdditiveGroup (D c r a) (D c r a) a
         )
      => Int
      -> D c r a
      -> Int
      -> D c r a
      -> D c r a
      -> D c r a
      -> Computation r a ()
    go miter eps oi apr alst d =
      let i = oi P.+ 1
      in if i P.>= miter
           then pure ()
           else do
             adjP <- adjoint apr
             adjL <- adjoint alst
             dmadjL <- d - adjL
             s <- adjP + dmadjL
             as <- abs s
             if as P.<= eps
               then pure ()
               else do
                 dadjP <- d + adjP
                 reverseProp (dadjP) adjL

instance ( Ord a
         , Show a
         , AdditiveUnital (D c r a) a
         , MultiplicativeUnital (D c r a) a
         , Additive (D c r a) (D c r a) a
         , AdditiveModule r (D c r a) (D c r a) a
         , AdditiveBasis r (D c r a) (D c r a) a
         , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) a
         ) =>
         Trace FixPoint r a where
  pushEl (FxP _ (b, bfirst, aprev, alast)) = fpPush b bfirst aprev alast
  resetEl (FxP _ (b, bf, ap, al)) = pure [b]

fixPoint ::
     (Ord a, Trace Noop r a, Show a
     , AdditiveUnital (D c r a) a
     , MultiplicativeUnital (D c r a) a
     , Additive (D c r a) (D c r a) a
     , AdditiveModule r (D c r a) (D c r a) a
     , AdditiveBasis r (D c r a) (D c r a) a
     , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) a
     , AdditiveGroup (D c r a) (Computation r a  (D c r a)) r a)
  => (D c r a -> D c r a -> Computation r a (D c r a))
  -> D c r a
  -> D c r a
  -> Computation r a (D c r a)
fixPoint g a0 b = do
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  case b of
    D _          -> goD g (D eps) mxitr 1 a0 b
    Dm _         -> goD g (D eps) mxitr 1 a0 b
    DF _ _ bi    -> goDF g (D eps) mxitr 1 a0 b bi
    DR bp _ bi _ -> goDR g (D eps) mxitr 1 a0 b bi bp
  where
    goD ::
         (Ord a, Show a
     , AdditiveUnital (D c r a) a
     , MultiplicativeUnital (D c r a) a
     , Additive (D c r a) (D c r a) a
     , AdditiveModule r (D c r a) (D c r a) a
     , AdditiveBasis r (D c r a) (D c r a) a
     , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) r a)
      => (D c r a -> D c r a -> Computation r a (D c r a))
      -> D c r a
      -> Int
      -> Int
      -> D c r a
      -> D c r a
      -> Computation r a (D c r a)
    goD g e m i a b =
      let ni = i P.+ 1
      in if ni P.>= m
           then pure a
           else do
             aa <- g a b
             d <- aa - a
             ad <- abs d
             if ad P.<= e
               then pure a
               else goD g e m ni aa b
    goDF ::
         (Ord a, Show a
     , AdditiveUnital (D c r a) a
     , MultiplicativeUnital (D c r a) a
     , Additive (D c r a) (D c r a) a
     , AdditiveModule r (D c r a) (D c r a) a
     , AdditiveBasis r (D c r a) (D c r a) a
     , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) a
     , AdditiveGroup (D c r a) (Computation r a  (D c r a)) r a)
      => (D c r a -> D c r a -> Computation r a (D c r a))
      -> D c r a
      -> Int
      -> Int
      -> D c r a
      -> D c r a
      -> Tag
      -> Computation r a (D c r a)
    goDF g e m i a b bi =
      let ni = i P.+ 1
      in if ni P.>= m
           then do
             cta <- t a
             pure P.$ DF (p a) (cta) bi
           else do
             aa <- g a b
             ps <- (p aa) - (p a)
             arg <- abs (ps)
             cta <- t aa
             td <- cta - t a
             if (arg P.<= e) P.&& (td P.<= e)
               then do
                 cta <- t a
                 pure P.$ DF (p a) (cta) bi
               else goDF g e m ni aa b bi
    drFin ::
         (Trace Noop r a, Ord a, Show a
     , AdditiveUnital (D c r a) a
     , MultiplicativeUnital (D c r a) a
     , Additive (D c r a) (D c r a) a
     , AdditiveModule r (D c r a) (D c r a) a
     , AdditiveBasis r (D c r a) (D c r a) a
     , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) r a)
      => (D c r a -> D c r a -> Computation r a (D c r a))
      -> D c r a
      -> Tag
      -> D c r a
      -> D c r a
      -> Computation r a (D c r a)
    drFin g a bi bfirst b = do
      aprev <- r (p a) (N Noop) bi
      alast <- g aprev bfirst
      r (p a) (FxP FixPoint (b, bfirst, aprev, alast)) bi
    goDR ::
         (Ord a, Trace Noop r a, Show a
     , AdditiveUnital (D c r a) a
     , MultiplicativeUnital (D c r a) a
     , Additive (D c r a) (D c r a) a
     , AdditiveModule r (D c r a) (D c r a) a
     , AdditiveBasis r (D c r a) (D c r a) a
     , Signed (D c r a) a
     , AdditiveGroup (D c r a) (D c r a) r a)
      => (D c r a -> D c r a -> Computation r a (D c r a))
      -> D c r a
      -> Int
      -> Int
      -> D c r a
      -> D c r a
      -> Tag
      -> D c r a
      -> Computation r a (D c r a)
    goDR g e m i a b bi bfirst =
      let ni = i P.+ 1
      in if ni P.>= m
           then drFin g a bi bfirst b
           else do
             aa <- g a b
             d <- aa - a
             ad <- abs d
             if ad P.<= e
               then drFin g a bi bfirst b
               else goDR g e m ni aa b bi bfirst
