{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
module Num (module Num) where
import           Control.Monad.State.Strict (State, get, gets, modify, put,
                                             (>=>), join, liftM, liftM2)
import           Core
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import            Ops
import qualified Prelude as P
import Prelude (pure)

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts


instance (P.Num a, Core a) => BinOp Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.+  a
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a + b
  {-# INLINE df_da #-}
  df_da _ _ _ _ at =  pure at
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt = pure bt
  {-# INLINE df_dab #-}
  df_dab _ _ _ at _ bt =  at + bt

instance Trace Add a where
  pushEl (B _ a b) dA =
    pure [(X dA, a), (X dA, b), (X dA, a), (X dA, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

instance (P.Num a, Core a) => BinOp Subtract a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  a P.- b
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a - b
  {-# INLINE df_da #-}
  df_da _ _ _ _ at = pure at
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt = zero - bt
  {-# INLINE df_dab #-}
  df_dab _ _ _ at _ bt =  at - bt

instance Trace Subtract a where
  pushEl (B _ a b) dA =
    pure [(X dA, a), (XNeg dA, b), (X dA, a ), (XNeg dA,b )]
  resetEl (B _ a b) = pure [a, b, a, b]


instance (P.Num a, Core a) => MonOp Sign a where
  {-# INLINE ff #-}
  ff _ a = P.signum a
  {-# INLINE fd #-}
  fd _ a = signum a
  {-# INLINE df #-}
  df _ _ _ _ = pure zero


instance Trace Sign a where


instance (P.Num a, Core a) => MonOp Abs a where
  {-# INLINE ff #-}
  ff _ a = P.abs a
  {-# INLINE fd #-}
  fd _ a = abs a
  {-# INLINE df #-}
  df _ _ ap at = do
    sap <- signum ap
    at * sap

instance Trace Abs a where

  

instance (P.Num a, Core a) => BinOp Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.*  a
  {-# INLINE fd_bin #-}
  fd_bin _ a b = a * b
  {-# INLINE df_da #-}
  df_da _ b _ _ at = at * b
  {-# INLINE df_db #-}
  df_db _ a _ _ bt =  bt * a
  {-# INLINE df_dab #-}
  df_dab _ _ ap at bp bt =  do
    atbp <- at * bp
    apbt <- ap * bt
    atbp + apbt


instance (Core a) => Trace Multiply a where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA * p b
    opb <- cdA * p a
    arga <- cdA * b
    argb <- cdA * a
    pure [(X opa, a), (X opb, b), (X arga, a), (X argb, b)] --- rethink the dual expressions  . . .
  resetEl (B _ a b) = pure [a, b, a, b]

fpPush ::
     (P.Ord a, Core a)
  => D a
  -> D a
  -> D a
  -> D a
  -> D a
  -> Computation a [(Delta a, D a)]
fpPush b bfirst aprev alast dA = do
  reverseProp dA alast
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  go mxitr (D eps) 0 alast aprev dA
  adjBf <- adjoint bfirst
  P.pure [(X adjBf, b)]
  where
    go ::
         (P.Ord a, Core a)
      => P.Int
      -> D a
      -> P.Int
      -> D a
      -> D a
      -> D a
      -> Computation a ()
    go miter eps oi apr alst d =
      let i = oi P.+ 1
      in if i P.>= miter
           then P.pure ()
           else do
             adjP <- adjoint apr
             adjL <- adjoint alst
             dmadjL <- d - adjL
             s <- adjP + dmadjL
             as <- abs s
             if as P.<= eps
               then P.pure ()
               else do
                 dadjP <- d + adjP
                 reverseProp (dadjP) adjL

instance (P.Ord a, Core a) => Trace FixPoint a where
  pushEl (FxP _ (b, bfirst, aprev, alast)) = fpPush b bfirst aprev alast
  resetEl (FxP _ (b, bf, ap, al)) = P.pure [b]

fixPoint :: (P.Ord a, Trace Noop a, Core a) =>(D a -> D a -> D a) -> D a -> D a -> Computation a (D a)
fixPoint g a0 b = do
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  case b of
    D _ -> goD g (D eps) mxitr 1 a0 b
    DF _ _ bi -> goDF g (D eps) mxitr 1 a0 b bi
    DR bp _ bi _ -> goDR g (D eps) mxitr 1 a0 b bi bp
  where
    goD ::
         (P.Ord a, Core a)
      => (D a -> D a -> D a)
      -> D a
      -> P.Int
      -> P.Int
      -> D a
      -> D a
      -> Computation a (D a)
    goD g e m i a b =
      let ni = i P.+ 1
      in if ni P.>= m
           then pure a
           else do
                let aa = g a b
                d <- aa - a
                ad <- abs d
                if ad P.<= e
                     then pure a
                     else goD g e m ni aa b
    goDF ::
         (P.Ord a, Core a)
      => (D a -> D a -> D a)
      -> D a
      -> P.Int
      -> P.Int
      -> D a
      -> D a
      -> Tag
      -> Computation a (D a)
    goDF g e m i a b bi =
      let ni = i P.+ 1
      in if ni P.>= m
           then pure P.$ DF (p a) (t a) bi
           else do
                let aa = g a b
                ps <- ( p aa) - (p a)
                arg <- abs (ps)
                td <- t aa - t a
                if (arg P.<= e)  P.&& (td P.<= e)
                     then pure P.$ DF (p a) (t a) bi
                     else goDF g e m ni aa b bi
    drFin ::
         ( Trace Noop a, P.Ord a, Core a)
      => (D a -> D a -> D a)
      -> D a
      -> Tag
      -> D a
      -> D a
      -> Computation a (D a)
    drFin g a bi bfirst b = do
      aprev <- r (p a) (N Noop) bi
      let alast = g aprev bfirst
      r (p a) (FxP FixPoint (b, bfirst, aprev, alast)) bi
    goDR ::
         (P.Ord a,Trace Noop a, Core a)
      => (D a -> D a -> D a)
      -> D a
      -> P.Int
      -> P.Int
      -> D a
      -> D a
      -> Tag
      -> D a
      -> Computation a (D a)
    goDR g e m i a b bi bfirst =
      let ni = i P.+ 1
      in if ni P.>= m
           then drFin g a bi bfirst b
           else do
                let aa = g a b
                d <- aa - a
                ad <- abs d
                if ad P.<= e
                     then drFin g a bi bfirst b
                     else goDR g e m ni aa b bi bfirst
