{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE UndecidableInstances          #-}
module Num (module Num) where
import           Control.Monad.State.Strict (State, get, gets, modify, put,
                                             (>=>), join, liftM, liftM2)
import           Core
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import qualified Prelude as P
import Prelude (pure)

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts


data FixPoint = FixPoint

fpPush ::
     (P.Ord a, WhatICanWorkWith a, MonCore (D a) a)
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
         (P.Ord a, WhatICanWorkWith a, MonCore (D a) a)
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

instance (P.Ord a, WhatICanWorkWith a, MonCore (D a) a) => Trace FixPoint a where
  pushEl (FxP _ (b, bfirst, aprev, alast)) = fpPush b bfirst aprev alast
  resetEl (FxP _ (b, bf, ap, al)) = P.pure [b]

fixPoint :: (P.Ord a, Trace Noop a, WhatICanWorkWith a, MonCore (D a) a) =>(D a -> D a -> D a) -> D a -> D a -> Computation a (D a)
fixPoint g a0 b = do
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  case b of
    D _ -> goD g (D eps) mxitr 1 a0 b
    DF _ _ bi -> goDF g (D eps) mxitr 1 a0 b bi
    DR bp _ bi _ -> goDR g (D eps) mxitr 1 a0 b bi bp
  where
    goD ::
         (P.Ord a, WhatICanWorkWith a, MonCore (D a) a)
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
         (P.Ord a, WhatICanWorkWith a, MonCore (D a) a)
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
           then do
                cta <- t a
                pure P.$ DF (p a) (cta) bi
           else do
                let aa = g a b
                ps <- ( p aa) - (p a)
                arg <- abs (ps)
                td <- t aa - t a
                if (arg P.<= e)  P.&& (td P.<= e)
                     then do
                     cta <- t a
                     pure P.$ DF (p a) (cta) bi
                     else goDF g e m ni aa b bi
    drFin ::
         ( Trace Noop a, P.Ord a, WhatICanWorkWith a, MonCore (D a) a)
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
         (P.Ord a,Trace Noop a, WhatICanWorkWith a, MonCore (D a) a)
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
