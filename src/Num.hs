{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
module Num (module Num) where
import           Control.Monad.State.Strict (State, get, gets, modify, put,
                                             (>=>), join)
import           Core
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import            Ops
import qualified Prelude as P

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts


instance  BinOp Add a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b +  a
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a + b
  {-# INLINE df_da #-}
  df_da _ _ _ _ at =  at
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt =  bt
  {-# INLINE df_dab #-}
  df_dab _ _ _ at _ bt =  at + bt


instance Trace Add a where
  pushEl (B _ a b) dA =
    return [(X dA, a), (X dA, b), (X dA, a), (X dA, b)]
  resetEl (B _ a b) = return [a, b, a, b]

instance  BinOp Subtract a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  a - b
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a - b
  {-# INLINE df_da #-}
  df_da _ _ _ _ at =  at
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt =  zero - bt
  {-# INLINE df_dab #-}
  df_dab _ _ _ at _ bt =  at - bt

instance Trace Subtract a where
  pushEl (B _ a b ac bc) dA =
    return [(X dA, a), (XNeg dA, b), (X dA, ac a b), (XNeg dA, bc b a)]
  resetEl (B _ a b _ _) = return [a, b, a, b]

instance  BinOp Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.*  a
  {-# INLINE fd_bin #-}
  fd_bin _ a b = do
    aa <- a
    bb <- b
    P.pure $ aa * bb
  {-# INLINE df_da #-}
  df_da _ b _ _ at = (P.pure at) * b
  {-# INLINE df_db #-}
  df_db _ a _ _ bt =  bt * a
  {-# INLINE df_dab #-}
  df_dab _ _ ap at bp bt =  at * bp + ap * bt

instance  Trace Multiply a where
  pushEl (B _ a b ) dA =
    return [(X (dA * p b), a), (X (dA * p a), b), (X (dA * b), a), (X (dA * a), b)] --- rethink the dual expressions  . . .
  resetEl (B _ a b ) =return  [a, b, a, b]



fpPush ::
     (P.Ord a)
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
         (P.Ord a)
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
             if abs (adjP + (d - adjL)) P.<= eps
               then P.pure ()
               else reverseProp (d + adjP) adjL

instance (P.Ord a) => Trace FixPoint a where
  pushEl (FxP _ (b, bfirst, aprev, alast)) = fpPush b bfirst aprev alast
  resetEl (FxP _ (b, bf, ap, al)) = P.pure [b]

fixPoint :: (P.Ord a, Trace Noop a) =>(D a -> D a -> D a) -> D a -> D a -> Computation a (D a)
fixPoint g a0 b = do
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  case b of
    D _ -> P.pure P.$ goD g (D eps) mxitr 1 a0 b
    DF _ _ bi -> P.pure P.$ goDF g (D eps) mxitr 1 a0 b bi
    DR bp _ bi _ -> goDR g (D eps) mxitr 1 a0 b bi bp
  where
    goD ::
         (P.Ord a)
      => (D a -> D a -> D a)
      -> D a
      -> P.Int
      -> P.Int
      -> D a
      -> D a
      -> D a
    goD g e m i a b =
      let ni = i P.+ 1
      in if ni P.>= m
           then a
           else let aa = g a b
                in if abs (aa - a) P.<= e
                     then a
                     else goD g e m ni aa b
    goDF ::
         (P.Ord a)
      => (D a -> D a -> D a)
      -> D a
      -> P.Int
      -> P.Int
      -> D a
      -> D a
      -> Tag
      -> D a
    goDF g e m i a b bi =
      let ni = i P.+ 1
      in if ni P.>= m
           then DF (p a) (t a) bi
           else let aa = g a b
                in if (abs (p aa - p a) P.<= e) P.&& ((t aa - t a) P.<= e)
                     then DF (p a) (t a) bi
                     else goDF g e m ni aa b bi
    drFin ::
         ( Trace Noop a, P.Ord a)
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
         (P.Ord a,Trace Noop a)
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
           else let aa = g a b
                in if abs (aa - a) P.<= e
                     then drFin g a bi bfirst b
                     else goDR g e m ni aa b bi bfirst
