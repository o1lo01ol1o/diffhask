{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Num () where
import           Control.Monad.State.Strict (State, get, gets, modify, put,
                                             (>=>), join)
import           Core
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Ops
type instance OpArity Noop = 'Nil

type instance OpArity Add = 'SymmetricBinary

type instance OpArity Subtract = 'Binary

type instance OpArity Negate = 'Unary

type instance OpArity Multiply = 'SymmetricBinary

type instance OpArity FixPoint = 'FxPoint

instance Dual Add a where
  dual _ = SBExp const

instance (Num (D a), Unital a ) => Dual Negate a where
  dual _ = UExp (\a -> zero - a)

instance (Num (D a), Num (D (D a)), Unital a) => Dual Subtract a where
  dual _ = BExp const (\ _ b -> zero - b)

instance (Num a, Dual Add a, Num (Computation a a), Num (D a)) => BinOp Add a where
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
  pushEl (B _ a b ac bc) dA =
    return [(X dA, a), (X dA, b), (X dA, ac a b), (X dA, bc b a)]
  resetEl (B _ a b _ _) = return [a, b, a, b]

instance (Num a, Dual Add a, Num (Computation a a), Num (D a)) => BinOp Subtract a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  a - b
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a- b
  {-# INLINE df_da #-}
  df_da _ _ _ _ at =  at
  {-# INLINE df_db #-}
  df_db _ _ _ _ bt =  negate bt
  {-# INLINE df_dab #-}
  df_dab _ _ _ at _ bt =  at - bt

instance (Num a, Dual Add a, Dual Subtract a, Num (Computation a a), Num (D a)) =>
         Num (Computation a (D a)) where
  a + b = do
    ca <- a
    cb <- b
    binOp Add ca cb
  a - b = do
    ca <- a
    cb <- b
    binOp Subtract ca cb

instance Trace Subtract a where
  pushEl (B _ a b ac bc) dA =
    return [(X dA, a), (XNeg dA, b), (X dA, ac a b), (XNeg dA, bc b a)]
  resetEl (B _ a b _ _) = return [a, b, a, b]


instance (Num (D a)) => Dual Multiply a where
  dual _ = SBExp (\ a b -> a * b + a * b) -- FIXME: do we want this dual here?

instance (Num a, Dual Add a, Num (Computation a a), Num (D a)) => BinOp Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b *  a
  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a * b
  {-# INLINE df_da #-}
  df_da _ b _ _ at =  at * b
  {-# INLINE df_db #-}
  df_db _ a _ _ bt =  bt * a
  {-# INLINE df_dab #-}
  df_dab _ _ ap at bp bt =  at * bp + ap * bt

instance (Num (D a)) => Trace Multiply a where
  pushEl (B _ a b _ _) dA =
    return [(X (dA * p b), a), (X (dA * p a), b), (X (dA * b), a), (X (dA * a), b)] --- rethink the dual expressions  . . .
  resetEl (B _ a b _ _) =return  [a, b, a, b]



fpPush ::
     (Num (D a), Num a, Unital a, Ord a)
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
  return [(X adjBf, b)]
  where
    go ::
         (Unital a, Ord a, Num a, Num (D a))
      => Int
      -> D a
      -> Int
      -> D a
      -> D a
      -> D a
      -> Computation a ()
    go miter eps oi apr alst d =
      let i = oi + 1
      in if i >= miter
           then return ()
           else do
             adjP <- adjoint apr
             adjL <- adjoint alst
             if abs (adjP + (d - adjL)) <= eps
               then return ()
               else reverseProp (d + adjP) adjL

instance (Num (D a), Num a, Unital a, Ord a) => Trace FixPoint a where
  pushEl (FxP _ (b, bfirst, aprev, alast)) = fpPush b bfirst aprev alast
  resetEl (FxP _ (b, bf, ap, al)) = return [b]

fixPoint :: (Ord a, Num (D a), Unital a, Num a, Trace Noop a) =>(D a -> D a -> D a) -> D a -> D a -> Computation a (D a)
fixPoint g a0 b = do
  eps <- gets (\st -> st ^. fpEps)
  mxitr <- gets (\st -> st ^. maxFpIter)
  case b of
    D _ -> return $ goD g (D eps) mxitr 1 a0 b
    DF _ _ bi -> return $ goDF g (D eps) mxitr 1 a0 b bi
    DR bp _ bi _ -> goDR g (D eps) mxitr 1 a0 b bi bp
  where
    goD ::
         (Ord a, Num (D a))
      => (D a -> D a -> D a)
      -> D a
      -> Int
      -> Int
      -> D a
      -> D a
      -> D a
    goD g e m i a b =
      let ni = i + 1
      in if ni >= m
           then a
           else let aa = g a b
                in if abs (aa - a) <= e
                     then a
                     else goD g e m ni aa b
    goDF ::
         (Ord a, Num (D a), Unital a)
      => (D a -> D a -> D a)
      -> D a
      -> Int
      -> Int
      -> D a
      -> D a
      -> Tag
      -> D a
    goDF g e m i a b bi =
      let ni = i + 1
      in if ni >= m
           then DF (p a) (t a) bi
           else let aa = g a b
                in if abs (p aa - p a) <= e && (t aa - t a) <= e
                     then DF (p a) (t a) bi
                     else goDF g e m ni aa b bi
    drFin ::
         (Num a, Trace Noop a, Unital a, Num (D a), Ord a)
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
         (Ord a, Num (D a), Unital a, Num a, Trace Noop a)
      => (D a -> D a -> D a)
      -> D a
      -> Int
      -> Int
      -> D a
      -> D a
      -> Tag
      -> D a
      -> Computation a (D a)
    goDR g e m i a b bi bfirst =
      let ni = i + 1
      in if ni >= m
           then drFin g a bi bfirst b
           else let aa = g a b
                in if abs (aa - a) <= e
                     then drFin g a bi bfirst b
                     else goDR g e m ni aa b bi bfirst
