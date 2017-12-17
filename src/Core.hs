{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FunctionalDependencies  #-}
-- {-# LANGUAGE UndecidableInstances  #-}

module Core
    ( module Core
    ) where

import           Control.Monad.State.Strict (State, evalState, get, gets,
                                             modify, put, runState, (>=>))
import qualified Data.Map                   as M (Map, empty, insert, lookup,
                                                  update, updateLookupWithKey)
import           Lens.Micro                 ((%~), (&), (.~), (^.))
import           Lens.Micro.TH              (makeLenses)
import           Prelude                    hiding (abs, signum, (*), (+), (-))
import qualified Prelude                    as P

import           Debug.Trace

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts
-- >>> let b = D 2
-- >>> let a = D 3

data Noop = Noop

data Add = Add

data Abs = Abs

data Sign = Sign

data Subtract = Subtract

data Negate = Negate

data Multiply = Multiply



--The types of arity an operation can have

data Arity
  = Unary
  | Binary
  | Nil
  | SymmetricBinary
  | IndexedUnary
  | FxPoint


-- the tape at a binary operation will either have two expressions (one to each arugment of the op) or a single expression
type family OpArity op :: Arity -- Encodes the arity of the arguments of the op


-- type instance OpTapeArity op
-- To store the adoint we have to keep track of the outputs of an operation as well as the expressions that yeild the dual of the input arguments
data DualTrace op a where
  N :: op -> DualTrace op a
  U :: op -> D a -> DualTrace op a
  B :: op -> D a -> D a -> DualTrace op a
  IxU :: op -> D a -> [Int]  -> DualTrace op a
  FxP :: op ->  FptNode a -> DualTrace op a

instance (Show op, Show a) => Show (DualTrace op a) where
  show (N o) = "N " ++ show o
  show (U o t ) = "U " ++ show o ++ show t -- ++ show c
  show (B o t tt) = "B " ++ show o ++ show t ++ show tt
  show (IxU o t ix ) = "IxU " ++ show o ++ show t ++ show ix
  show (FxP o (a, b, c, d)) = "Fxp "  ++ show o ++ show a ++ show b ++ show c ++ show d


type FptNode a = (D a, D a, D a, D a) -- nodes needed for a fixpoint evaluation


newtype Tag = Tag Int
  deriving (Eq, Ord, Show)

newtype UID = UID Int
  deriving (Eq, Ord, Show)


type Fanouts = M.Map UID Tag

type Adjoints a = M.Map UID (D a)


data ComputationState a = ComputationState
  { _nextTag   :: !Tag
  , _nextUID   :: !UID
  , _adjoints  :: Adjoints a
  , _fanouts   :: Fanouts
  , _fpEps     :: a
  , _maxFpIter :: Int
  }

type Computation a = State (ComputationState a)

data D a where
  D :: a -> D a
  DF :: Primal a -> Tangent a -> Tag -> D a
  DR :: (Trace op a) => D a -> DualTrace op a -> Tag -> UID -> D a

instance (Show a, Show Tag, Show UID ) => Show (D a) where
  show (D a) = "D " ++ show a
  show (DF p t ti) = "DF " ++ show p ++ show t ++ show ti
  show (DR p dt ti uid) = "DR " ++ show p ++ "-- fixme --" ++ show ti ++ show uid

type Primal a = D a
type Tangent a = D a


-- the accumulated adjoint at a given node in reverse-mode is aliased as a Delta
data Delta a
  = X (D a)
  | XNeg (D a)
  deriving (Show)

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
  put (st & nextTag .~ (Tag (t P.+ 1)))
  return tg

getNextUID :: Computation a (UID)
getNextUID = do
  st <- get
  let tg@(UID t) = st ^. nextUID
  put (st & nextUID .~ (UID (t P.+ 1)))
  return tg


instance (Eq a) => Eq (D a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D a) where
  d1 `compare` d2 = pD d1 `compare` pD d2

--Core operations;  FIXME:   Move these to a real numeric hierarchy when things are working.

class (Show t) => BinCore a b t where
  (+) :: a -> b -> Computation t (D t) -- need to split all these classes
  (-) :: a -> b -> Computation t (D t) -- BinCore
  (*) :: a -> b -> Computation t (D t) -- BinCore

class (Show t) => MonCore a t where
  abs :: a -> Computation t (D t) -- MonCore
  signum :: a -> Computation t (D t) -- MonCore

class (Show t) => UnitalCore t where
  zero :: Computation t (D t) -- UnitalCore
  one :: Computation t (D t) -- UnitalCore

type CoreConstraintsBin a b c
   = ( BinOp Add a b c
     , Num c
     , BinOp Subtract a b c
     , BinOp Multiply a b c
     , DfDaBin Add a c
     , DfDbBin Add b c
     , DfDaBin Subtract a c
     , DfDbBin Subtract b c
     , DfDaBin Multiply a c
     , DfDbBin Multiply b c
     , Trace Add c
     , Trace Subtract c
     , Trace Multiply c
     , Ord c)

type CoreConstraintsMon a = (MonOp Abs a, MonOp Sign a, UnitalCore a, Num a)

instance (CoreConstraintsBin (D Float) (D Float) Float) =>
         BinCore (Computation Float (D Float)) (Computation Float (D Float)) Float where
  (+) a b = do
    aa <- a
    bb <- b
    binOp Add aa bb
  (-) a b = do
    aa <- a
    bb <- b
    binOp Subtract aa bb
  (*) a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance (CoreConstraintsBin (D Float) (D Float) Float) => MonCore  (Computation Float (D Float)) Float where
  abs a = do
    aa <- a
    monOp Abs aa
  signum a = do
    aa<- a
    monOp Sign aa

instance UnitalCore Float where
  zero = pure $ D 0
  one = pure $ D 1

instance (CoreConstraintsBin (D Double) (D Double) Double) =>  BinCore  (Computation Double (D Double))  (Computation Double (D Double)) Double where
  (+) a b = do
    aa <- a
    bb <- b
    binOp Add aa bb
  (-) a b = do
    aa <- a
    bb <- b
    binOp Subtract aa bb
  (*) a b = do
    aa <- a
    bb <- b
    binOp Multiply aa bb

instance (CoreConstraintsBin (D Double) (D Double) Double) => MonCore  (Computation Double (D Double)) Double where
  abs a = do
    aa <- a
    monOp Abs aa
  signum a = do
    aa<- a
    monOp Sign aa

instance UnitalCore Double where
  zero =pure $  D 0
  one = pure $  D 1

instance (CoreConstraintsBin (D Float) (D Float) Float) => BinCore  (D Float)  (D Float) Float where
  (+) a b = binOp Add a b
  (-) a b = binOp Subtract a b
  (*) a b = binOp Multiply a b

instance (CoreConstraintsBin (D Float) (D Float) Float) => MonCore (D Float) Float where
  abs a = monOp Abs a
  signum a = monOp Sign a


instance (CoreConstraintsBin (D Double) (D Double) Double) =>  BinCore (D Double)  (D Double) Double where
  (+) a b = binOp Add a b
  (-) a b = binOp Subtract a b
  (*) a b = binOp Multiply a b

instance (CoreConstraintsBin (D Double) (D Double) Double) => MonCore (D Double) Double where
  abs a = monOp Abs a
  signum a = monOp Sign a


instance (CoreConstraintsBin (D Float) (D Float) Float) => BinCore  (Computation Float (D Float))  (D Float) Float where

  (+) a b = do
    aa <- a
    binOp Add aa b
  (-) a b = do
    aa <- a
    binOp Subtract aa b
  (*) a b = do
    aa <- a
    binOp Multiply aa b


instance (CoreConstraintsBin (D Double) (D Double) Double) => BinCore (Computation Double (D Double))  (D Double) Double where
  (+) a b = do
    aa <- a
    binOp Add aa b
  (-) a b = do
    aa <- a
    binOp Subtract aa b
  (*) a b = do
    aa <- a
    binOp Multiply aa b

instance (CoreConstraintsBin (D Float) (D Float) Float) => BinCore (D Float)  (Computation Float (D Float))  Float where
  (+) a b = do
    bb <- b
    binOp Add a bb
  (-) a b = do
    bb <- b
    binOp Subtract a bb
  (*) a b = do
    bb <- b
    binOp Multiply a bb

instance (CoreConstraintsBin (D Double) (D Double) Double) => BinCore  (D Double) (Computation Double (D Double)) Double where
  (+) a b = do
    bb <- b
    binOp Add a bb
  (-) a b = do
    bb <- b
    binOp Subtract a bb
  (*) a b = do
    bb <- b
    binOp Multiply a bb

initComp :: (RealFrac a) => ComputationState a
initComp = ComputationState (Tag 0) (UID 0) M.empty M.empty (1e-6) 1000


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

toNumeric :: D a -> a

toNumeric d =
  let (D n) = pD d
  in n

-- Get Tangent
t :: (UnitalCore a) => D a -> Computation a (Tangent a)
t =
  \case
    D _ -> zero
    DF _ at _ -> pure at
    DR {} -> error "Can't get tangent of a reverse node"

mkForward :: Tag -> Tangent a -> Primal a  -> D a
mkForward i tg d  = DF d tg i


mkReverse :: (Trace Noop a) => Tag -> D a -> Computation a (D a)
mkReverse i d = r d (N Noop) i

class MonOp op a where
  ff ::( Computation a ~ m) => op -> a -> a
  fd :: ( Computation a ~ m) =>  op -> D a -> m (D a)
  df :: ( Computation a ~ m) =>  op -> D a -> D a -> D a ->m( D a)

monOp' :: (Trace op a, Computation a ~ m) =>
     op
  -> D a
  -> (a -> a)
  -> (D a -> m (D a))
  -> (D a -> D a -> D a -> m (D a))
  -> (D a -> DualTrace op a)
  -> Computation a (D a)
monOp' _ a ff fd df r_ =
  case a of
    D ap -> return . D $ ff ap
    DF ap at ai -> do
      cp <- fd ap
      cdf <- df cp ap at
      return $ DF cp cdf ai
    DR ap _ ai _ ->do
      cp <- fd ap
      r cp (r_ a) ai

monOp :: (MonOp op a, (Trace op a)) => op -> D a -> Computation a (D a)
monOp op a =
  let r_d =   U op
  in monOp' op a (ff op) (fd op) (df op) r_d


binOp' ::
     (Trace op a, Computation a ~ m)
  => op
  -> (D a)
  -> (D a)
  -> (a -> a -> a)
  -> (D a -> D a -> m (D a))
  -> (D a -> D a -> D a -> m (D a))
  -> (D a -> D a -> D a -> m (D a))
  -> (D a -> D a -> D a -> D a -> D a -> m (D a))
  -> (D a -> D a -> DualTrace op a)
  -> (D a -> D a -> DualTrace op a)
  -> (D a -> D a -> DualTrace op a)
  -> m (D a)
binOp' _ a b ff fd df_da df_db df_dab r_d_d r_d_c r_c_d = do
  case a of
    D ap ->
      case b of
        D bp -> return . D $ ff ap bp
        DF bp bt bi -> do
          cp <- fd a bp
          cdf <- df_db cp bp bt
          return $ DF cp cdf bi
        DR bp _ bi _ -> do
          cfd <- fd a bp
          r (cfd) (r_c_d a b) bi
    DF ap at ai ->
      case b of
        D _ -> do
          cp <- fd ap b
          cdf <- df_da cp ap at
          return $ DF cp (cdf) ai
        DF bp bt bi ->
          case compare ai bi of
            EQ -> do
              cp <- fd ap bp
              cdf <- df_dab cp ap at bp bt
              return $ DF cp (cdf) ai
            LT -> do
              cp <- fd a bp
              cdf <- df_db cp bp bt
              return $ DF cp (cdf) bi
            GT -> do
              cp <- fd ap b
              cdf <- df_da cp ap at
              return $ DF cp (cdf) ai
        DR bp _ bi _ ->
          case compare ai bi of
            LT -> do
              fdb <- fd a bp
              r (fdb) (r_c_d a b) bi
            GT -> do
              cp <- fd ap b
              cdf <- df_da cp ap at
              return $ DF cp (cdf) ai
            EQ -> error "Forward and reverse AD cannot run on the same level."
    DR ap _ ai _ ->
      case b of
        D _ -> do
          fda <- fd ap b
          r (fda) (r_d_c a b) ai
        DF bp bt bi ->
          case compare ai bi of
            EQ -> error "Forward and reverse AD cannot run on the same level."
            LT -> do
              cp <- fd a bp
              cdf <- df_db cp bp bt
              return $ DF cp (cdf) bi
            GT -> do
              fdb <- fd ap b
              r (fdb) (r_d_c a b) ai
        DR bp _ bi _ ->
          case compare ai bi of
            EQ -> do
              fdap <- fd ap bp
              r (fdap) (r_d_d a b) ai
            LT -> do
              fdab <- fd a bp
              r (fdab) (r_c_d a b) bi
            GT -> do
              fdab <- fd ap b
              r (fdab) (r_d_c a b) ai




-- binOp :: ( BinOp op a,(Trace op a), Computation a ~ m)
--   =>
--   op
--   ->  (D a)
--   ->  (D a)
--   -> m (D a)
-- binOp op a b =
--   let traceOp = B op
--       r_d_d = traceOp
--       r_d_c = traceOp
--       r_c_d = traceOp
--   in binOp'
--        op
--        a
--        b
--        (ff_bin op)
--        (fd_bin op)
--        (df_da op b)
--        (df_db op a)
--        (df_dab op)
--        r_d_d
--        r_d_c
--        r_c_d

class FFBin op c where
  ff_bin :: op -> c -> c -> c
  binOp :: (Trace op c, BinOp op (D c) (D c) c, DfDaBin op (D c) c, DfDbBin op (D c) c) => op -> D c -> D c -> Computation c (D c)
  binOp op a b =
    let traceOp = B op
        r_d_d = traceOp
        r_d_c = traceOp
        r_c_d = traceOp
    in binOp'
         op
         a
         b
         (ff_bin op )
         (fd_bin op)
         (df_da op b)
         (df_db op a)
         (df_dab op a b)
         r_d_d
         r_d_c
         r_c_d

class DfDaBin op b c | b -> c where
  df_da :: (Computation c ~ m) => op -> b -> D c -> D c -> D c -> m (D c)

class DfDbBin op a c | a -> c where
  df_db :: (Computation c ~ m) => op -> a -> D c -> D c -> D c -> m (D c)


class BinOp op a b c | a b -> c where
  fd_bin :: (Computation c ~ m) => op -> a -> b -> m (D c) --BinOp
  df_dab ::
       (Computation c ~ m) --BinOp
    => op
    -> a
    -> b
    -> (D c)
    -> (D c)
    -> (D c)
    -> (D c)
    -> (D c)
    -> m (D c)


-- type BinOpConditions a = (P.Num a
--          , BinCore (Computation a (D a)) (Computation a (D a)) a
--          , BinCore (D a) (D a) a)
                       
instance Trace Noop a where
  pushEl _ _ = pure []
  resetEl _ = pure []

-- | Addition
-- >>> compute $ diff' (\x -> x + a) a
-- (D 4.0, D 1.0)
instance (P.Num a) => FFBin Add a where
    {-# INLINE ff_bin #-}
    ff_bin  _ a b = b P.+ a

instance DfDaBin Add (Computation a (D a)) a where
    {-# INLINE df_da #-}
    df_da  _ _ _ _ at = pure at

instance  DfDbBin Add (Computation a (D a)) a where
    {-# INLINE df_db #-}
    df_db _ _ _ _ bt = pure bt

instance (WhatICanWorkWith a) =>
         BinOp Add (Computation a (D a)) (Computation a (D a)) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = a + b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt = at + bt

instance Trace Add a where
  pushEl (B _ a b) dA =
    pure [(X dA, a), (X dA, b), (X dA, a), (X dA, b)]
  resetEl (B _ a b) = pure [a, b, a, b]

-- | Subtraction
-- >>> compute $ diff' (\x -> x - a) a
-- (D 0.0, D 1.0)
instance (P.Num a) => FFBin Subtract a where
    {-# INLINE ff_bin #-}
    ff_bin  _ a b = a P.- b


instance  DfDaBin Subtract (Computation a (D a)) a where
    {-# INLINE df_da #-}
    df_da _  _ _ _ at = pure at

instance (WhatICanWorkWith a) => DfDbBin Subtract (Computation a (D a)) a where
    {-# INLINE df_db #-}
    df_db _  _ _ _ bt = do
      a <- zero -- FIXME: zerp - bt fails to unify the UntialCore a and bt types . . . 
      a - bt

instance (WhatICanWorkWith a) => BinOp Subtract (Computation a (D a)) (Computation a (D a)) a where

  {-# INLINE fd_bin #-}
  fd_bin _ a b =  a - b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ _ at _ bt =  at - bt

instance Trace Subtract a where
  pushEl (B _ a b) dA =
    pure [(X dA, a), (XNeg dA, b), (X dA, a ), (XNeg dA,b )]
  resetEl (B _ a b) = pure [a, b, a, b]

instance (P.Num a, MonCore (D a) a, UnitalCore a) => MonOp Sign a where
  {-# INLINE ff #-}
  ff _ a = P.signum a
  {-# INLINE fd #-}
  fd _ a = signum a
  {-# INLINE df #-}
  df _ _ _ _ = zero


instance (UnitalCore a) => Trace Sign a where
  pushEl (U _ a) dA = do
    z <- zero
    pure [(X z, a)]
  resetEl (U _ a ) = pure [a]



-- | Abs
-- >>> compute $ diff' abs a
-- (a, D 1.0)
instance (MonCore (D a) a, P.Num a, BinCore (D a) (D a) a) => MonOp Abs a where
  {-# INLINE ff #-}
  ff _ a = P.abs a
  {-# INLINE fd #-}
  fd _ a = abs a
  {-# INLINE df #-}
  df _ _ ap at = do
    sap <- signum ap
    at * sap

instance (MonCore (D a) a, P.Num a, BinCore (D a) (D a) a) => Trace Abs a where
  pushEl (U _ a) dA = do
    cdA <- pure dA
    sp <-  signum (p a)
    dl <- cdA * sp
    pure [(X dl, a)]
  resetEl (U _ a ) = pure [a]

-- | Multiplication
-- >>> compute $ diff' (\x -> x * a) a
-- (D 4.0, D 2.0)

instance (P.Num a) => FFBin Multiply a where
  {-# INLINE ff_bin #-}
  ff_bin _ a b =  b P.*  a


type WhatICanWorkWith a
   = ( BinCore (Computation a (D a)) (Computation a (D a)) a
     , BinCore (D a) (D a) a
     , BinCore (Computation a (D a)) (D a) a
     , BinCore (D a) (Computation a (D a)) a
     , MonOp (D a) a
     , MonOp (Computation a (D a)) a
     , UnitalCore a)
     
instance ( WhatICanWorkWith a )=> DfDaBin Multiply (Computation a (D a)) a where
  {-# INLINE df_da #-}
  df_da _ b _ _ at = at * b

instance (WhatICanWorkWith a )=> DfDbBin Multiply (Computation a (D a)) a where
  {-# INLINE df_db #-}
  df_db _ a _ _ bt =  bt * a



instance (WhatICanWorkWith a) => BinOp Multiply (Computation a (D a)) (Computation a (D a)) a where
  {-# INLINE fd_bin #-}
  fd_bin _ a b = a * b
  {-# INLINE df_dab #-}
  df_dab _ _ _ _ ap at bp bt =  do
    cat <- (at * bp)
    cap <- (ap * bt)
    cat + cap -- FIXME: this failes to unify the BinOp (D a) ( D a) t_  in : (at * bp) + (ap * bt)


instance (WhatICanWorkWith a) => Trace Multiply a where
  pushEl (B _ a b) dA = do
    cdA <- pure dA
    opa <- cdA * p b
    opb <- cdA * p a
    arga <- cdA * b
    argb <- cdA * a
    pure [(X opa, a), (X opb, b), (X arga, a), (X argb, b)]
  resetEl (B _ a b) = pure [a, b, a, b]


eval :: (WhatICanWorkWith a) => Delta a -> Computation a (D a)
eval dl =
  case dl of
    X v    -> pure v
    XNeg v -> do
      z <- zero -- FIXME: zero - v failes to unify
      z - v



applyDelta :: (WhatICanWorkWith a) => UID -> Delta a -> Adjoints a -> (Maybe (Computation a (D a)))
applyDelta tag dlta adjs=
  case M.lookup tag adjs of
    Just v -> Just $ do
      e <- eval dlta
      r <- v + e
      modify (\st -> st & adjoints .~ M.update (const . Just $ r) tag adjs)
      return r
    Nothing -> Nothing
  -- M.updateLookupWithKey
  --   (\ k v -> Just $ go dlta k v)
  --   tag
  -- where
  --   go :: Delta a ->  UID -> D a -> (Computation a (D a))
  --   go dlta k v =  do
  --      e <- eval dlta
  --      r <- v + e
  --      return r

decrementFanout :: UID -> Fanouts -> (Maybe Tag, Fanouts)
decrementFanout =
  M.updateLookupWithKey (\k (Tag v) -> Just . Tag $ v P.- 1)

-- updateStack ls = modify (\ st -> st & stack %~ mappend ls)

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


reset :: (UnitalCore a) => [D a] -> Computation a ()
reset l =
  case l of
    [] -> return ()
    (da:xs) ->
      case da of
        DR _ o _ uniq -> do
          fanout <- incrementFanout uniq
          if fanout == Tag 1 then
            do
              z <- zero
              modify (\st -> st & adjoints %~ M.insert uniq z)
              x <- resetEl o
              reset $ x `mappend` xs -- verify this
            else reset xs
          reset xs
        _ -> reset xs

-- recursively pushes nodes onto the reverse mode stack and evaluates partials
push :: (WhatICanWorkWith a) => [(Delta a, D a)] -> Computation a ()
push l =
  case l of
    [] -> return ()
    ((dl, da):xs) ->
      case da of
        DR _ o _ uniq -> do
          st <- gets (\ st -> st ^. adjoints )
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

reverseReset :: UnitalCore a => D a -> Computation a ()
reverseReset d = do
  modify (\st -> st & fanouts .~ M.empty )
  reset [d]

reverseProp :: WhatICanWorkWith a => D a -> D a -> Computation a ()
reverseProp  v d = do
  reverseReset  d
  push [(X v, d)]

{-# INLINE primalTanget #-}
primalTanget :: UnitalCore a => D a -> Computation a (D a, Tangent a)
primalTanget d = do
  ct <- t d
  pure (p d, ct)

adjoint :: UnitalCore a =>  D a -> Computation a (D a)
adjoint d =
  case d of
    DR _ _ _ uniq -> do
      ma <- gets (\st -> M.lookup uniq (st ^. adjoints))
      case ma of
        Just a  -> return a
        Nothing -> error "Adjoint not in map!"
    DF{} -> error "Cannot get adjoint value of DF. Use makeReverse on this node when composing the computation."
    D _ -> zero

runComputation :: (WhatICanWorkWith a) => State s a -> s -> (a, s)
runComputation = runState

compute :: (WhatICanWorkWith a, RealFrac a, MonCore (D a)  a, MonCore (Computation a (D a)) a) => Computation a (b) -> b
compute f = evalState f initComp


{-# INLINE computeAdjoints' #-}
computeAdjoints' :: WhatICanWorkWith a => D a -> Computation a ()
computeAdjoints' d = do
  modify (\st -> st & adjoints .~ M.empty)
  o <- one
  reverseProp o d

{-# INLINE computeAdjoints #-}
computeAdjoints :: WhatICanWorkWith a => D a -> Computation a (Adjoints a)
computeAdjoints d = do
  computeAdjoints' d
  st <- get
  return $ st ^. adjoints
{-# INLINE diff' #-}

diff' :: WhatICanWorkWith a => (D a ->  Computation a (D a)) -> D a -> Computation a (D a, Tangent a)
diff' f x = do
  n <- getNextTag
  o <- one
  fout <- f $ mkForward n o x
  primalTanget fout
{-# INLINE diff #-}

diff :: WhatICanWorkWith a => (D a -> Computation a (D a)) -> D a -> Computation a (Tangent a)
diff f x =
  snd <$> diff' f x

{-# INLINE diffn #-}
diffn :: WhatICanWorkWith a => Int -> (D a -> Computation a (D a)) -> D a -> Computation a (Tangent a)
diffn n f x =
  if n < 0
    then error "Cannot get the nth derivitive when n is negative!"
    else if n == 0
           then f x
           else go n f x
  where
    go :: WhatICanWorkWith a => Int -> (D a -> Computation a (D a)) -> D a -> Computation a (Tangent a)
    go n f =
      case n of
        0 -> diff f
        _ -> go (n P.- 1) f >=> diff f

{-# INLINE diffn' #-}
diffn'
  :: WhatICanWorkWith a => Int -> (D a -> Computation a (D a)) -> D a -> Computation a (D a, (Tangent a))
diffn' n f x = do
  it <- f x
  again <- diffn n f x
  return (it, again)

{-# INLINE grad' #-}
grad' ::
     (Trace Noop a, WhatICanWorkWith a) =>
  (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a, (D a))
grad' f x = do
  ntg <- getNextTag
  xa <-  trace ("calling mkReverse with x = " ++ show x) mkReverse ntg x
  z <- trace ("calling f with xa = " ++ show xa) f xa
  trace ("calling computeAdjoints' with z = " ++ show z) computeAdjoints' z
  adj <- trace ("calling adjoint' with xa = " ++ show xa) adjoint xa
  trace ("calling return with adj = " ++ show adj) return (p xa, adj)

{-# INLINE grad #-}
grad ::
     (Trace Noop a, WhatICanWorkWith a ) =>
   (D a -> Computation a (D a))
  -> D a
  -> Computation a (D a)
grad f x = do
  (_, g)<- grad' f x
  return g

-- Original value and Jacobian product of `f`, at point `x`, along `v`. Forward AD.
jacobian' :: WhatICanWorkWith a =>
     (D a -> Computation a (D a)) -> Tangent a -> Primal a -> Computation a (D a, Tangent a)
jacobian' f x v = do
  ntg <- getNextTag
  fout <- f $ mkForward ntg v x
  primalTanget fout

jacobian :: WhatICanWorkWith a => (D a -> Computation a (D a)) -> Tangent a -> Primal a -> Computation a (Tangent a)
jacobian f x v = snd <$> jacobian' f x v
