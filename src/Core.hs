{-#LANGUAGE LambdaCase#-}
{-#LANGUAGE GADTs #-}
{-#LANGUAGE TypeFamilies #-}
{-#LANGUAGE FunctionalDependencies #-}
{-#LANGUAGE MultiParamTypeClasses#-}
module Core
    ( 
    ) where

import Data.Map (Map)

type Fanouts = Map Tag UID

type Adjoints a = Map Tag (D a)

data Delta a
  = X (D a)
  | XNeg (D a)

-- make this take a state monad to keep track of all these things.
class Trace op a where
  resetRec0 :: op -> [TraceOp a] -> Fanouts
  pushRec0 :: op -> Adjoints a -> [TraceOp a] -> ()
  resetRec1 :: op -> D a -> [TraceOp a] -> Fanouts
  pushRec1 :: op -> D a -> Adjoints a -> [TraceOp a] -> ()
  resetRec2 :: op -> D a -> D a -> [TraceOp a] -> Fanouts
  pushRec2 :: op -> D a -> D a -> Adjoints a -> [TraceOp a] -> ()
  resetRecIx :: op -> D a -> [Integer] -> [TraceOp a] -> Fanouts
  pushRecIx :: op -> D a -> [Integer] -> Adjoints a -> [TraceOp a] -> ()
  resetRecQ :: op -> D a -> D a -> D a -> D a -> [TraceOp a] -> Fanouts
  pushRecQ :: op -> D a -> D a -> D a -> D a -> Adjoints a -> [TraceOp a] -> ()
  {-# MINIMAL (resetRec0, pushRec0)
            | (resetRec1, pushRec1)
            | (resetRec2, pushRec2)
            | (resetRecIx, pushRecIx) | (resetRecQ, pushRecQ) #-}

-- Deep embedding is the arity of the trace
data TraceOp a where
  NilOp :: TraceOp a
  S :: (Trace op a) => op ->  D a -> TraceOp a
  P :: (Trace op a) => op -> D a -> D a -> TraceOp a
  Ix :: (Trace op a) => op -> D a -> [Integer] -> TraceOp a
  Q :: (Trace op a) => op ->  D a ->  D a -> D a -> D a -> TraceOp a

data Noop 

instance Trace Noop a where
  resetRec0 = undefined
  pushRec0 _ _ _ = ()

type Tag = Integer

type UID = Integer


zero = undefined
supplyValue = undefined

type Primal a = D a
type Tangent a = D a

data D a where
  D :: a -> D a
  DF :: Primal a -> Tangent a -> UID -> D a
  DR :: Trace trace => D a -> trace -> Tag -> UID -> D a

instance (Eq a) => Eq (D a) where
  d1 == d2 = pD d1 == pD d2


instance (Ord a) => Ord (D a) where
  d1 `compare` d2 = pD d1 `compare` pD d2
  
-- Make a reverse node
r :: (Trace at) => D a -> at -> Tag -> D a
r d op ai =
  let uid = supplyValue
  in DR d op ai uid
  
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

-- Get Tangent 
t :: D a -> Tangent a
t =
  \case
    D _ -> D zero
    DF _ at _ -> at
    DR {} -> error "Can't get tangent of a reverse node"

type Ff_m a = (a -> a)
type Fd_m a = (D a -> D a)
type Df_m a = (D a -> D a -> D a -> D a)
type R_m a at = (D a -> at)

monOp' a ff fd df r_ =
  case a of
    D ap -> D $ ff ap
    DF ap at ai ->
      let cp = fd ap
      in DF cp (df cp ap at) ai
    DR ap _ ai _ ->
      let cp = fd ap
      in r cp (r_ a) ai

binOp' a b ff fd df_da df_db df_dab r_d_d r_d_c r_c_d =
    case a of
      D ap ->
        case b of
          D bp -> D $ ff ap bp
          DF bp bt bi ->
            let cp = fd a bp
            in DF cp (df_db cp bp bt) bi
          DR bp _ bi _ -> r (fd a bp) (r_c_d a b) bi
      DF ap at ai ->
        case b of
          D _ ->
            let cp = fd ap b
            in DF cp (df_da cp ap at) ai
          DF bp bt bi ->
            case compare ai bi of
              EQ ->
                let cp = fd ap bp
                in DF cp (df_dab cp ap at bp bt) ai
              LT ->
                let cp = fd a bp
                in DF cp (df_db cp bp bt) bi
              GT ->
                let cp = fd ap b
                in DF cp (df_da cp ap at) ai
          DR bp _ bi _ ->
            case compare ai bi of
              LT -> r (fd a bp) (r_c_d a b) bi
              GT ->
                let cp = fd ap b
                in DF cp (df_da cp ap at) ai
              EQ -> error "Forward and reverse AD cannot run on the same level."
      DR ap _ ai _ ->
        case b of
          D _ -> r (fd ap b) (r_d_c a b) ai
          DF bp bt bi ->
            case compare ai bi of
              EQ -> error "Forward and reverse AD cannot run on the same level."
              LT ->
                let cp = fd a bp
                in DF cp (df_db cp bp bt) bi
              GT -> r (fd ap b) (r_d_c a b) ai
          DR bp _ bi _ ->
            case compare ai bi of
              EQ -> r (fd ap bp) (r_d_d a b) ai
              LT -> r (fd a bp) (r_c_d a b) bi
              GT -> r (fd ap b) (r_d_c a b) ai
  
type Ff_b a = (a -> a -> a)
type Fd_b a b = (D a -> D b -> D b)
type Df_da a = (D a -> D a -> D a -> D a)
type Df_db a = Df_da a
type Df_dab a b c = (D a -> D b -> Tangent a -> D b -> D b -> Tangent c)
type R_d_d a at b = (D a -> D b -> at)
type R_d_c a at b = (D a -> D b -> at)
type R_c_d a at b = (D a -> D b -> at)



