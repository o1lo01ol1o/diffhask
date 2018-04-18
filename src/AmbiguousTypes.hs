{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module AmbiguousTypes where
import           Control.Monad.Cont         (Cont (..), ContT (..), cont,
                                             runContT)
import           Control.Monad.Identity
import           Control.Monad.State.Strict (State, StateT, evalState, get,
                                             gets, modify, put, runState, (>=>))
import           Control.Monad.Trans
import           GHC.TypeLits
import           Prelude


