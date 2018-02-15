{-# LANGUAGE NoImplicitPrelude#-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where


-- import Test.DocTest
import Test.Tasty (testGroup, TestTree,defaultMain) -- (TestTree, defaultMain, testGroup, localOption)
import Test.Tasty.QuickCheck()
import Test.Tasty.HUnit (testCase, (@?=))

import Internal.Internal
import Core
import Num
import Internal.NumHask.Prelude
-- import NumHask.Array()
import qualified NumHask.Array as A
-- import qualified NumHask.Prelude as E

instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveModule (A.Array c s) (D (A.Array c s) Float) (D (A.Array c s) Float) Float where
  (.+) a b = binOp Add a b
  (+.) a b = binOp Add a b
  
instance (AdditiveBasisConstraints (A.Array c s) Float) =>
         AdditiveBasis (A.Array c s) (D (A.Array c s) Float) (D (A.Array c s) Float) Float where
  (.+.) a b = 
    binOp Add a b

-- simple = go
--   where
--     g ::
--          D (A.Array [] '[1]) Float
--       -> D (A.Array [] '[1]) Float
--       -> Computation (A.Array [] '[1]) Float (D (A.Array [] '[1]) Float)
--     g a b = (a + b / a) / (D 2.0 :: D (A.Array [] '[1]) Float)
--     go :: ((D (A.Array [] '[1]) Float), (D (A.Array [] '[1]) Float))
--     go = compute $ diff' (fixPoint g (D 1.2 :: D (A.Array [] '[1]) Float)) (D 25.0 :: D (A.Array [] '[1]) Float)

add = let b = D 2 :: (D (A.Array [] '[]) Float)
          a = D 3 :: (D  (A.Array [] '[0]) Float)
          c = [3,4] :: A.Array [] '[2] Float
          d = Dm c :: (D (A.Array [] '[2]) Float)
      -- in compute $ diff' (+ a) a
      in compute $ a +. d
   

unitTests =
  testGroup
    "Unit tests"
    [ testCase "Addition" $
      add @?= (Dm [6, 7] :: (D (A.Array [] '[2]) Float))
      -- add @?= False


      -- testCase "Fixpoint" $
      -- simple @?=
      -- ( ( (D 1.0 :: D (A.Array [] '[ 1]) Float)
      --   --, (D 5.0 :: D (A.Array [] '[ 1]) Float))
      -- , (( D 1.0 :: D (A.Array [] '[ 1]) Float)
      --  -- , (D 0.1 :: D (A.Array [] '[ 1]) Float)))
      --   )))
    ]

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ unitTests]


