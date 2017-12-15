
module Main where


import Test.DocTest
import Test.Tasty() -- (TestTree, defaultMain, testGroup, localOption)
import Test.Tasty.QuickCheck()


main :: IO ()
main = do
  putStrLn "Num DocTest"
  doctest ["src/Num.hs"]
  -- defaultMain tests
