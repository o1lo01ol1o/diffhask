
main :: IO ()
main = defaultMain [bench "const" (whnf const ())]
 
