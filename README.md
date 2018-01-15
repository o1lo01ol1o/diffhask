# diffhask

[![Hackage](https://img.shields.io/hackage/v/diffhask.svg)](https://hackage.haskell.org/package/diffhask)
[![Build status](https://secure.travis-ci.org/o1lo01ol1o/diffhask.svg)](https://travis-ci.org/o1lo01ol1o/diffhask)
[![MIT license](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/o1lo01ol1o/diffhask/blob/master/LICENSE)

> Vive la programmation différentielle! 
>
> -- <cite> Yan LeCun </cite> 
 
 
DSL for forward and reverse mode automatic differentiation via a version of operator overloading.  

Port of [DiffSharp](https://github.com/DiffSharp/DiffSharp) to Haskell; currently a work in progress.



```haskell
let g a b = (a + b / a) / (D 2.0 :: D Float)
compute $ diff' (fixPoint g (D 1.2)) (D 25.0 :: D Float) 
-- (D 1.0, D 5.0), (D 1.0, D 0.1)
```
