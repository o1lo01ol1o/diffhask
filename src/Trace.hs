module Trace () where
import Core



data Add

instance Trace Add where

data TraceOp a =
    | Add (D a) (D a)
    | Add_Cons (D a)
    | Sub (D a)(D a)
    | Sub_Cons (D a)
    | Mul (D a) (D a)
    
