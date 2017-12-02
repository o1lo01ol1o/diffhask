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
    | Mul_D_DCons            of D * D
    | Div_D_D                of D * D
    | Div_D_DCons            of D * D
    | Div_DCons_D            of D * D
    | Pow_D_D                of D * D
    | Pow_D_DCons            of D * D
    | Pow_DCons_D            of D * D
    | Atan2_D_D              of D * D
    | Atan2_D_DCons          of D * D
    | Atan2_DCons_D          of D * D
    | Log_D                  of D
    | Log10_D                of D
    | Exp_D                  of D
    | Sin_D                  of D
    | Cos_D                  of D
    | Tan_D                  of D
    | Neg_D                  of D
    | Sqrt_D                 of D
    | Sinh_D                 of D
    | Cosh_D                 of D
    | Tanh_D                 of D
    | Asin_D                 of D
    | Acos_D                 of D
    | Atan_D                 of D
    | Abs_D                  of D
    | Sign_D                 of D
    | Floor_D                of D
    | Ceil_D                 of D
    | Round_D                of D
    | Mul_Dot_DV_DV          of DV * DV
    | Mul_Dot_DV_DVCons      of DV * DV
    | Sum_DV                 of DV
    | L1Norm_DV              of DV
    | L2NormSq_DV            of DV
    | L2Norm_DV              of DV
    | Item_DV                of DV * int
    | Sum_DM                 of DM
    | Item_DM                of DM * int * int
    | ReLU_D                 of D
    | Sigmoid_D              of D
    | LogSumExp_DV           of DV
    | FixedPoint_D           of D * D * D * D
