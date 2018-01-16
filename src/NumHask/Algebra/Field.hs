{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE UndecidableInstances      #-}
-- | Field classes
module NumHask.Algebra.Field
  ( Semifield
  , Field
  , ExpField(..)
  -- , QuotientField(..)
  -- , BoundedField(..)
  -- , infinity
  -- , neginfinity
  -- , TrigField(..)
  ) where

import NumHask.Algebra.Additive
import NumHask.Algebra.Multiplicative
import NumHask.Algebra.Ring
import Protolude ( Double, Float, Bool)
import qualified Protolude as P
import Protolude (pure, ($))
import Core (D(..), Computation, MonOp(..), BinOp(..), Trace(..), DualTrace(..), Delta(..), monOp, binOp, p,t,r)

-- | A Semifield is a Field without Commutative Multiplication.
class (MultiplicativeInvertible a t, Ring a b t) =>
      Semifield a b t | a b -> t, a -> t, b -> t

instance Semifield (D Double) (D Double) Double

instance Semifield (Computation Double (D Double)) (D Double) Double

instance Semifield (D Double) (Computation Double (D Double)) Double

instance Semifield (D Float) (D Float) Float

instance Semifield (D Float) (Computation Float (D Float)) Float

instance Semifield (Computation Float (D Float)) (D Float) Float

instance Semifield (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Semifield (Computation Float (D Float)) (Computation Float (D Float)) Float

-- | A Field is a Ring plus additive invertible and multiplicative invertible operations.
--
-- A summary of the rules inherited from super-classes of Field
--
-- > zero + a == a
-- > a + zero == a
-- > (a + b) + c == a + (b + c)
-- > a + b == b + a
-- > a - a = zero
-- > negate a = zero - a
-- > negate a + a = zero
-- > a + negate a = zero
-- > one * a == a
-- > a * one == a
-- > (a * b) * c == a * (b * c)
-- > a * (b + c) == a * b + a * c
-- > (a + b) * c == a * c + b * c
-- > a * zero == zero
-- > zero * a == zero
-- > a * b == b * a
-- > a / a = one
-- > recip a = one / a
-- > recip a * a = one
-- > a * recip a = one
class (AdditiveGroup a b t, MultiplicativeGroup a b t, Ring a b t) =>
      Field a b t | a b -> t, a -> t, b -> t

instance Field (D Double) (D Double) Double

instance Field (Computation Double (D Double)) (D Double) Double

instance Field (D Double) (Computation Double (D Double)) Double

instance Field (D Float) (D Float) Float

instance Field (D Float) (Computation Float (D Float)) Float

instance Field (Computation Float (D Float)) (D Float) Float

instance Field (Computation Double (D Double)) (Computation Double (D Double)) Double

instance Field (Computation Float (D Float)) (Computation Float (D Float)) Float


data Log = Log
data Exp = Exp


-- | A hyperbolic field class
--
-- > sqrt . (**2) == identity
-- > log . exp == identity
-- > for +ive b, a != 0,1: a ** logBase a b ≈ b
class ( Field a a t
      ) =>
      ExpField a t | a -> t where
  exp :: a -> Computation t (D t)
  log :: a -> Computation t (D t)


logBase ::
     ( ExpField a t
     , ExpField b t
     , MultiplicativeGroup (Computation t (D t)) (Computation t (D t)) t
     )
  => a
  -> b
  -> Computation t (D t)
logBase a b = log b / log a


  
-- instance ExpField (Computation Double (D Double)) Double where
--   log a = do
--     aa <- a
--     monOp Log aa
--   exp a = do
--     aa <- a
--     monOp Exp aa

-- instance ExpField  (Computation Float (D Float)) Float where
--   log a = do
--     aa <- a
--     monOp Log aa
--   exp a = do
--     aa <- a
--     monOp Exp aa

-- instance ExpField  (D Double) Double where
--   log = monOp Log
--   exp = monOp Exp

-- instance ExpField   (D Float) Float where
--   log = monOp Log
--   exp = monOp Exp


-- sqrt ::
--      ( ExpField (Computation t (D t)) t
--      , ExpField a t
--      , MultiplicativeGroup a (Computation t (D t)) t
--      , MultiplicativeUnital a t
--      , MultiplicativeUnital (Computation t (D t)) t
--      , Additive a a t
--      )
--   => a
--   -> Computation t (D t)
-- sqrt a = do a ** (one / ( one + one))

(**) ::
     ( ExpField (Computation t (D t)) t
     , ExpField a t
     , ExpField b t
     , MultiplicativeGroup (Computation t (D t)) b t
     )
  => a
  -> b
  -> Computation t (D t)
(**) a b = exp (log a * b)

-- log10Val ::
--      ( ExpField (Computation t (D t)) t
--      , MultiplicativeUnital (Computation t (D t)) t
--      , MultiplicativeUnital (D t) t
--      , Additive (Computation t (D t)) (Computation t (D t)) t
--      , Additive ((D t)) (Computation t (D t)) t
--      )
--   => Computation t (D t)
-- log10Val = (log (ten))

-- ten :: ( MultiplicativeUnital (Computation t (D t)) t, Additive (Computation t (D t)) (Computation t (D t)) t) => Computation t (D t)
-- ten = sum [one, one, one, one, one, one, one, one, one, one]

-- | Exponentiation
-- >>> compute $ diff' (\x -> x + a) a
-- (D 6.0,D 1.0)
-- instance ( P.Floating a
--          , ExpField (D a) a
--          , MultiplicativeGroup (D a) (Computation a (D a)) a
--          , ExpField (Computation a (D a)) a
--          , MultiplicativeUnital (Computation a (D a)) a
--          , Additive  (D a) (Computation a (D a)) a
--          ) =>
--          MonOp Exp a where
--   {-# INLINE ff #-}
--   ff _ a = P.exp a
--   {-# INLINE fd #-}
--   fd _ a = exp a
--   {-# INLINE df #-}
--   df _ cp ap at =
--     at / (ap * (log10Val))

instance ( MultiplicativeGroup (D a) (D a) a) => Trace Exp a where
  pushEl (U _ a) dA = do
    cda <- (dA / (p a))
    P.pure [(X cda, a)]
  resetEl (U _ a ) = pure [a]



-- | quotient fields explode constraints if they allow for polymorphic integral types
--
-- > a - one < floor a <= a <= ceiling a < a + one
-- > round a == floor (a + one/(one+one))
-- class (Field a a t) =>
--       QuotientField a t | a -> t where
--   round :: a -> Computation t (D t)
--   ceiling :: a -> Computation t (D t)
--   floor :: a -> Computation t (D t)
--   (^^) :: a -> a -> Computation t (D t)

-- instance QuotientField Float where
--   round = P.round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField Double where
--   round = P.round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- | A bounded field includes the concepts of infinity and NaN, thus moving away from error throwing.
--
-- > one / zero + infinity == infinity
-- > infinity + a == infinity
-- > isNaN (infinity - infinity)
-- > isNaN (infinity / infinity)
-- > isNaN (nan + a)
-- > zero / zero != nan
--
-- Note the tricky law that, although nan is assigned to zero/zero, they are never-the-less not equal. A committee decided this.
-- class (Field a a t) =>
--       BoundedField a t | a -> t where
--   maxBound ::  Computation t (D t)
--   maxBound = one / zero
--   minBound ::  Computation t (D t)
--   minBound = negate (one / zero)
--   nan ::  Computation t (D t)
--   nan = zero / zero
--   isNaN :: a -> Bool

-- -- | prints as `Infinity`
-- infinity :: BoundedField a t =>  Computation t (D t)
-- infinity = maxBound

-- -- | prints as `-Infinity`
-- neginfinity :: BoundedField a t =>  Computation t (D t)
-- neginfinity = minBound

-- instance BoundedField Float where
--   isNaN = P.isNaN

-- instance BoundedField Double where
--   isNaN = P.isNaN

-- | todo: work out boundings for complex
-- as it stands now, complex is different eg
--

-- | Trigonometric Field
-- class (Field a a t) =>
--       TrigField a t | a -> t where
--   pi :: a
--   sin :: a -> Computation t (D t)
--   cos :: a -> Computation t (D t)
--   tan :: a -> Computation t (D t)
--   tan x = sin x / cos x
--   asin :: a -> Computation t (D t)
--   acos :: a -> Computation t (D t)
--   atan :: a -> Computation t (D t)
--   sinh :: a -> Computation t (D t)
--   cosh :: a -> Computation t (D t)
--   tanh :: a -> Computation t (D t)
--   tanh x = sinh x / cosh x
--   asinh :: a -> Computation t (D t)
--   acosh :: a -> Computation t (D t)
--   atanh :: a -> Computation t (D t)
  -- atan2 :: a -> a -> a
  -- atan2 y x
  --   | x P.> zero = atan (y / x)
  --   | x P.== zero P.&& y P.> zero = pi / (one + one)
  --   | x P.< one P.&& y P.> one = pi + atan (y / x)
  --   | (x P.<= zero P.&& y P.< zero) || (x P.< zero) =
  --     negate (atan2 (negate y) x)
  --   | y P.== zero = pi -- must be after the previous test on zero y
  --   | x P.== zero P.&& y P.== zero = y -- must be after the other double zero tests
  --   | P.otherwise = x + y -- x or y is a NaN, return a NaN (via +)

-- instance TrigField Double where
--   pi = P.pi
--   sin = P.sin
--   cos = P.cos
--   asin = P.asin
--   acos = P.acos
--   atan = P.atan
--   sinh = P.sinh
--   cosh = P.cosh
--   asinh = P.sinh
--   acosh = P.acosh
--   atanh = P.atanh

-- instance TrigField Float where
--   pi = P.pi
--   sin = P.sin
--   cos = P.cos
--   asin = P.asin
--   acos = P.acos
--   atan = P.atan
--   sinh = P.sinh
--   cosh = P.cosh
--   asinh = P.sinh
--   acosh = P.acosh
--   atanh = P.atanh
