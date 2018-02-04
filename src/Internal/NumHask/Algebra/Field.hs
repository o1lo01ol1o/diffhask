{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies   #-}
-- | Field classes
module Internal.NumHask.Algebra.Field
  ( Semifield
  , Field
  , ExpField(..)
  --, QuotientField(..)
  , BoundedField(..)
  , infinity
  , neginfinity
  , TrigField(..)
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Multiplicative
import           Internal.NumHask.Algebra.Ring
import           Protolude                      (Bool, Double, Float)
import           Protolude                      (pure, ($), Show)
import qualified Protolude                      as P

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


data Log = Log deriving Show
data Exp = Exp deriving Show


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



instance ExpField (Computation Double (D Double)) Double where
  log a = do
    aa <- a
    monOp Log aa
  exp a = do
    aa <- a
    monOp Exp aa

instance ExpField  (Computation Float (D Float)) Float where
  log a = do
    aa <- a
    monOp Log aa
  exp a = do
    aa <- a
    monOp Exp aa

instance ExpField  (D Double) Double where
  log = monOp Log
  exp = monOp Exp

instance ExpField   (D Float) Float where
  log = monOp Log
  exp = monOp Exp


sqrt :: forall a t.
     ( ExpField (Computation t (D t)) t
     , ExpField a t
     , MultiplicativeGroup a (Computation t (D t)) t
     , MultiplicativeUnital a t
     , MultiplicativeUnital (Computation t (D t)) t
     , Additive a a t
     )
  => a
  -> Computation t (D t)
sqrt a =
  a **
  ((one :: Computation t (D t)) /
   ((one :: Computation t (D t)) + (one :: Computation t (D t))))

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

log10Val ::
     ( ExpField (Computation t (D t)) t
     , MultiplicativeUnital (Computation t (D t)) t
     , MultiplicativeUnital (D t) t
     , Additive (Computation t (D t)) (Computation t (D t)) t
     , Additive ((D t)) (Computation t (D t)) t
     )
  => Computation t (D t)
log10Val = log (ten)

ten :: forall t.
     ( MultiplicativeUnital (Computation t (D t)) t
     , Additive (Computation t (D t)) (Computation t (D t)) t
     )
  => Computation t (D t)
ten = sum $ P.replicate 10 (one :: Computation t (D t))

-- | Exponentiation
-- >>> compute $ diff' (\x -> x + ) a
-- (D 6.0,D 1.0)
instance ( P.Floating a
         , ExpField (D a) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeUnital (Computation a (D a)) a
         , Additive  (D a) (Computation a (D a)) a
         ) =>
         MonOp Exp a where
  {-# INLINE ff #-}
  ff _ a = P.exp a
  {-# INLINE fd #-}
  fd _ a = exp a
  {-# INLINE df #-}
  df _ cp ap at =
    at / (ap * (log10Val))

instance (ScalarInABox a, MultiplicativeGroup (D a) (D a) a) => Trace Exp a where
  pushEl (U _ a) dA = do
    cda <- (dA * (p a))
    P.pure [(X cda, X a)]
  resetEl (U _ a ) = pure [X a]


instance ( P.Floating a
         , ExpField (D a) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeUnital (Computation a (D a)) a
         , Additive  (D a) (Computation a (D a)) a
         ) =>
         MonOp Log a where
  {-# INLINE ff #-}
  ff _ a = P.log a
  {-# INLINE fd #-}
  fd _ a = log a
  {-# INLINE df #-}
  df _ cp ap at =
    at / ap

instance (ScalarInABox a, MultiplicativeGroup (D a) (D a) a) => Trace Log a where
  pushEl (U _ a) dA = do
    cda <- (dA / (p a))
    P.pure [(X cda, X a)]
  resetEl (U _ a ) = pure [X a]


-- TODO: QuotientFields are not differentiable and we lack a RealFrac (D a) instance.  Should just provide one.
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

-- instance QuotientField (D Float) Float where
--   round = monOp Round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField (D Double) Double where
--   round = monOp Round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField (Computation Double (D Double)) Double where
--   round a = do
--     ca <- a
--     monOp Round ca
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField  (Computation Float (D Float)) Float where
--   round = P.round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- data Round = Round deriving Show

-- data Ceiling = Ceiling deriving Show

-- data Floor = Floor deriving Show

-- instance ( AdditiveUnital (Computation a (D a)) a
--          , P.RealFrac a
--          , P.Integral a
--          , P.RealFrac (D a)
--          , P.Integral (Computation a (D a))
--          ) =>
--          MonOp Round a where
--   {-# INLINE ff #-}
--   ff _ a = P.round a
--   {-# INLINE fd #-}
--   fd _ a = P.round a
--   {-# INLINE df #-}
--   df _ cp ap at = (zero :: Computation a (D a))


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
class (Field a a t) =>
      BoundedField a t | a -> t where
  maxBound :: (a ~ D t) => Computation t a
  maxBound = (one :: D t) / (zero :: D t)
  minBound ::
       (a ~ D t, AdditiveInvertible (Computation t (D t)) t) => Computation t a
  minBound = negate ((one :: D t) / (zero :: D t))
  nan :: (a ~ D t) => Computation t a
  nan = (zero :: D t) / (zero :: D t)
  isNaN :: a -> Computation t Bool

-- -- | prints as `Infinity`
infinity :: (BoundedField a t, a ~ D t) => Computation t a
infinity = maxBound

-- -- | prints as `-Infinity`
neginfinity ::
     (BoundedField a t, a ~ D t, AdditiveInvertible (Computation t (D t)) t)
  => Computation t a
neginfinity = minBound

instance BoundedField (D Float) Float where
  isNaN = pure P.. P.isNaN P.. toNumeric P.. p 

instance BoundedField (D Double) Double where
  isNaN = pure P.. P.isNaN P.. toNumeric P.. p 

instance BoundedField (Computation Float (D Float)) Float where
  isNaN a = do
    ca <- a
    pure P.. P.isNaN P.. toNumeric $ p ca

instance BoundedField (Computation Double (D Double)) Double where
  isNaN a = do
    ca <- a
    pure P.. P.isNaN P.. toNumeric $ p ca


-- | Trigonometric Field
class ( Field a a t
      , ExpField a t
      , BoundedField (D t) t
      , ExpField (Computation t (D t)) t
      , Additive (D t) (D t) t
      , Additive a (D t) t
      , Additive (D t) (Computation t (D t)) t
      , Additive a (Computation t (D t)) t
      , AdditiveGroup a (D t) t
      , Additive (Computation t (D t)) (Computation t (D t)) t
      , MultiplicativeGroup (D t) (D t) t
      , MultiplicativeGroup (D t) (Computation t (D t)) t
      , MultiplicativeGroup (Computation t (D t)) (Computation t (D t)) t
      ) =>
      TrigField a t | a -> t where
  pi :: a
  sin :: a -> Computation t (D t)
  cos :: a -> Computation t (D t)
  tan :: a -> Computation t (D t)
  tan x = do
    sx <- sin x
    cx <- cos x
    sx / cx
  asin :: a -> Computation t (D t)
  acos :: a -> Computation t (D t)
  atan :: a -> Computation t (D t)
  sinh :: a -> Computation t (D t)
  cosh :: a -> Computation t (D t)
  tanh :: a -> Computation t (D t)
  tanh x = do
    sx <- sinh x
    cx <- cosh x
    sx / cx
  asinh :: a -> Computation t (D t)
  asinh z = log (z + sqrt ((one :: D t) + z ** ((one :: D t) + (one :: D t))))
  acosh :: a -> Computation t (D t)
  acosh z = log (z + sqrt (z + (one :: D t)) * sqrt (z - (one :: D t)))
  atanh :: a -> Computation t (D t)
  -- atan2 :: a -> a -> a --FIXME: implement in instances
  -- atan2 y x
  --   | x P.> zero = atan (y / x)
  --   | x P.== zero P.&& y P.> zero = pi / (one + one)
  --   | x P.< one P.&& y P.> one = pi + atan (y / x)
  --   | (x P.<= zero P.&& y P.< zero) || (x P.< zero) =
  --     negate (atan2 (negate y) x)
  --   | y P.== zero = pi -- must be after the previous test on zero y
  --   | x P.== zero P.&& y P.== zero = y -- must be after the other double zero tests
  --   | P.otherwise = x + y -- x or y is a NaN, return a NaN (via +)

data Sin = Sin deriving Show
data Cos = Cos deriving Show
data ASin = ASin deriving Show
data ACos = ACos deriving Show
data ATan = ATan deriving Show
data SinH = SinH deriving Show
data CosH = CosH deriving Show


instance TrigField (D Double) Double where
  pi = D P.pi
  sin = monOp Sin
  cos = monOp Cos
  asin = monOp ASin
  acos = monOp ACos
  atan = monOp ATan
  sinh = monOp SinH
  cosh = monOp CosH
  atanh z
    | z P.== zero = zero
    | z P.== one = infinity -- Other cases yeild complex numbers
    | P.otherwise =
      ((one :: D Double) / ((one :: D Double) + (one :: D Double))) *
      (log (z + (one :: D Double)) - log (z - (one :: D Double)))


instance TrigField (D Float) Float where
  pi = D P.pi
  sin = monOp Sin
  cos = monOp Cos
  asin = monOp ASin
  acos = monOp ACos
  atan = monOp ATan
  sinh = monOp SinH
  cosh = monOp CosH
  atanh z
    | z P.== zero = zero
    | z P.== one = infinity -- Other cases yeild complex numbers
    | P.otherwise =
      ((one :: D Float) / ((one :: D Float) + (one :: D Float))) *
      (log (z + (one :: D Float)) - log (z - (one :: D Float)))

instance TrigField (Computation Float (D Float)) Float where
  pi = pure $ D P.pi
  sin z = do
    cz <- z
    monOp Sin cz
  cos z = do
    cz <- z
    monOp Cos cz
  asin z = do
    cz <- z
    monOp ASin cz
  acos z = do
    cz <- z
    monOp ACos cz
  atan z = do
    cz <- z
    monOp ATan cz
  sinh z = do
    cz <- z
    monOp SinH cz
  cosh z = do
    cz <- z
    monOp Cos cz
  atanh z = do
    cz <- z
    case cz of
      z
        | z P.== zero -> zero
        | z P.== one -> infinity -- Other cases yeild complex numbers
        | P.otherwise ->
          ((one :: D Float) / ((one :: D Float) + (one :: D Float))) *
          (log (z + (one :: D Float)) - log (z - (one :: D Float)))

instance TrigField (Computation Double (D Double)) Double where
  pi = pure $ D P.pi
  sin z = do
    cz <- z
    monOp Sin cz
  cos z = do
    cz <- z
    monOp Cos cz
  asin z = do
    cz <- z
    monOp ASin cz
  acos z = do
    cz <- z
    monOp ACos cz
  atan z = do
    cz <- z
    monOp ATan cz
  sinh z = do
    cz <- z
    monOp SinH cz
  cosh z = do
    cz <- z
    monOp Cos cz
  atanh z = do
    cz <- z
    case cz of
      z
        | z P.== zero -> zero
        | z P.== one -> infinity -- Other cases yeild complex numbers
        | P.otherwise ->
          ((one :: D Double) / ((one :: D Double) + (one :: D Double))) *
          (log (z + (one :: D Double)) - log (z - (one :: D Double)))


instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , MonOp Cos a
         , Trace Cos a
         ) =>
         MonOp Sin a where
  {-# INLINE ff #-}
  ff _ a = P.sin a
  {-# INLINE fd #-}
  fd _ a = monOp Sin a
  {-# INLINE df #-}
  df _ _ ap at = at * (monOp Cos ap)

instance (ScalarInABox a, TrigField (D a) a, Multiplicative (D a) (Computation a (D a)) a) =>
         Trace Sin a where
  pushEl (U _ a) dA = do
    d <- dA * (cos (p a))
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]


instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , Multiplicative (Computation a (D a)) (Computation a (D a)) a
         , MonOp Cos a
         , Trace Cos a
         ) =>
         MonOp Cos a where
  {-# INLINE ff #-}
  ff _ a = P.sin a
  {-# INLINE fd #-}
  fd _ a = monOp Sin a
  {-# INLINE df #-}
  df _ _ ap at = at * (monOp Cos ap)

instance (ScalarInABox a, AdditiveInvertible (Computation a (D a)) a
         , TrigField (D a) a
         , Multiplicative (D a) (Computation a (D a)) a
         ) =>
         Trace Cos a where
  pushEl (U _ a) dA = do
    d <- dA * (negate $ sin (p a))
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]


instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , Multiplicative (Computation a (D a)) (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , AdditiveInvertible (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         ) =>
         MonOp ASin a where
  {-# INLINE ff #-}
  ff _ a = P.asin a
  {-# INLINE fd #-}
  fd _ a = monOp ASin a
  {-# INLINE df #-}
  df _ _ ap at = at / sqrt ((one :: D a) - ap * ap)

instance (ScalarInABox a, AdditiveInvertible (Computation a (D a)) a
         , TrigField (D a) a
         , Multiplicative (D a) (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         ) =>
         Trace ASin a where
  pushEl (U _ a) dA = do
    d <- dA / (sqrt ((one :: D a) - (p a * p a)))
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]

instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , Multiplicative (Computation a (D a)) (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , AdditiveInvertible (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         ) =>
         MonOp ACos a where
  {-# INLINE ff #-}
  ff _ a = P.acos a
  {-# INLINE fd #-}
  fd _ a = monOp ACos a
  {-# INLINE df #-}
  df _ _ ap at = negate $ at / sqrt ((one :: D a) - ap * ap)

instance (ScalarInABox a, AdditiveInvertible (Computation a (D a)) a
         , TrigField (D a) a
         , Multiplicative (D a) (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         ) =>
         Trace ACos a where
  pushEl (U _ a) dA = do
    d <- negate $ dA / (sqrt ((one :: D a) - (p a * p a)))
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]


instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , Multiplicative (Computation a (D a)) (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , AdditiveInvertible (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         ) =>
         MonOp ATan a where
  {-# INLINE ff #-}
  ff _ a = P.atan a
  {-# INLINE fd #-}
  fd _ a = monOp ATan a
  {-# INLINE df #-}
  df _ _ ap at = at / sqrt ((one :: D a) + ap * ap)

instance (ScalarInABox a, AdditiveInvertible (Computation a (D a)) a
         , TrigField (D a) a
         , Multiplicative (D a) (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         ) =>
         Trace ATan a where
  pushEl (U _ a) dA = do
    d <- dA / (sqrt ((one :: D a) + (p a * p a)))
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]

instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , Multiplicative (Computation a (D a)) (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , AdditiveInvertible (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         ) =>
         MonOp SinH a where
  {-# INLINE ff #-}
  ff _ a = P.sinh a
  {-# INLINE fd #-}
  fd _ a = monOp SinH a
  {-# INLINE df #-}
  df _ _ ap at = at * (cosh ap)

instance (ScalarInABox a, AdditiveInvertible (Computation a (D a)) a
         , TrigField (D a) a
         , Multiplicative (D a) (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         ) =>
         Trace SinH a where
  pushEl (U _ a) dA = do
    d <- dA * (cosh $ p a)
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]

instance (ScalarInABox a, TrigField (D a) a
         , P.Floating a
         , Multiplicative (D a) (Computation a (D a)) a
         , Multiplicative (Computation a (D a)) (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         , AdditiveInvertible (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         ) =>
         MonOp CosH a where
  {-# INLINE ff #-}
  ff _ a = P.cosh a
  {-# INLINE fd #-}
  fd _ a = monOp CosH a
  {-# INLINE df #-}
  df _ _ ap at = at * (sinh ap)

instance (ScalarInABox a, AdditiveInvertible (Computation a (D a)) a
         , TrigField (D a) a
         , Multiplicative (D a) (Computation a (D a)) a
         , AdditiveGroup (D a) (Computation a (D a)) a
         , ExpField (Computation a (D a)) a
         , MultiplicativeGroup (D a) (Computation a (D a)) a
         ) =>
         Trace CosH a where
  pushEl (U _ a) dA = do
    d <- dA * (sinh $ p a)
    pure [(X d, X a)]
  resetEl (U _ a) = pure [X a]

