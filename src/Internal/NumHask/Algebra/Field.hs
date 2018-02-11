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
  -- , infinity
  -- , neginfinity
  , TrigField(..)
  , Log(..)
  , Exp(..)
  , Sin(..)
  , Cos(..)
  , ASin(..)
  , ACos(..)
  , ATan(..)
  , SinH(..)
  , CosH(..)
  ) where

import           Internal.Internal
import           Internal.NumHask.Algebra.Additive
import           Internal.NumHask.Algebra.Multiplicative
import           Internal.NumHask.Algebra.Ring
import           Protolude                      (Bool, Double, Float)
import           Protolude                      (pure, ($), Show)
import qualified Protolude                      as P

data Log = Log deriving Show
data Exp = Exp deriving Show

data Sin = Sin deriving Show
data Cos = Cos deriving Show
data ASin = ASin deriving Show
data ACos = ACos deriving Show
data ATan = ATan deriving Show
data SinH = SinH deriving Show
data CosH = CosH deriving Show

-- | A Semifield is a Field without Commutative Multiplication.
class (MultiplicativeInvertible a r t, Ring a b r t) =>
      Semifield a b r t

instance Semifield (D r Double) (D r Double) r Double

instance Semifield (Computation r Double (D r Double)) (D r Double) r Double

instance Semifield (D r Double) (Computation r Double (D r Double)) r Double

instance Semifield (D r Float) (D r Float) r Float

instance Semifield (D r Float) (Computation r Float (D r Float)) r Float

instance Semifield (Computation r Float (D r Float)) (D r Float) r Float

instance Semifield (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance Semifield (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float

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
class (AdditiveGroup a b r t, MultiplicativeGroup a b r t, Ring a b r t) =>
      Field a b r t

instance Field (D r Double) (D r Double) r Double

instance Field (Computation r Double (D r Double)) (D r Double) r Double

instance Field (D r Double) (Computation r Double (D r Double)) r Double

instance Field (D r Float) (D r Float) r Float

instance Field (D r Float) (Computation r Float (D r Float)) r Float

instance Field (Computation r Float (D r Float)) (D r Float) r Float

instance Field (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double

instance Field (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float





-- | A hyperbolic field class
--
-- > sqrt . (**2) == identity
-- > log . exp == identity
-- > for +ive b, a != 0,1: a ** logBase a b ≈ b
class ( Field a a r t
      ) =>
      ExpField a r t where
  exp :: a -> Computation r t (D r t)
  log :: a -> Computation r t (D r t)


logBase ::
     ( ExpField a r t
     , ExpField b r t
     , MultiplicativeGroup (Computation r t (D r t)) (Computation r t (D r t)) r t
     )
  => a
  -> b
  -> Computation r t (D r t)
logBase a b = log b / log a



instance ExpField (Computation r Double (D r Double)) r Double where
  log a = do
    aa <- a
    monOp Log aa
  exp a = do
    aa <- a
    monOp Exp aa

instance ExpField  (Computation r Float (D r Float)) r Float where
  log a = do
    aa <- a
    monOp Log aa
  exp a = do
    aa <- a
    monOp Exp aa

instance ExpField  (D r Double) r Double where
  log = monOp Log
  exp = monOp Exp

instance ExpField   (D r Float) r Float where
  log = monOp Log
  exp = monOp Exp


sqrt ::
     forall a r t.
     ( ExpField a r t
     , ExpField (Computation r t (D r t)) r t
     , MultiplicativeUnital a r t
     , Additive a a r t
     , MultiplicativeGroup a (Computation r t (D r t)) r t
     )
  => a
  -> Computation r t (D r t)
sqrt a = a ** ((one :: a) / ((one :: a) + (one :: a)))

(**) ::
     ( ExpField a r t
     , ExpField (Computation r t (D r t)) r t
     , Multiplicative (Computation r t (D r t)) b r t
     , ExpField b r t
     )
  => a
  -> b
  -> Computation r t (D r t)
(**) a b = exp (log a * b)

log10Val :: forall r t.
     (
     ExpField (Computation r t (D r t)) r t
     , MultiplicativeUnital (Computation r t (D r t)) r t
     , MultiplicativeUnital (D r t)r t
     , Additive (Computation r t (D r t)) (Computation r t (D r t)) r t
     , Additive (D r t) (Computation r t (D r t))r t
     )
  => Computation r t (D r t)
log10Val = log ten

ten :: forall t r.
     (
       MultiplicativeUnital (Computation r t (D r t)) r t
     , Additive (Computation r t (D r t)) (Computation r t (D r t)) r t
     )
  => Computation r t (D r t)
ten = sum $ P.replicate 10 (one :: Computation r t (D r t))

-- | Exponentiation
-- >>> compute $ diff' (\x -> x + ) a
-- (D 6.0,D 1.0)
instance ( P.Floating t
         , ExpField (D r t) r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t)) r t
         , MultiplicativeUnital (Computation r t (D r t)) r t
         , Additive  (D r t) (Computation r t (D r t)) r t
         ) =>
         MonOp Exp r t where
  {-# INLINE fd #-}
  fd _ a = exp a
  {-# INLINE df #-}
  df _ cp ap at =
    at / (ap * (log10Val))
instance ( P.Floating t
 
         
         ) =>
         FfMon Exp t where
  {-# INLINE ff #-}
  ff _ a = P.exp a

instance (MultiplicativeGroup (D r t) (D r t) r t) => Trace Exp r t where
  pushEl (U _ a) dA = do
    cda <- (dA * (p a))
    P.pure [(cda, a)]
  resetEl (U _ a ) = pure [a]


instance ( P.Floating t
         , ExpField (D r t) r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t)) r t
         , ExpField (Computation r t (D r t)) r t
         , MultiplicativeUnital (Computation r t (D r t)) r t
         , Additive  (D r t) (Computation r t (D r t)) r t
         ) =>
         MonOp Log r t where

  {-# INLINE fd #-}
  fd _ a = log a
  {-# INLINE df #-}
  df _ cp ap at =
    at / ap

instance ( P.Floating a
        
         ) =>
         FfMon Log a where
   {-# INLINE ff #-}
   ff _ a = P.log a

instance (MultiplicativeGroup (D r t) (D r t) r t) => Trace Log r t where
  pushEl (U _ a) dA = do
    cda <- (dA / (p a))
    P.pure [(cda, a)]
  resetEl (U _ a ) = pure [a]


-- TODO: QuotientFields are not differentiable and we lack a RealFrac (D r t) instance. 
-- | quotient fields explode constraints if they allow for polymorphic integral types
--
-- > a - one < floor a <= a <= ceiling a < a + one
-- > round a == floor (a + one/(one+one))
-- class (Field a a t) =>
--       QuotientField a t | a -> t where
--   round :: a -> Computation r t (D r t)
--   ceiling :: a -> Computation r t (D r t)
--   floor :: a -> Computation r t (D r t)
--   (^^) :: a -> a -> Computation r t (D r t)

-- instance QuotientField (D r Float) Float where
--   round = monOp Round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField (D r Double) Double where
--   round = monOp Round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField (Computation r Double (D r Double)) Double where
--   round a = do
--     ca <- a
--     monOp Round ca
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- instance QuotientField  (Computation r Float (D r Float)) Float where
--   round = P.round
--   ceiling = P.ceiling
--   floor = P.floor
--   (^^) = (P.^^)

-- data Round = Round deriving Show

-- data Ceiling = Ceiling deriving Show

-- data Floor = Floor deriving Show

-- instance ( AdditiveUnital (Computation r t (D r t)) a
--          , P.RealFrac a
--          , P.Integral a
--          , P.RealFrac (D r t)
--          , P.Integral (Computation r t (D r t))
--          ) =>
--          MonOp Round a where
--   {-# INLINE ff #-}
--   ff _ a = P.round a
--   {-# INLINE fd #-}
--   fd _ a = P.round a
--   {-# INLINE df #-}
--   df _ cp ap at = (zero :: Computation r t (D r t))


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
class (Field a a r t) =>
      BoundedField a r t where
  -- maxBound :: (D r t ~ D r t) => Computation r t a
  -- maxBound = ((one :: D r t) / (zero :: D r t))
  -- minBound :: (D r t ~ D r t) => Computation r t a
  -- minBound = negate (one / zero)
  -- nan :: (D r t ~ D r t) => Computation r t a
  -- nan = (zero / zero)
  -- isNaN :: a -> Computation r t Bool

-- -- | prints as `Infinity`
-- infinity :: (BoundedField a, a ~ D r t) =>  Computation r t a
-- infinity = maxBound

-- -- | prints as `-Infinity`
-- neginfinity ::
--      (BoundedField a, a ~ D r t, AdditiveInvertible (Computation r t (D r t)))
--   =>  Computation r t a
-- neginfinity = minBound
--TODO: toNumeric function need
-- instance BoundedField (D r Float) Float where
--   isNaN = pure P.. P.isNaN P.. toNumeric P.. p 

-- instance BoundedField (D r Double) Double where
--   isNaN = pure P.. P.isNaN P.. toNumeric P.. p 

-- instance BoundedField (Computation r Float (D r Float)) Float where
--   isNaN a = do
--     ca <- a
--     pure P.. P.isNaN P.. toNumeric $ p ca

-- instance BoundedField (Computation r Double (D r Double)) Double where
--   isNaN a = do
--     ca <- a
--     pure P.. P.isNaN P.. toNumeric $ p ca


-- | Trigonometric Field
class ( Field a a r t
      , ExpField a  r t
      , BoundedField (D r t) r t
      , ExpField (Computation r t (D r t)) r t
      , Additive (D r t) (D r t) r t
      , Additive a (D r t) r t
      , Additive (D r t) (Computation r t (D r t)) r t
      , Additive a (Computation r t (D r t)) r t
      , AdditiveGroup a (D r t) r t
      , Additive(Computation r t (D r t))(Computation r t (D r t)) r t
      , MultiplicativeGroup (D r t)(D r t) r t
      , MultiplicativeGroup (D r t) (Computation r t (D r t)) r t
      , MultiplicativeGroup (Computation r t (D r t)) (Computation r t (D r t)) r t
      , MultiplicativeUnital ((D r t ))r t
      , ExpField (Computation r t (D r t)) r t
      ) =>
      TrigField a r t where
  pi :: a
  sin :: a -> Computation r t (D r t)
  cos :: a -> Computation r t (D r t)
  tan :: a -> Computation r t (D r t)
  tan x = do
    sx <- sin x
    cx <- cos x
    sx / cx
  asin :: a -> Computation r t (D r t)
  acos :: a -> Computation r t (D r t)
  atan :: a -> Computation r t (D r t)
  sinh :: a -> Computation r t (D r t)
  cosh :: a -> Computation r t (D r t)
  tanh :: a -> Computation r t (D r t)
  tanh x = do
    sx <- sinh x
    cx <- cosh x
    sx / cx

  -- asinh :: ((D r t )  ~ D r t) => a -> Computation r t (D r t)
  -- asinh z = log (z + sqrt ((one :: D r t) + z ** ((one :: D r t) + (one :: D r t))))

  asinh ::  a -> Computation r t (D r t)
  -- asinh z = log (z + sqrt ((one :: D r t) + z ** ((one :: D r t) + (one :: D r t))))


  acosh :: a -> Computation r t (D r t)
  -- acosh z = log (z + sqrt (z + (one :: D r t)) * sqrt (z - (one :: D r t)))
  atanh :: a -> Computation r t (D r t)
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




instance ( BoundedField (D r Double) r Double
         , ExpField (Computation r Double (D r Double)) r Double
         , Additive ((D r Double)) ((D r Double)) r Double
         , Additive (D r Double) ((D r Double)) r Double
         , Additive ((D r Double)) (Computation r Double (D r Double)) r Double
         , Additive (D r Double) (Computation r Double (D r Double)) r Double
         , AdditiveGroup (D r Double) ((D r Double)) r Double
         , Additive (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double
         , MultiplicativeGroup ((D r Double)) ((D r Double)) r Double
         , MultiplicativeGroup ((D r Double)) (Computation r Double (D r Double)) r Double
         , MultiplicativeGroup (Computation r Double (D r Double)) (Computation r Double (D r Double)) r Double
         , MultiplicativeUnital (((D r Double))) r Double
         ) =>
         TrigField (D r Double) r Double where
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
    -- | z P.== one = infinity -- Other cases yeild complex numbers
    | P.otherwise =
      ((one :: D r Double) / ((one :: D r Double) + (one :: D r Double))) *
      (log (z + (one :: D r Double)) - log (z - (one :: D r Double)))


instance (BoundedField (D r Float) r Float
         , ExpField (Computation r Float (D r Float)) r Float
         , Additive (D r Float) (D r Float) r Float
         , Additive (D r Float) (D r Float) r Float
         , Additive (D r Float) (Computation r Float (D r Float)) r Float
         , Additive (D r Float) (Computation r Float (D r Float)) r Float
         , AdditiveGroup (D r Float) (D r Float) r Float
         , Additive (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float
         , MultiplicativeGroup (D r Float) (D r Float) r Float
         , MultiplicativeGroup (D r Float) (Computation r Float (D r Float)) r Float
         , MultiplicativeGroup (Computation r Float (D r Float)) (Computation r Float (D r Float)) r Float
         , MultiplicativeUnital ((D r Float)) r Float) => TrigField (D r Float) r Float where
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
    -- | z P.== one = infinity -- Other cases yeild complex numbers
    | P.otherwise =
      ((one :: D r Float) / ((one :: D r Float) + (one :: D r Float))) *
      (log (z + (one :: D r Float)) - log (z - (one :: D r Float)))


instance ( BoundedField (D r t)  r t
         , ExpField (Computation r t (D r t)) r t
         , Additive (D r t) (D r t) r t
         , Additive a (D r t) r t
         , Additive (D r t) (Computation r t (D r t)) r t
         , Additive a (Computation r t (D r t)) r t
         , AdditiveGroup a (D r t) r t
         , Additive (Computation r t (D r t)) (Computation r t (D r t)) r t
         , MultiplicativeGroup (D r t) (D r t) r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t)) r t
         , MultiplicativeGroup (Computation r t (D r t)) (Computation r t (D r t)) r t
         , MultiplicativeUnital ((D r t)) r t
         , ExpField (Computation r t (D r t)) r t
         , a ~ Computation r Double (D r Double)
         , t ~ Double
         ) =>
         TrigField (Computation r Double (D r Double)) r Double where
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
        -- | z P.== one -> infinity -- Other cases yeild complex numbers
        | P.otherwise ->
          ((one :: D r Double) / ((one :: D r Double) + (one :: D r Double))) *
          (log (z + (one :: D r Double)) - log (z - (one :: D r Double)))

instance ( BoundedField (D r t)  r t
         , ExpField (Computation r t (D r t))  r t
         , Additive (D r t) (D r t)  r t
         , Additive a (D r t) r t
         , Additive (D r t) (Computation r t (D r t)) r t
         , Additive a (Computation r t (D r t)) r t
         , AdditiveGroup a (D r t) r t
         , Additive (Computation r t (D r t)) (Computation r t (D r t)) r t
         , MultiplicativeGroup (D r t) (D r t) r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t)) r t
         , MultiplicativeGroup (Computation r t (D r t)) (Computation r t (D r t)) r t
         , MultiplicativeUnital ((D r t)) r t
         , ExpField (Computation r t (D r t)) r t
         , a ~ Computation r Float (D r Float)
         , t ~ Float
         ) =>
         TrigField (Computation r Float (D r Float)) r Float where
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
        -- | z P.== one -> infinity -- Other cases yeild complex numbers
        | P.otherwise ->
          ((one :: D r Float) / ((one :: D r Float) + (one :: D r Float))) *
          (log (z + (one :: D r Float)) - log (z - (one :: D r Float)))

instance (TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t)) r t
         , MonOp Cos r t
         , Trace Cos r t
         ) =>
         MonOp Sin r t where

  {-# INLINE fd #-}
  fd _ a = monOp Sin a
  {-# INLINE df #-}
  df _ _ ap at = at * (monOp Cos ap)

instance (
         P.Floating a
         ) =>
         FfMon Sin a where
    {-# INLINE ff #-}
    ff _ a = P.sin a
    
instance (TrigField (D r t)  r t, Multiplicative (D r t) (Computation r t (D r t))  r t) =>
         Trace Sin r t where
  pushEl (U _ a) dA = do
    d <- dA * (cos (p a))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]


instance (TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , Multiplicative (Computation r t (D r t)) (Computation r t (D r t))  r t
         , MonOp Cos r t
         , Trace Cos r t
         ) =>
         MonOp Cos r t where

  {-# INLINE fd #-}
  fd _ a = monOp Sin a
  {-# INLINE df #-}
  df _ _ ap at = at * (monOp Cos ap)

instance (P.Floating a
         ) =>
         FfMon Cos a where
  {-# INLINE ff #-}
  ff _ a = P.sin a

instance (AdditiveInvertible (Computation r t (D r t))  r t
         , TrigField (D r t)  r t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         ) =>
         Trace Cos r t where
  pushEl (U _ a) dA = do
    d <- dA * (negate $ sin (p a))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]


instance (TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , Multiplicative (Computation r t (D r t)) (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         , AdditiveInvertible (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t)) r t
         ) =>
         MonOp ASin r t where

  {-# INLINE fd #-}
  fd _ a = monOp ASin a
  {-# INLINE df #-}
  df _ _ ap at = at / sqrt ((one :: D r t) - ap * ap)

instance (P.Floating a) => FfMon ASin a where
  {-# INLINE ff #-}
  ff _ a = P.asin a

instance (AdditiveInvertible (Computation r t (D r t))  r t
         , TrigField (D r t)  r t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         Trace ASin r t where
  pushEl (U _ a) dA = do
    d <- dA / (sqrt ((one :: D r t) - (p a * p a)))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

instance (TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , Multiplicative (Computation r t (D r t)) (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         , AdditiveInvertible (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         MonOp ACos r t where

  {-# INLINE fd #-}
  fd _ a = monOp ACos a
  {-# INLINE df #-}
  df _ _ ap at = negate $ at / sqrt ((one :: D r t) - ap * ap)

instance (P.Floating a) => FfMon ACos a where
  {-# INLINE ff #-}
  ff _ a = P.acos a

instance (AdditiveInvertible (Computation r t (D r t))  r t
         , TrigField (D r t)  r t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         Trace ACos r t where
  pushEl (U _ a) dA = do
    d <- negate $ dA / (sqrt ((one :: D r t) - (p a * p a)))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]


instance (TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , Multiplicative (Computation r t (D r t)) (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         , AdditiveInvertible (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         MonOp ATan r t where

  {-# INLINE fd #-}
  fd _ a = monOp ATan a
  {-# INLINE df #-}
  df _ _ ap at = at / sqrt ((one :: D r t) + ap * ap)

instance (P.Floating a) => FfMon ATan a where
  {-# INLINE ff #-}
  ff _ a = P.atan a

instance (AdditiveInvertible (Computation r t (D r t))  r t
         , TrigField (D r t)   r t
         , Multiplicative (D r t) (Computation r t (D r t))   r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         Trace ATan r t where
  pushEl (U _ a) dA = do
    d <- dA / (sqrt ((one :: D r t) + (p a * p a)))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

instance ( TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , Multiplicative (Computation r t (D r t)) (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         , AdditiveInvertible (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         MonOp SinH r t where

  {-# INLINE fd #-}
  fd _ a = monOp SinH a
  {-# INLINE df #-}
  df _ _ ap at = at * (cosh ap)

instance (P.Floating a) => FfMon SinH a where
  {-# INLINE ff #-}
  ff _ a = P.sinh a

instance (AdditiveInvertible (Computation r t (D r t))  r t
         , TrigField (D r t)  r t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         Trace SinH r t where
  pushEl (U _ a) dA = do
    d <- dA * (cosh $ p a)
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

instance (TrigField (D r t)  r t
         , P.Floating t
         , Multiplicative (D r t) (Computation r t (D r t))  r t
         , Multiplicative (Computation r t (D r t)) (Computation r t (D r t))  r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t))  r t
         , AdditiveInvertible (Computation r t (D r t))  r t
         , ExpField (Computation r t (D r t))  r t
         , AdditiveGroup (D r t) (Computation r t (D r t))  r t
         ) =>
         MonOp CosH r t where

  {-# INLINE fd #-}
  fd _ a = monOp CosH a
  {-# INLINE df #-}
  df _ _ ap at = at * (sinh ap)

instance (P.Floating a ) => FfMon CosH a where
  {-# INLINE ff #-}
  ff _ a = P.cosh a

instance ( AdditiveInvertible (Computation r t (D r t)) r t
         , TrigField (D r t) r t
         , Multiplicative (D r t) (Computation r t (D r t)) r t
         , AdditiveGroup (D r t) (Computation r t (D r t)) r t
         , ExpField (Computation r t (D r t)) r t
         , MultiplicativeGroup (D r t) (Computation r t (D r t)) r t
         ) =>
         Trace CosH r t where
  pushEl (U _ a) dA = do
    d <- dA * (sinh $ p a)
    pure [(d, a)]
  resetEl (U _ a) = pure [a]
