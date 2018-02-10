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
class (MultiplicativeInvertible a, Ring a b) =>
      Semifield a b

instance Semifield (D r Double) (D r Double)

instance Semifield (Computation r Double (D r Double)) (D r Double) 

instance Semifield (D r Double) (Computation r Double (D r Double)) 

instance Semifield (D r Float) (D r Float) 

instance Semifield (D r Float) (Computation r Float (D r Float)) 

instance Semifield (Computation r Float (D r Float)) (D r Float) 

instance Semifield (Computation r Double (D r Double)) (Computation r Double (D r Double)) 

instance Semifield (Computation r Float (D r Float)) (Computation r Float (D r Float)) 

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
class (AdditiveGroup a b, MultiplicativeGroup a b, Ring a b) =>
      Field a b 

instance Field (D r Double) (D r Double) 

instance Field (Computation r Double (D r Double)) (D r Double) 

instance Field (D r Double) (Computation r Double (D r Double)) 

instance Field (D r Float) (D r Float) 

instance Field (D r Float) (Computation r Float (D r Float)) 

instance Field (Computation r Float (D r Float)) (D r Float) 

instance Field (Computation r Double (D r Double)) (Computation r Double (D r Double)) 

instance Field (Computation r Float (D r Float)) (Computation r Float (D r Float)) 





-- | A hyperbolic field class
--
-- > sqrt . (**2) == identity
-- > log . exp == identity
-- > for +ive b, a != 0,1: a ** logBase a b ≈ b
class ( Field a a
      ) =>
      ExpField a where
  exp :: a -> CodomainU a
  log :: a -> CodomainU a


logBase ::
     ( ExpField a 
     , ExpField b 
     -- , MultiplicativeGroup (Computation r a (D r a)) (Computation r a (D r a))
     )
  => a
  -> b
  -> CodomainB a b
logBase a b = log b / log a



instance ExpField (Computation r Double (D r Double)) where
  log a = do
    aa <- a
    monOp Log aa
  exp a = do
    aa <- a
    monOp Exp aa

instance ExpField  (Computation r Float (D r Float)) where
  log a = do
    aa <- a
    monOp Log aa
  exp a = do
    aa <- a
    monOp Exp aa

instance ExpField  (D r Double) where
  log = monOp Log
  exp = monOp Exp

instance ExpField   (D r Float) where
  log = monOp Log
  exp = monOp Exp


sqrt :: forall a.
     ( -- ExpField (Computation r t (D r t)) 
      ExpField a 
     --, MultiplicativeGroup a (Computation r t (D r t)) 
     , MultiplicativeUnital a 
     --, MultiplicativeUnital (Computation r t (D r t)) 
     , Additive a a 
     )
  => a
  -> CodomainU a
sqrt a =
  a **
  ((one :: Computation r t (D r t)) /
   ((one :: Computation r t (D r t)) + (one :: Computation r t (D r t))))

(**) ::
     ( -- ExpField (Computation r t (D r t)) 
      ExpField a 
     , ExpField b 
     --, MultiplicativeGroup (Computation r t (D r t)) b 
     )
  => a
  -> b
  -> CodomainU a
(**) a b = exp (log a * b)

log10Val :: forall r t.
     (
     ExpField (Computation r t (D r t)) 
     , MultiplicativeUnital (Computation r t (D r t)) 
     , MultiplicativeUnital (D r t)
     , Additive (Computation r t (D r t)) (Computation r t (D r t)) 
     , Additive (D r t) (Computation r t (D r t))
     )
  => CodomainU (D r t)
log10Val = log ten

ten :: forall t r.
     (
       MultiplicativeUnital (Computation r t (D r t)) 
     , Additive (Computation r t (D r t)) (Computation r t (D r t)) 
     )
  => CodomainU (D r t)
ten = sum $ P.replicate 10 (one :: Computation r t (D r t))

-- | Exponentiation
-- >>> compute $ diff' (\x -> x + ) a
-- (D 6.0,D 1.0)
instance ( P.Floating a
         , ExpField (D r a)
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a))
         , MultiplicativeUnital (Computation r a (D r a))
         , Additive  (D r a) (Computation r a (D r a))
         ) =>
         MonOp Exp r a where
  {-# INLINE fd #-}
  fd _ a = exp a
  {-# INLINE df #-}
  df _ cp ap at =
    at / (ap * (log10Val))
instance ( P.Floating a
 
         
         ) =>
         FfMon Exp a where
  {-# INLINE ff #-}
  ff _ a = P.exp a

instance (MultiplicativeGroup (D r a) (D r a)) => Trace Exp r a where
  pushEl (U _ a) dA = do
    cda <- (dA * (p a))
    P.pure [(cda, a)]
  resetEl (U _ a ) = pure [a]


instance ( P.Floating a
         , ExpField (D r a)
         , MultiplicativeGroup (D r a) (Computation r a (D r a))
         , ExpField (Computation r a (D r a))
         , MultiplicativeUnital (Computation r a (D r a))
         , Additive  (D r a) (Computation r a (D r a)) 
         ) =>
         MonOp Log r a where

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

instance (MultiplicativeGroup (D r a) (D r a)) => Trace Log r a where
  pushEl (U _ a) dA = do
    cda <- (dA / (p a))
    P.pure [(cda, a)]
  resetEl (U _ a ) = pure [a]


-- TODO: QuotientFields are not differentiable and we lack a RealFrac (D r a) instance. 
-- | quotient fields explode constraints if they allow for polymorphic integral types
--
-- > a - one < floor a <= a <= ceiling a < a + one
-- > round a == floor (a + one/(one+one))
-- class (Field a a t) =>
--       QuotientField a t | a -> t where
--   round :: a -> CodomainU a
--   ceiling :: a -> CodomainU a
--   floor :: a -> CodomainU a
--   (^^) :: a -> a -> CodomainU a

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

-- instance ( AdditiveUnital (Computation r a (D r a)) a
--          , P.RealFrac a
--          , P.Integral a
--          , P.RealFrac (D r a)
--          , P.Integral (Computation r a (D r a))
--          ) =>
--          MonOp Round a where
--   {-# INLINE ff #-}
--   ff _ a = P.round a
--   {-# INLINE fd #-}
--   fd _ a = P.round a
--   {-# INLINE df #-}
--   df _ cp ap at = (zero :: Computation r a (D r a))


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
class (Field a a) =>
      BoundedField a where
  -- maxBound :: (Domain a ~ D r t) => Computation r t a
  -- maxBound = ((one :: D r t) / (zero :: D r t))
  -- minBound :: (Domain a ~ D r t) => Computation r t a
  -- minBound = negate (one / zero)
  -- nan :: (Domain a ~ D r t) => Computation r t a
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
class ( Field a a
      , ExpField a 
      , BoundedField (Domain a) 
      , ExpField (CodomainU a)
      , Additive (Domain a) (Domain a)
      , Additive a (Domain a) 
      , Additive (Domain a) (CodomainU a)
      , Additive a (CodomainU a)
      , AdditiveGroup a (Domain a) 
      , Additive(CodomainU a)(CodomainU a)
      , MultiplicativeGroup (Domain a)(Domain a)
      , MultiplicativeGroup (Domain a) (CodomainU a)
      , MultiplicativeGroup (CodomainU a) (CodomainU a)
      ,MultiplicativeUnital ((Domain a ))
      , ExpField (CodomainU a)
      ) =>
      TrigField a where
  pi :: a
  sin :: a -> CodomainU a
  cos :: a -> CodomainU a
  tan :: a -> CodomainU a
  tan x = do
    sx <- sin x
    cx <- cos x
    sx / cx
  asin :: a -> CodomainU a
  acos :: a -> CodomainU a
  atan :: a -> CodomainU a
  sinh :: a -> CodomainU a
  cosh :: a -> CodomainU a
  tanh :: a -> CodomainU a
  tanh x = do
    sx <- sinh x
    cx <- cosh x
    sx / cx

  -- asinh :: ((Domain a )  ~ D r t) => a -> Computation r t (D r t)
  -- asinh z = log (z + sqrt ((one :: D r t) + z ** ((one :: D r t) + (one :: D r t))))

  asinh ::  a -> CodomainU a
  -- asinh z = log (z + sqrt ((one :: D r t) + z ** ((one :: D r t) + (one :: D r t))))


  acosh :: a -> CodomainU a
  -- acosh z = log (z + sqrt (z + (one :: D r t)) * sqrt (z - (one :: D r t)))
  atanh :: a -> CodomainU a
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




instance ( AdditiveGroup Double Double
         , Multiplicative Double Double
         , BoundedField (D r Double)
         , ExpField (CodomainU (D r Double))
         , Additive (Domain (D r Double)) (Domain (D r Double))
         , Additive (D r Double) (Domain (D r Double))
         , Additive (Domain (D r Double)) (CodomainU (D r Double))
         , Additive (D r Double) (CodomainU (D r Double))
         , AdditiveGroup (D r Double) (Domain (D r Double))
         , Additive (CodomainU (D r Double)) (CodomainU (D r Double))
         , MultiplicativeGroup (Domain (D r Double)) (Domain (D r Double))
         , MultiplicativeGroup (Domain (D r Double)) (CodomainU (D r Double))
         , MultiplicativeGroup (CodomainU (D r Double)) (CodomainU (D r Double))
         , MultiplicativeUnital ((Domain (D r Double)))
         ) =>
         TrigField (D r Double) where
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


instance (AdditiveGroup Float Float, Multiplicative Float Float
         , BoundedField (D r Float)
         , ExpField (CodomainU (D r Float))
         , Additive (Domain (D r Float)) (Domain (D r Float))
         , Additive (D r Float) (Domain (D r Float))
         , Additive (Domain (D r Float)) (CodomainU (D r Float))
         , Additive (D r Float) (CodomainU (D r Float))
         , AdditiveGroup (D r Float) (Domain (D r Float))
         , Additive (CodomainU (D r Float)) (CodomainU (D r Float))
         , MultiplicativeGroup (Domain (D r Float)) (Domain (D r Float))
         , MultiplicativeGroup (Domain (D r Float)) (CodomainU (D r Float))
         , MultiplicativeGroup (CodomainU (D r Float)) (CodomainU (D r Float))
         , MultiplicativeUnital ((Domain (D r Float)))) => TrigField (D r Float) where
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


instance ( AdditiveGroup Double Double
         , Multiplicative Double Double
         , BoundedField (Domain a)
         , ExpField (CodomainU a)
         , Additive (Domain a) (Domain a)
         , Additive a (Domain a)
         , Additive (Domain a) (CodomainU a)
         , Additive a (CodomainU a)
         , AdditiveGroup a (Domain a)
         , Additive (CodomainU a) (CodomainU a)
         , MultiplicativeGroup (Domain a) (Domain a)
         , MultiplicativeGroup (Domain a) (CodomainU a)
         , MultiplicativeGroup (CodomainU a) (CodomainU a)
         , MultiplicativeUnital ((Domain a))
         , ExpField (CodomainU a)
         , a ~ Computation r Double (D r Double)
         ) =>
         TrigField (Computation r Double (D r Double)) where
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

instance ( AdditiveGroup Float Float
         , Multiplicative Float Float
         , BoundedField (Domain a)
         , ExpField (CodomainU a)
         , Additive (Domain a) (Domain a)
         , Additive a (Domain a)
         , Additive (Domain a) (CodomainU a)
         , Additive a (CodomainU a)
         , AdditiveGroup a (Domain a)
         , Additive (CodomainU a) (CodomainU a)
         , MultiplicativeGroup (Domain a) (Domain a)
         , MultiplicativeGroup (Domain a) (CodomainU a)
         , MultiplicativeGroup (CodomainU a) (CodomainU a)
         , MultiplicativeUnital ((Domain a))
         , ExpField (CodomainU a)
         , a ~ Computation r Float (D r Float)
         ) =>
         TrigField (Computation r Float (D r Float)) where
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

instance (TrigField (D r a)
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a)) 
         , MonOp Cos r a
         , Trace Cos r a
         ) =>
         MonOp Sin r a where

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
    
instance (TrigField (D r a), Multiplicative (D r a) (Computation r a (D r a))) =>
         Trace Sin r a where
  pushEl (U _ a) dA = do
    d <- dA * (cos (p a))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]


instance (TrigField (D r a)
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a))
         , Multiplicative (Computation r a (D r a)) (Computation r a (D r a))
         , MonOp Cos r a
         , Trace Cos r a
         ) =>
         MonOp Cos r a where

  {-# INLINE fd #-}
  fd _ a = monOp Sin a
  {-# INLINE df #-}
  df _ _ ap at = at * (monOp Cos ap)

instance (P.Floating a
         ) =>
         FfMon Cos a where
  {-# INLINE ff #-}
  ff _ a = P.sin a

instance (AdditiveInvertible (Computation r a (D r a))
         , TrigField (D r a)
         , Multiplicative (D r a) (Computation r a (D r a))
         ) =>
         Trace Cos r a where
  pushEl (U _ a) dA = do
    d <- dA * (negate $ sin (p a))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]


instance (TrigField (D r a) 
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a))
         , Multiplicative (Computation r a (D r a)) (Computation r a (D r a))
         , MultiplicativeGroup (D r a) (Computation r a (D r a))
         , AdditiveInvertible (Computation r a (D r a))
         , ExpField (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a))
         ) =>
         MonOp ASin r a where

  {-# INLINE fd #-}
  fd _ a = monOp ASin a
  {-# INLINE df #-}
  df _ _ ap at = at / sqrt ((one :: D r a) - ap * ap)
  
instance (P.Floating a) => FfMon ASin a where
  {-# INLINE ff #-}
  ff _ a = P.asin a

instance (AdditiveInvertible (Computation r a (D r a))
         , TrigField (D r a)
         , Multiplicative (D r a) (Computation r a (D r a))
         , AdditiveGroup (D r a) (Computation r a (D r a))
         , ExpField (Computation r a (D r a))
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         ) =>
         Trace ASin r a where
  pushEl (U _ a) dA = do
    d <- dA / (sqrt ((one :: D r a) - (p a * p a)))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

instance (TrigField (D r a) 
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a)) 
         , Multiplicative (Computation r a (D r a)) (Computation r a (D r a)) 
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         , AdditiveInvertible (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a)) 
         ) =>
         MonOp ACos r a where

  {-# INLINE fd #-}
  fd _ a = monOp ACos a
  {-# INLINE df #-}
  df _ _ ap at = negate $ at / sqrt ((one :: D r a) - ap * ap)

instance (P.Floating a) => FfMon ACos a where
  {-# INLINE ff #-}
  ff _ a = P.acos a

instance (AdditiveInvertible (Computation r a (D r a)) 
         , TrigField (D r a) 
         , Multiplicative (D r a) (Computation r a (D r a))
         , AdditiveGroup (D r a) (Computation r a (D r a))
         , ExpField (Computation r a (D r a))
         , MultiplicativeGroup (D r a) (Computation r a (D r a))
         ) =>
         Trace ACos r a where
  pushEl (U _ a) dA = do
    d <- negate $ dA / (sqrt ((one :: D r a) - (p a * p a)))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]


instance (TrigField (D r a) 
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a))
         , Multiplicative (Computation r a (D r a)) (Computation r a (D r a))
         , MultiplicativeGroup (D r a) (Computation r a (D r a))
         , AdditiveInvertible (Computation r a (D r a))
         , ExpField (Computation r a (D r a))
         , AdditiveGroup (D r a) (Computation r a (D r a))
         ) =>
         MonOp ATan r a where

  {-# INLINE fd #-}
  fd _ a = monOp ATan a
  {-# INLINE df #-}
  df _ _ ap at = at / sqrt ((one :: D r a) + ap * ap)

instance (P.Floating a) => FfMon ATan a where
  {-# INLINE ff #-}
  ff _ a = P.atan a

instance (AdditiveInvertible (Computation r a (D r a))
         , TrigField (D r a) 
         , Multiplicative (D r a) (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a)) 
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         ) =>
         Trace ATan r a where
  pushEl (U _ a) dA = do
    d <- dA / (sqrt ((one :: D r a) + (p a * p a)))
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

instance ( TrigField (D r a)
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a))
         , Multiplicative (Computation r a (D r a)) (Computation r a (D r a)) 
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         , AdditiveInvertible (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a)) 
         ) =>
         MonOp SinH r a where

  {-# INLINE fd #-}
  fd _ a = monOp SinH a
  {-# INLINE df #-}
  df _ _ ap at = at * (cosh ap)

instance (P.Floating a) => FfMon SinH a where
  {-# INLINE ff #-}
  ff _ a = P.sinh a

instance (AdditiveInvertible (Computation r a (D r a)) 
         , TrigField (D r a) 
         , Multiplicative (D r a) (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a)) 
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         ) =>
         Trace SinH r a where
  pushEl (U _ a) dA = do
    d <- dA * (cosh $ p a)
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

instance (TrigField (D r a) 
         , P.Floating a
         , Multiplicative (D r a) (Computation r a (D r a)) 
         , Multiplicative (Computation r a (D r a)) (Computation r a (D r a)) 
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         , AdditiveInvertible (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a)) 
         ) =>
         MonOp CosH r a where

  {-# INLINE fd #-}
  fd _ a = monOp CosH a
  {-# INLINE df #-}
  df _ _ ap at = at * (sinh ap)

instance (P.Floating a ) => FfMon CosH a where
  {-# INLINE ff #-}
  ff _ a = P.cosh a

instance ( AdditiveInvertible (Computation r a (D r a)) 
         , TrigField (D r a) 
         , Multiplicative (D r a) (Computation r a (D r a)) 
         , AdditiveGroup (D r a) (Computation r a (D r a)) 
         , ExpField (Computation r a (D r a)) 
         , MultiplicativeGroup (D r a) (Computation r a (D r a)) 
         ) =>
         Trace CosH r a where
  pushEl (U _ a) dA = do
    d <- dA * (sinh $ p a)
    pure [(d, a)]
  resetEl (U _ a) = pure [a]

