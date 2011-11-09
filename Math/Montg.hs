{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Math.Montg
  ( modP
  ) where

import Data.Bits

newtype Dep a b = Dep { unDep :: b }

data One = One

data D0 a = D0 a
data D1 a = D1 a

class (Ord b, Integral b, Bits b) => PositiveN p b where
    p2num :: Dep p b
    bitLen :: Dep (p, b) Int
    montgKeys :: Dep p b
    montgKeys = montgKeys'
    pmask :: Dep p b
    pmask = pmask'

instance (Ord b, Integral b, Bits b) => PositiveN One b where
    p2num = Dep 1
    bitLen = Dep 1

instance PositiveN p b => PositiveN (D0 p) b where
    p2num = Dep (unDep (p2num :: Dep p b) * 2)
    bitLen = Dep (unDep (bitLen :: Dep (p, b) Int) + 1)

instance PositiveN p b => PositiveN (D1 p) b where
    p2num = Dep (unDep (p2num :: Dep p b) * 2 + 1)
    bitLen = Dep (unDep (bitLen :: Dep (p, b) Int) + 1)

ctz :: (Num a, Bits a) => a -> Int
ctz x | testBit x 0 = 0
      | otherwise   = ctz (x `shiftR` 1)

pmask' :: forall p b. (PositiveN p b) => Dep p b
pmask' | bl == ctz n + 1 = Dep (bit (ctz n) - 1)
       | otherwise       = Dep (bit bl - 1)
  where
    n = unDep (p2num :: Dep p b)
    bl = unDep (bitLen :: Dep (p, b) Int)

-- | extended euclidean algorithm
-- `extgcd a b` returns `(g, x, y)` s.t. `g = gcd a b` and `ax + by = g`
--
extgcd :: Integral a => a -> a -> (a, a, a)
extgcd a b | a < 0 = let (g, x, y) = extgcd (-a) b in (g, -x, y)
extgcd a b | b < 0 = let (g, x, y) = extgcd a (-b) in (g, x, -y)
extgcd a 0 = (a, 1, 0)
extgcd a b = let
                 (adivb, amodb) = a `divMod` b
                 (g, y, x) = extgcd b amodb
                 --   (a - a / b * b) * x + b * y
                 -- = a * x - a / b * b * x + b * y
                 -- = a * x + (y - a / b * x) * b
             in
                 (g, x, y - adivb * x)

newtype PositiveN p b => ModP2 p b = ModP2 { unModP2 :: b } deriving Eq

instance PositiveN p b => Show (ModP2 p b) where
    show (ModP2 r) = show r ++ "+" ++ show (unDep (pmask :: Dep p b) + 1) ++ "Z"

instance PositiveN p b => Num (ModP2 p b) where
    ModP2 a + ModP2 b = ModP2 ((a + b) .&. unDep (pmask :: Dep p b))
    ModP2 a - ModP2 b = ModP2 ((a - b) .&. unDep (pmask :: Dep p b))
    ModP2 a * ModP2 b = ModP2 ((a * b) .&. unDep (pmask :: Dep p b))
    fromInteger x = ModP2 (fromInteger x .&. unDep (pmask :: Dep p b))
    abs = id
    signum = const 1

montgKeys' :: forall p b. PositiveN p b => Dep p b
montgKeys' | ctz n /= 0 = error "ModP : p must be odd"
           | g /= 1     = error "ModP : internal error"
           | otherwise  = Dep ((-n') `mod` r)
  where
    n = unDep (p2num :: Dep p b)
    bl = unDep (bitLen :: Dep (p, b) Int)
    r = bit bl

    (g, r', n') = extgcd r n

trans :: forall p b. PositiveN p b => Dep p b -> Dep p b
trans (Dep x) = Dep ((x `shiftL` unDep (bitLen :: Dep (p, b) Int)) `mod` unDep (p2num :: Dep p b))

reduce :: forall p b. PositiveN p b => Dep p b -> Dep p b
reduce (Dep x)
    | a > n     = Dep (a - n)
    | otherwise = Dep a
  where
    n = unDep (p2num :: Dep p b)
    pm = unDep (pmask :: Dep p b)
    q = ((x .&. pm) * unDep (montgKeys :: Dep p b)) .&. pm
    a = (x + q * n) `shiftR` unDep (bitLen :: Dep (p, b) Int)

newtype PositiveN p b => ModP p b = ModP { unModP :: b } deriving Eq

instance PositiveN p b => Show (ModP p b) where
    show (ModP r) = show (unDep (reduce (Dep r) :: Dep p b)) ++ "+" ++ show (unDep (p2num :: Dep p b)) ++ "Z"

instance PositiveN p b => Num (ModP p b) where
    ModP a + ModP b
        | a + b >= n = ModP (a + b - n)
        | otherwise  = ModP (a + b)
      where
        n = unDep (p2num :: Dep p b)
    ModP a - ModP b
        | a >= b    = ModP (a - b)
        | otherwise = ModP (a + unDep (p2num :: Dep p b) - b)
    ModP a * ModP b = (ModP . unDep) (reduce (Dep (a * b) :: Dep p b))
    fromInteger x = (ModP . unDep) (trans (Dep (fromInteger x `mod` unDep (p2num :: Dep p b))) :: Dep p b)
    abs = id
    signum = const 1

num2p' :: (Integral b, Bits b, Ord b, Integral i) => i -> (forall p. PositiveN p b => p -> b) -> (forall p. PositiveN p b => p -> b)
num2p' n _ | n <= 0 = error "num2p: internal error"
num2p' 1 f = f
num2p' n f | even n    = num2p' (n `div` 2) (f . D0)
           | otherwise = num2p' (n `div` 2) (f . D1)

num2p :: (Integral b, Bits b, Ord b, Integral i) => i -> (forall p. PositiveN p b => p -> b) -> b
num2p n f = (num2p' n f) One

modP :: (Integral b, Bits b, Ord b) => (forall a. Num a => a) -> b -> b
modP val n 
    | n <= 0    = error "modP: modulus must be positive"
    | g /= 1    = error "modP: internal error"
    | otherwise = (m1' + m2') `mod` n
  where
    go x | even x    = go (x `div` 2)
         | otherwise = x

    n1 = go n
    n2 = n `div` n1

    go1 :: forall p b. (PositiveN p b) => p -> b
    go1 _ = unDep (reduce (Dep (unModP (val :: ModP p b))) :: Dep p b)
    
    m1 | n1 == 1   = 0
       | otherwise = num2p n1 go1

    go2 :: forall p b. (PositiveN p b) => p -> b
    go2 _ = unModP2 (val :: ModP2 p b)

    m2 | n2 == 1   = 0
       | otherwise = num2p n2 go2

    (g, r1, r2) = extgcd n1 n2

    m1' = (m1 * r2 `mod` n1) * n2
    m2' = (m2 * r1 `mod` n2) * n1
