{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

module Math.Montg 
  ( modP
  ) where

import Data.Bits

newtype Dep a b = Dep { unDep :: b }

data One = One

data D0 a = D0 a
data D1 a = D1 a

class PostiveN a where
    p2num :: (Num b, Bits b) => Dep a b

instance PostiveN One where
    p2num = Dep 1

instance PostiveN p => PostiveN (D0 p) where
    p2num = Dep (unDep (p2num :: forall b. (Num b, Bits b) => Dep p b) * 2)

instance PostiveN p => PostiveN (D1 p) where
    p2num = Dep (unDep (p2num :: forall b. (Num b, Bits b) => Dep p b) * 2 + 1)

ctz :: (Num a, Bits a) => a -> Int
ctz x | testBit x 0 = 0
      | otherwise   = ctz (x `shiftR` 1)

bitLen :: (Num a, Bits a) => a -> Int
bitLen 0 = 0
bitLen x = bitLen (x `shiftR` 1) + 1

pmask :: forall p b. (PostiveN p, Num b, Bits b) => Dep p b
pmask | bitLen n == ctz n + 1 = Dep (bit (ctz n) - 1)
      | otherwise             = Dep (bit (bitLen n) - 1)
  where
    n = unDep (p2num :: Dep p b)

addmod2 :: forall p b. (PostiveN p, Num b, Bits b) => p -> b -> b -> b
addmod2 _ a b = (a + b) .&. unDep (pmask :: Dep p b)
{-# INLINE addmod2 #-}

submod2 :: forall p b. (PostiveN p, Num b, Bits b) => p -> b -> b -> b
submod2 _ a b = (a - b) .&. unDep (pmask :: Dep p b)
{-# INLINE submod2 #-}

mulmod2 :: forall p b. (PostiveN p, Num b, Bits b) => p -> b -> b -> b
mulmod2 _ a b = (a * b) .&. unDep (pmask :: Dep p b)
{-# INLINE mulmod2 #-}

addmod :: forall p b. (PostiveN p, Integral b, Bits b) => p -> b -> b -> b
addmod _ a b | a + b >= p = a + b - p
             | otherwise  = a + b
  where
    p = unDep (p2num :: Dep p b)
{-# INLINE addmod #-}

submod :: forall p b. (PostiveN p, Integral b, Bits b) => p -> b -> b -> b
submod _ a b | a < b     = a + unDep (p2num :: Dep p b) - b
             | otherwise = a - b
{-# INLINE submod #-}

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

newtype PostiveN p => ModP2 p a = ModP2 { unModP2 :: a } deriving Eq

instance (PostiveN p, Integral a, Bits a) => Show (ModP2 p a) where
    show (ModP2 r) = show r ++ "+" ++ show (unDep (pmask :: Dep p a) + 1) ++ "Z"

instance (PostiveN p, Integral a, Bits a) => Num (ModP2 p a) where
    ModP2 a + ModP2 b = ModP2 $ addmod2 (undefined :: p) a b
    ModP2 a - ModP2 b = ModP2 $ submod2 (undefined :: p) a b
    ModP2 a * ModP2 b = ModP2 $ mulmod2 (undefined :: p) a b
    fromInteger = ModP2 . fromInteger . (`mod` (unDep (pmask :: Dep p Integer) + 1))
    abs = id
    signum = const 1

montgKeys :: forall p b. (PostiveN p, Integral b, Bits b) => Dep p b
montgKeys | ctz n /= 0 = error "ModP : p must be odd"
          | g /= 1     = error "ModP : internal error"
          | otherwise  = Dep ((-n') `mod` r)
  where
    n = unDep (p2num :: Dep p b)
    blen = bitLen n
    r = bit blen

    (g, r', n') = extgcd r n

trans :: forall p b. (PostiveN p, Integral b, Bits b) => p -> b -> b
trans _ x = (x `shiftL` bitLen n) `mod` n
  where
    n = unDep (p2num :: Dep p b)

reduce :: forall p b. (PostiveN p, Integral b, Bits b) => p -> b -> b
reduce _ x
    | a > n     = a - n
    | otherwise = a
  where
    n = unDep (p2num :: Dep p b)
    pm = unDep (pmask :: Dep p b)
    q = ((x .&. pm) * unDep (montgKeys :: Dep p b)) .&. pm
    a = (x + q * n) `shiftR` bitLen n

newtype PostiveN p => ModP p a = ModP { unModP :: a } deriving Eq

instance (PostiveN p, Integral a, Bits a) => Show (ModP p a) where
    show (ModP r) = show (reduce (undefined :: p) r) ++ "+" ++ show (unDep (p2num :: Dep p a)) ++ "Z"

instance (PostiveN p, Integral a, Bits a) => Num (ModP p a) where
    ModP a + ModP b = ModP $ addmod (undefined :: p) a b
    ModP a - ModP b = ModP $ submod (undefined :: p) a b
    ModP a * ModP b = ModP $ reduce (undefined :: p) (a * b)
    fromInteger = ModP . trans (undefined :: p). fromInteger . (`mod` unDep (p2num :: Dep p Integer))
    abs = id
    signum = const 1

num2p' :: Integral i => i -> (forall a. PostiveN a => a -> b) -> (forall a. PostiveN a => a -> b)
num2p' n _ | n <= 0 = error "num2p: internal error"
num2p' 1 f = f
num2p' n f | even n    = num2p' (n `div` 2) (f . D0)
           | otherwise = num2p' (n `div` 2) (f . D1)

num2p :: Integral i => i -> (forall p. PostiveN p => p -> b) -> b
num2p n f = (num2p' n f) One

modP :: (Integral b, Bits b) => (forall a. Num a => a) -> b -> b
modP val n 
    | n <= 0    = error "modP: modulus must be positive"
    | g /= 1    = error "modP: internal error"
    | otherwise = (m1' + m2') `mod` n
  where
    go x | even x    = go (x `div` 2)
         | otherwise = x

    n1 = go n
    n2 = n `div` n1

    go1 :: forall b. forall p. (Integral b, Bits b, PostiveN p) => p -> b
    go1 _ = reduce (undefined :: p) $ unModP (val :: ModP p b)
    
    m1 | n1 == 1   = 0
       | otherwise = num2p n1 go1

    go2 :: forall b. forall p. (Integral b, Bits b, PostiveN p) => p -> b
    go2 _ = unModP2 (val :: ModP2 p b)

    m2 | n2 == 1   = 0
       | otherwise = num2p n2 go2

    (g, r1, r2) = extgcd n1 n2

    m1' = (m1 * r2 `mod` n1) * n2
    m2' = (m2 * r1 `mod` n2) * n1
