{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

module Math.Montg 
  ( modP
  ) where

import Data.Bits

data One = One

data D0 a = D0 a
data D1 a = D1 a

class PostiveN a where
    p2num :: (Num b, Bits b) => a -> b
    ctz :: a -> Int
    bitLen :: a -> Int

instance PostiveN One where
    p2num _ = 1 :: forall b. (Num b, Bits b) => b
    ctz _ = 0
    bitLen _ = 1

instance PostiveN a => PostiveN (D0 a) where
    p2num _ = p2num (undefined :: a) * 2 :: forall b. (Num b, Bits b) => b
    ctz _ = ctz (undefined :: a) + 1
    bitLen _ = bitLen (undefined :: a) + 1

instance PostiveN a => PostiveN (D1 a) where
    p2num _ = p2num (undefined :: a) * 2 + 1 :: forall b. (Num b, Bits b) => b
    ctz _ = 0
    bitLen _ = bitLen (undefined :: a) + 1

pmask :: (PostiveN a, Num b, Bits b) => a -> b
pmask p | bitLen p == ctz p + 1 = bit (ctz p) - 1
        | otherwise             = bit (bitLen p) - 1

addmod2 :: (PostiveN a, Num b, Bits b) => a -> b -> b -> b
addmod2 p a b = (a + b) .&. pmask p
{-# INLINE addmod2 #-}

submod2 :: (PostiveN a, Num b, Bits b) => a -> b -> b -> b
submod2 p a b = (a - b) .&. pmask p
{-# INLINE submod2 #-}

mulmod2 :: (PostiveN a, Num b, Bits b) => a -> b -> b -> b
mulmod2 p a b = (a * b) .&. pmask p
{-# INLINE mulmod2 #-}

addmod :: (PostiveN a, Integral b, Bits b) => a -> b -> b -> b
addmod p a b | a + b >= p2num p = a + b - p2num p
             | otherwise        = a + b
{-# INLINE addmod #-}

submod :: (PostiveN a, Integral b, Bits b) => a -> b -> b -> b
submod p a b | a < b     = a + p2num p - b
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

instance (PostiveN p, Show a) => Show (ModP2 p a) where
    show (ModP2 r) = show r ++ "+" ++ show (pmask (undefined :: p) + 1 :: Integer) ++ "Z"

instance (PostiveN p, Num a, Bits a) => Num (ModP2 p a) where
    ModP2 a + ModP2 b = ModP2 $ addmod2 (undefined :: p) a b
    ModP2 a - ModP2 b = ModP2 $ submod2 (undefined :: p) a b
    ModP2 a * ModP2 b = ModP2 $ mulmod2 (undefined :: p) a b
    fromInteger = ModP2 . fromInteger . (`mod` (pmask (undefined :: p) + 1))
    abs = id
    signum = const 1

montgKeys :: (PostiveN p, Integral a, Bits a) => p -> a
montgKeys p | ctz p /= 0 = error "ModP : p must be odd"
            | g /= 1     = error "ModP : internal error"
            | otherwise  = (-n') `mod` r
  where
    n = p2num p
    blen = bitLen p
    r = bit blen

    (g, r', n') = extgcd r n

trans :: (PostiveN p, Integral a, Bits a) => p -> a -> a
trans p x = (x `shiftL` bitLen p) `mod` p2num p

reduce :: (PostiveN p, Integral a, Bits a) => p -> a -> a
reduce p x
    | a > n     = a - n
    | otherwise = a
  where
    n = p2num p
    q = ((x .&. pmask p) * montgKeys p) .&. pmask p
    a = (x + q * n) `shiftR` bitLen p

newtype PostiveN p => ModP p a = ModP { unModP :: a } deriving Eq

instance (PostiveN p, Integral a, Bits a) => Show (ModP p a) where
    show (ModP r) = show (reduce (undefined :: p) r) ++ "+" ++ show (p2num (undefined :: p) :: Integer) ++ "Z"

instance (PostiveN p, Integral a, Bits a) => Num (ModP p a) where
    ModP a + ModP b = ModP $ addmod (undefined :: p) a b
    ModP a - ModP b = ModP $ submod (undefined :: p) a b
    ModP a * ModP b = ModP $ reduce (undefined :: p) (a * b)
    fromInteger = ModP . trans (undefined :: p). fromInteger . (`mod` p2num (undefined :: p))
    abs = id
    signum = const 1

num2p' :: Integral i => i -> (forall a. PostiveN a => a -> b) -> (forall a. PostiveN a => a -> b)
num2p' n _ | n <= 0 = error "num2p: internal error"
num2p' 1 f = f
num2p' n f | even n    = num2p' (n `div` 2) (f . D0)
           | otherwise = num2p' (n `div` 2) (f . D1)

num2p :: Integral i => i -> (forall p. PostiveN p => p -> b) -> b
num2p n f = (num2p' n f) (undefined :: One)

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
