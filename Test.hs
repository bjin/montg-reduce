{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

import Math.Montg

import Data.Bits
import Test.QuickCheck ((==>))
import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Data.Int (Int64)

main = defaultMain tests

tests = [ testGroup "basics"
          [ testProperty "add" prop_add
          , testProperty "sub" prop_sub
          , testProperty "mul" prop_mul
          , testProperty "pow2" prop_pow2
          , testProperty "int64" prop_int64
          ]
        ]

prop_add :: Integer -> Integer -> Integer -> Bool
prop_add x y n = n <= 0 || (fromInteger x + fromInteger y) `modP` n == (x + y) `mod` n

prop_sub :: Integer -> Integer -> Integer -> Bool
prop_sub x y n = n <= 0 || (fromInteger x - fromInteger y) `modP` n == (x - y) `mod` n

prop_mul :: Integer -> Integer -> Integer -> Bool
prop_mul x y n = n <= 0 || (fromInteger x * fromInteger y) `modP` n == (x * y) `mod` n

prop_pow2 :: Integer -> Integer -> Integer -> Bool
prop_pow2 x y n = n <= 0 || y < 0 || (fromInteger x ^ y) `modP` n == (x ^ y) `mod` n

prop_int64 :: Integer -> Bool
prop_int64 n = n <= 0 || (2 ^ n) `modP` (10^9+7 :: Int64) == fromInteger ((2 ^ n) `mod` (10^9+7))
