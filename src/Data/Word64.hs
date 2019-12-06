{- | Data.Word64 is an implementation of


-}

{-# LANGUAGE BangPatterns, MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Data.Word64(
  Word64(..)
  ) where


import GHC.Prim

import Data.Typeable(Typeable)
import Data.Data(Data)
#include "MachDeps.h"
#if WORD_SIZE_IN_BITS == 64

import Data.Word(Word64(..))
#elif WORD_SIZE_IN_BITS == 32
import GHC.Base as GB
import GHC.Enum as GE
import GHC.Num as GN
import GHC.Real as GR
import GHC.Arr as GA
import GHC.Show as GS

import Data.Bits

--data Word = W# Word# Word#

#else
#error "uh oh, word is neither 32 or 64 bit"
#endif


#if WORD_SIZE_IN_BITS == 32


data {-# CTYPE "HsWord64" #-} Word64 =
  W64# Word#  -- high word
       Word#  -- low word
-- ^ 64-bit unsigned integer type

-- See GHC.Classes#matching_overloaded_methods_in_rules
-- | @since 2.01
instance Eq Word64 where
    (==) = eqWord64
    (/=) = neWord64

eqWord64, neWord64 :: Word64 -> Word64 -> Bool
eqWord64 (W64# x) (W64# y) = isTrue# (x `eqWord64#` y)
neWord64 (W64# x) (W64# y) = isTrue# (x `neWord64#` y)
{-# INLINE [1] eqWord64 #-}
{-# INLINE [1] neWord64 #-}

-- | @since 2.01
instance Ord Word64 where
    (<)  = ltWord64
    (<=) = leWord64
    (>=) = geWord64
    (>)  = gtWord64

{-# INLINE [1] gtWord64 #-}
{-# INLINE [1] geWord64 #-}
{-# INLINE [1] ltWord64 #-}
{-# INLINE [1] leWord64 #-}
gtWord64, geWord64, ltWord64, leWord64 :: Word64 -> Word64 -> Bool
(W64# x) `gtWord64` (W64# y) = isTrue# (x `gtWord64#` y)
(W64# x) `geWord64` (W64# y) = isTrue# (x `geWord64#` y)
(W64# x) `ltWord64` (W64# y) = isTrue# (x `ltWord64#` y)
(W64# x) `leWord64` (W64# y) = isTrue# (x `leWord64#` y)

-- | @since 2.01
instance Num Word64 where
    (W64# x#) + (W64# y#)  = W64# (int64ToWord64# (word64ToInt64# x# `plusInt64#` word64ToInt64# y#))
    (W64# x#) - (W64# y#)  = W64# (int64ToWord64# (word64ToInt64# x# `minusInt64#` word64ToInt64# y#))
    (W64# x#) * (W64# y#)  = W64# (int64ToWord64# (word64ToInt64# x# `timesInt64#` word64ToInt64# y#))
    negate (W64# x#)       = W64# (int64ToWord64# (negateInt64# (word64ToInt64# x#)))
    abs x                  = x
    signum 0               = 0
    signum _               = 1
    fromInteger i          = W64# (integerToWord64 i)

-- | @since 2.01
instance Enum Word64 where
    succ x
        | x /= maxBound = x + 1
        | otherwise     = succError "Word64"
    pred x
        | x /= minBound = x - 1
        | otherwise     = predError "Word64"
    toEnum i@(I# i#)
        | i >= 0        = W64# (wordToWord64# (int2Word# i#))
        | otherwise     = toEnumError "Word64" i (minBound::Word64, maxBound::Word64)
    fromEnum x@(W64# x#)
        | x <= fromIntegral (maxBound::Int)
                        = I# (word2Int# (word64ToWord# x#))
        | otherwise     = fromEnumError "Word64" x
    enumFrom            = integralEnumFrom
    enumFromThen        = integralEnumFromThen
    enumFromTo          = integralEnumFromTo
    enumFromThenTo      = integralEnumFromThenTo

-- | @since 2.01
instance Integral Word64 where
    quot    (W64# x#) y@(W64# y#)
        | y /= 0                    = W64# (x# `quotWord64#` y#)
        | otherwise                 = divZeroError
    rem     (W64# x#) y@(W64# y#)
        | y /= 0                    = W64# (x# `remWord64#` y#)
        | otherwise                 = divZeroError
    div     (W64# x#) y@(W64# y#)
        | y /= 0                    = W64# (x# `quotWord64#` y#)
        | otherwise                 = divZeroError
    mod     (W64# x#) y@(W64# y#)
        | y /= 0                    = W64# (x# `remWord64#` y#)
        | otherwise                 = divZeroError
    quotRem (W64# x#) y@(W64# y#)
        | y /= 0                    = (W64# (x# `quotWord64#` y#), W64# (x# `remWord64#` y#))
        | otherwise                 = divZeroError
    divMod  (W64# x#) y@(W64# y#)
        | y /= 0                    = (W64# (x# `quotWord64#` y#), W64# (x# `remWord64#` y#))
        | otherwise                 = divZeroError
    toInteger (W64# x#)             = word64ToInteger x#

-- | @since 2.01
instance Bits Word64 where
    {-# INLINE shift #-}
    {-# INLINE bit #-}
    {-# INLINE testBit #-}

    (W64# x#) .&.   (W64# y#)  = W64# (x# `and64#` y#)
    (W64# x#) .|.   (W64# y#)  = W64# (x# `or64#`  y#)
    (W64# x#) `xor` (W64# y#)  = W64# (x# `xor64#` y#)
    complement (W64# x#)       = W64# (not64# x#)
    (W64# x#) `shift` (I# i#)
        | isTrue# (i# >=# 0#)  = W64# (x# `shiftL64#` i#)
        | otherwise            = W64# (x# `shiftRL64#` negateInt# i#)
    (W64# x#) `shiftL`       (I# i#) = W64# (x# `shiftL64#` i#)
    (W64# x#) `unsafeShiftL` (I# i#) = W64# (x# `uncheckedShiftL64#` i#)
    (W64# x#) `shiftR`       (I# i#) = W64# (x# `shiftRL64#` i#)
    (W64# x#) `unsafeShiftR` (I# i#) = W64# (x# `uncheckedShiftRL64#` i#)
    (W64# x#) `rotate` (I# i#)
        | isTrue# (i'# ==# 0#) = W64# x#
        | otherwise            = W64# ((x# `uncheckedShiftL64#` i'#) `or64#`
                                       (x# `uncheckedShiftRL64#` (64# -# i'#)))
        where
        !i'# = word2Int# (int2Word# i# `and#` 63##)
    bitSizeMaybe i            = Just (finiteBitSize i)
    bitSize i                 = finiteBitSize i
    isSigned _                = False
    popCount (W64# x#)        = I# (word2Int# (popCnt64# x#))
    bit                       = bitDefault
    testBit                   = testBitDefault

-- give the 64-bit shift operations the same treatment as the 32-bit
-- ones (see GHC.Base), namely we wrap them in tests to catch the
-- cases when we're shifting more than 64 bits to avoid unspecified
-- behaviour in the C shift operations.

shiftL64#, shiftRL64# :: Word64# -> Int# -> Word64#

a `shiftL64#` b  | isTrue# (b >=# 64#) = wordToWord64# 0##
                 | otherwise           = a `uncheckedShiftL64#` b

a `shiftRL64#` b | isTrue# (b >=# 64#) = wordToWord64# 0##
                 | otherwise           = a `uncheckedShiftRL64#` b

{-# RULES
"fromIntegral/Int->Word64"    fromIntegral = \(I#   x#) -> W64# (int64ToWord64# (intToInt64# x#))
"fromIntegral/Word->Word64"   fromIntegral = \(W#   x#) -> W64# (wordToWord64# x#)
"fromIntegral/Word64->Int"    fromIntegral = \(W64# x#) -> I#   (word2Int# (word64ToWord# x#))
"fromIntegral/Word64->Word"   fromIntegral = \(W64# x#) -> W#   (word64ToWord# x#)
"fromIntegral/Word64->Word64" fromIntegral = id :: Word64 -> Word64
  #-}



-- | @since 4.6.0.0
instance FiniteBits Word64 where
    finiteBitSize _ = 64
    countLeadingZeros  (W64# x#) = I# (word2Int# (clz64# x#))
    countTrailingZeros (W64# x#) = I# (word2Int# (ctz64# x#))

-- | @since 2.01
instance Show Word64 where
    showsPrec p x = showsPrec p (toInteger x)

-- | @since 2.01
instance Real Word64 where
    toRational x = toInteger x % 1

-- | @since 2.01
instance Bounded Word64 where
    minBound = 0
    maxBound = 0xFFFFFFFFFFFFFFFF

-- | @since 2.01
instance Ix Word64 where
    range (m,n)         = [m..n]
    unsafeIndex (m,_) i = fromIntegral (i - m)
    inRange (m,n) i     = m <= i && i <= n

-- | Reverse order of bytes in 'Word64'.
--
-- @since 4.7.0.0

byteSwap64 :: Word64 -> Word64
byteSwap64 (W64# w#) = W64# (byteSwap64# w#)

#endif









