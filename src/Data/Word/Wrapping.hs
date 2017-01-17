{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Data.Word.Wrapping(
  Word64(..)
  ,Word32(..)
  ,nativeWordSize
 )where

import Data.Word(Word32(..)
                ,Word64(..)
                ,byteSwap32,byteSwap64)
import Data.Data (Data,Typeable)
import Data.Bits

#include "MachDeps.h"

nativeWordSize :: Word64
nativeWordSize = WORD_SIZE_IN_BITS

{-# inline oneBits #-}
oneBits :: (FiniteBits b) => b
oneBits = complement zeroBits

data Word128 =
    W128# {-# UNPACK #-} !Word64  -- high bits
          {-# UNPACK #-} !Word64  -- low bits
    deriving(Eq,Data,Typeable)

data Word256 =
    W256# {-# UNPACK #-} !Word128  -- high bits
          {-# UNPACK #-} !Word128  -- low bits
    deriving(Eq,Data,Typeable)

-- NB on 32bit systems we *may* be able to do a faster Ord Word128 instance
-- but this depends on the rep of word64 in that context
-- so not doing for now


instance Ord Word128 where
  compare (W128# hw1 lw1) (W128# hw2 lw2) =
      case compare hw1 hw2 of
        GT -> GT
        EQ -> compare lw1 lw2
        LT -> LT

instance Ord Word256 where
  compare (W256# hw1 lw1) (W256# hw2 lw2) =
      case compare hw1 hw2 of
        GT -> GT
        EQ -> compare lw1 lw2
        LT -> LT

instance Bits Word128 where
    --{-# INLINE shift #-}
    {-# INLINE bit #-}
    {-# INLINE testBit #-}


    (W128# hw1 lw1) .&.   (W128# hw2 lw2)  = W128# (hw1 .&. hw2) (lw1 .&. lw2)
    (W128# hw1 lw1) .|.   (W128# hw2 lw2)  = W128# (hw1 .|. hw2) (lw1 .|. lw2)
    (W128# hw1 lw1) `xor` (W128# hw2 lw2)  = W128# (hw1 `xor` hw2) (lw1 `xor` lw2)
    complement (W128# hw1 lw1)       = W128# (complement hw1) (complement lw1)
    --((W128# hw1 lw1) `shift` (I# i#)
    --    | isTrue# (i# >=# 0#)  = W128# (x# `shiftL64#` i#)
    --    | otherwise            = W128# (x# `shiftRL64#` negateInt# i#)
    (W128# hw1 lw1) `shiftL`       i
              | i >= 0  =    W128#  ((hw1 `unsafeShiftL` i) .|. (lw1 `shift` (i -64)))
                                    (lw1 `unsafeShiftL` i )
              | otherwise = error "negative argument to shiftL Word128"
     -- W128# (hw1 `shiftL` i .|. lw1 `shiftR` (negate ))
    (W128# hw lw) `unsafeShiftL` i =  W128# ((hw `unsafeShiftL` i) .|. (lw `shift` (i - 64)))
                                            (lw `unsafeShiftL` i )
    (W128# hw lw) `shiftR`  i
                               | i >= 0  = W128# (hw `unsafeShiftR` i)
                                           ((hw `shift` (i - 64) )  .|.  (lw  `unsafeShiftR` i))
                               | otherwise = error  "negative index for shiftR Word128"
    (W128# hw lw) `unsafeShiftR` i = W128# (hw `unsafeShiftR` i)
                                           ((hw `shift` (i - 64) )  .|.  (lw  `unsafeShiftR` i))
    --(W128# hw1 lw1) `rotate` i
    --    | isTrue# (i'# ==# 0#) = W128# x#
    --    | otherwise            = W128# ((x# `uncheckedShiftL64#` i'#) `or64#`
    --                                   (x# `uncheckedShiftRL64#` (64# -# i'#)))
    --    where
    --    !i'# = word2Int# (int2Word# i# `and#` 63##)
    bw@(W128# hw lw) `rotateL` i
                                | i < 0 = error "negative Int argument to rotateL Word128"
                                | otherwise = W128# ((hw `unsafeShiftL` modi) .|. (lw `shift` modtrani))
                                                    ((lw `unsafeShiftL` modi) .|. (hw `shift` modtrani))
                where
                    modi = i `mod` 128
                    modtrani = modi - 64
    bitSizeMaybe i            = Just (finiteBitSize i)
    bitSize i                 = finiteBitSize i
    isSigned _                = False
    popCount (W128# hw1 lw1)  = popCount hw1 + popCount lw1
    bit i | i  >= 64 &&  i <= 127 =  W128# (bit (i - 64)) 0
          | i >= 0 && i < 64 =  W128# 0 (bit i)
          | otherwise = W128# 0 0
    testBit a i | i >= 64 && i <= 127 = testBit a (i - 64)
                | i >= 0 =  testBit a  i
                | otherwise = False
instance FiniteBits Word128 where
  finiteBitSize _ = 128
  countLeadingZeros (W128# hw lw)  | hw /= 0 = countLeadingZeros hw
                                   | otherwise = 64 + countLeadingZeros lw
  countTrailingZeros (W128# hw lw) | lw /= 0 = countTrailingZeros lw
                                   | otherwise = 64 + countTrailingZeros hw


