{-#  LANGUAGE BangPatterns, CPP, ForeignFunctionInterface, MagicHash,
        NoImplicitPrelude, UnboxedTuples, UnliftedFFITypes #-}
{-
for now, 32bit support is done by way of mapping back and forth to natural,
there *may* be circumstance where thiswould actually be faster than
the approach with native word64#, but for now probably not.
many thanks to some friends who made the suggestion, though i was
a tad slow on executing it.

that code path is likely SUPER BUGGY :)
-}
module Data.CarryUtils.Word64(
  --boxInt#
  --,boxWord#
  --,boxDouble#
  --,unboxWord
  --,unboxInt
  --,unboxDouble
  plusWord
  ,plusWord2
  ,plusWord3
  ,plusWord4

  ,minusWord2
  ,minusWord2C

  ,timesWord2
  ,timesWord2C
  ,timesWord2CC

  ,quotRemWord64
  ,quotRemWord2

  ,nat2Word64C
  ,nat2Word64

  ,shiftLWord2#
  ,shiftRWord64

  ,wordSizeInBits
  ,wordSizeInBytes
  ,highestSetBit
  ) where

import GHC.Prim
--import Data.Word
import GHC.Word(Word64(..))

#include "MachDeps.h"


-- code in part derived from
-- https://github.com/erikd/haskell-big-integer-experiment/blob/master/Common/GHC/Integer/Prim.hs
-- as of January 2017

import GHC.Base (Int (..)
               --, Word (..)
               )
--import GHC.Float (Double (..))
import GHC.Types (isTrue#)

import Numeric.Natural
import qualified Prelude as P
import Prelude
import Data.Bits as DB

#if  !(WORD_SIZE_IN_BITS == 64  || WORD_SIZE_IN_BITS == 32)
#error "something really unusual happening on this platform, native word isnt 32 or 64 bits"
#endif

-- uncomment this line to test the not 64bit platform fallback
-- #define PrimFALLBACK 1

-- NOTE: nat2Word64C is ONLY safe / correct when the overflow is at most 64bits
{-# INLINE nat2Word64C #-}
nat2Word64C :: Natural -> (# Word64 ,Word64 #)
nat2Word64C nat = val  `seq`  (carry `seq`  (#carry  , val #))
    where
      val = carry `seq` fromIntegral $ 0xFFFFFFFFFFFFFFFFFF  .&. nat
      carry = val `seq` (fromIntegral P.$! (DB.unsafeShiftR val 64))

-- wrapping semantics for Natural number to word64 truncation is assumed here
-- any other semantics is a bug. This corresponds to taking the lower 64 bits of the
-- natural number as is
{-# INLINE nat2Word64 #-}
nat2Word64 :: Natural -> Word64
nat2Word64 = \ n -> fromIntegral n

-- Many of these primitives are defined in compiler/prelude/primops.txt.pp
-- from the GHC source tree (both the Git tree and the distribution tarball.





--{-# INLINE boxInt# #-}
--boxInt# :: Int# -> Int
--boxInt# = I#

--{-# INLINE boxWord# #-}
--boxWord# :: Word# -> Word64
--boxWord# = W64#

--{-# INLINE boxDouble# #-}
--boxDouble# :: Double# -> Double
--boxDouble# = D#


--{-# INLINE unboxInt #-}
--unboxInt :: Int -> Int#
--unboxInt (I# !i#) = i#

--{-# INLINE unboxWord #-}
--unboxWord :: Word64 -> Word#
--unboxWord (W64# !w#) = w#

--{-# INLINE unboxDouble #-}
--unboxDouble :: Double -> Double#
--unboxDouble (D# !d#) = d#



{- the real answer here is to have all
the carry ops defined via wired in for native / supported 32/64/native pointer sized
int/word stuff, but in the mean time lets keep the 32bit platform code simple and correct

also use ghcjs to make sure the 32bit path is correct

this code will get messy / complicated perhaps depending on how word64# et al
are added (correctly or not)
 -}


{-# INLINE plusWord #-}
-- | a + b
plusWord :: Word64 -> Word64 -> Word64
#if WORD_SIZE_IN_BITS == 64  &&  !defined(PrimFALLBACK)
plusWord  = \ (W64# a) (W64# b) ->
    let !s = plusWord# a b
    in W64# s
#else
plusWord  = \ a b ->  nat2Word64 $ (fromIntegral a) + (fromIntegral b)
#endif

--- for add with carry, result is (# high word aka carry , low word #)

{-# INLINE plusWord2 #-}
-- | a + b, with carry and result tuple
plusWord2 :: Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
plusWord2  = \ (W64# a) (W64# b) ->
    let !(# !c, !s #) = plusWord2# a b
    in (# W64# c, W64# s #)
#else
plusWord2  = \ a b -> nat2Word64C $! fromIntegral a +  fromIntegral b
#endif

{-# INLINE plusWord3 #-}
-- | a + b + c , with carry
plusWord3 :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
plusWord3  = \  (W64# a) (W64# b) (W64# c) ->
    let !(# !c1, !s1 #) = plusWord2# a b
        !(# !c2, !s2 #) = plusWord2# s1 c
        !c3 = plusWord# c1 c2
    in (# W64# c3, W64# s2 #)
#else
plusWord3 = \ a b c -> nat2Word64C $! (fromIntegral a + fromIntegral b + fromIntegral c)
#endif

{-# INLINE plusWord4 #-}
-- | a + b + c + d , with carry
plusWord4 :: Word64 -> Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
plusWord4  = \ (W64# a) (W64# b) (W64# c) (W64# d) ->
    let !(# !c1, !s1 #) = plusWord2# a b
        !(# !c2, !s2 #) = plusWord2# c d
        !(# !c3, !s3 #) = plusWord2# s1 s2
        !c4 = plusWord# c1 c2
        !carry = plusWord# c3 c4
    in (# W64# carry, W64# s3 #)
#else
plusWord4 = \ a b c d -> nat2Word64C $! (fromIntegral a + fromIntegral b + fromIntegral c + fromIntegral d)
#endif


{-# INLINE minusWord2 #-}
-- a - b, with borrow flag/bit
minusWord2 :: Word64 -> Word64 -> (# Word64, Word64 #) -- (Borrow flag, Word64)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
minusWord2  = \ (W64# a) (W64# b) ->
    let !diff = minusWord# a b
        -- TODO : Really need a minusWord2# PrimOp.
        !borrow = if isTrue# (ltWord# a b) then 1## else 0##
    in (# W64# borrow, W64# diff #)
#else
minusWord2  = \ a  b ->  let !diff = a - b  -- wrapping default semantics assumed here
                             !borrow = if  a < b then 1 else 0
                             in (# borrow, diff #)
#endif

{-# INLINE minusWord2C #-}
-- | a - (b+c ), with a borrow word (its a borrow not a carry!!!),
minusWord2C :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
minusWord2C  = \ (W64# a) (W64# b) (W64# c) ->
    let !(# W64# c1, W64# sum_wd #) = plusWord2 (W64# b) (W64# c)
        !diff = minusWord# a sum_wd
        !carry = if isTrue# (ltWord# a sum_wd)
           then plusWord# c1 1##  -- need to borrow for subtraction
           else c1 -- no borrow
    in (# W64# carry, W64# diff #)
#else
minusWord2C  = \ a b c ->
    let !(#  c1,  sum_wd #) = plusWord2  b c
        !diff =  a  - sum_wd
        !carry = if  a < sum_wd then c1  +  1 else c1
      in  (# carry, diff #)
#endif


{-# INLINE timesWord2 #-}
-- |  a * b with carry
timesWord2 :: Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
timesWord2  = \ (W64# a) (W64# b) ->
    let !(# !ovf, !prod #) = timesWord2# a b
    in (# W64# ovf, W64# prod #)
#else
timesWord2  = \ a b -> nat2Word64C $! fromIntegral a * fromIntegral b
#endif


{-# INLINE timesWord2C #-}
-- | (a * b) + c with carry,
timesWord2C :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
timesWord2C  = \ (W64# a) (W64# b) (W64# c) ->
    let !(# !ovf, !prod #) = timesWord2# a b
        !(# !cry, !prodc #) = plusWord2# prod c
        !carry = plusWord# ovf cry
    in (# W64# carry, W64# prodc #)
#else
timesWord2C = \ a b c -> nat2Word64C $! (fromIntegral a * fromIntegral b) + fromIntegral c

#endif

{-# INLINE timesWord2CC #-}
-- | a * b + (c + d), with carry,
-- this is safe cause max of a*b is (2^128 -2* 2^64 +1)
-- and max of (word 128) is 2^128 - 1
-- and max of c+d is 2(2^64 - 1)
-- thus max word128 >= max (a*b) + max (c + d)
--       via  2^128 -1 >=  2^128 -2* 2^64 +1)  + 2(2^64 - 1)
--       which simplifies to  2^128 -1 >= 2^128 - 1

timesWord2CC :: Word64 -> Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
#if WORD_SIZE_IN_BITS == 64 &&  !defined(PrimFALLBACK)
timesWord2CC  = \ (W64# a) (W64# b) (W64# c) (W64# d) ->
    let !(# !ovf, !prod #) = timesWord2# a b
        !(# !c1, !sm #) = plusWord2# c d
        !(# !cry, !prodc #) = plusWord2# prod sm
        !carry = plusWord# (plusWord# ovf cry) c1
    in (# W64# carry, W64# prodc #)
#else
timesWord2CC = \ a b c d -> nat2Word64C $! (fromIntegral a * fromIntegral b) + (fromIntegral c + fromIntegral d)
#endif


{-# INLINE shiftLWord2# #-}
-- Assumes shift amount is >= 0 && < WORD_SIZE_IN_BITS.
shiftLWord2# :: Word# -> Word# -> (# Word#, Word# #)
shiftLWord2#  = \ w s ->
    let i# = word2Int# s
    in (# uncheckedShiftRL# w (WORD_SIZE_IN_BITS# -# i#), uncheckedShiftL# w i# #)

{-# INLINE shiftRWord64 #-}
shiftRWord64 :: Word64 -> Int -> Word64
shiftRWord64  = \ (W64# w) (I# i) -> W64# (uncheckedShiftRL# w i)

{-# INLINE quotRemWord64 #-}
quotRemWord64 :: Word64 -> Word64 -> (# Word64, Word64 #)
quotRemWord64  = \ (W64# x) (W64# y) ->
    let !(# q, r #) = quotRemWord# x y
    in (# W64# q, W64# r #)

{-# INLINE quotRemWord2 #-}
quotRemWord2 :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
quotRemWord2  = \ (W64# xhi) (W64# xlo) (W64# y) ->
    let !(# q, r #) = quotRemWord2# xhi xlo y
    in (# W64# q, W64# r #)


{-# INLINE wordSizeInBits #-}
wordSizeInBits :: Int
wordSizeInBits = I# WORD_SIZE_IN_BITS#

{-# INLINE wordSizeInBytes #-}
wordSizeInBytes :: Int
wordSizeInBytes = I# (word2Int# (uncheckedShiftRL# WORD_SIZE_IN_BITS## 3#))


-- this counts offset from lowest order bit ... sortah big (little?!) endian it feels like
{-# INLINE highestSetBit #-}
highestSetBit :: Word64 -> Int
highestSetBit (W64# w) = I# (word2Int# (minusWord# WORD_SIZE_IN_BITS## (clz# w)))


