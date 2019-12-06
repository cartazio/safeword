{-#  LANGUAGE BangPatterns, CPP, ForeignFunctionInterface, MagicHash,
        NoImplicitPrelude, UnboxedTuples, UnliftedFFITypes #-}

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

  ) where

import GHC.Prim
import Data.Word
import GHC.Word(Word64(..))

#include "MachDeps.h"


-- code in part derived from
-- https://github.com/erikd/haskell-big-integer-experiment/blob/master/Common/GHC/Integer/Prim.hs
-- as of January 2017

import GHC.Base (Int (..), Word (..))
import GHC.Float (Double (..))
import GHC.Types (isTrue#)

import Numeric.Natural
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


#if WORD_SIZE_IN_BITS == 64

{-# INLINE plusWord #-}
plusWord :: Word64 -> Word64 -> Word64
plusWord (W64# a) (W64# b) =
    let !s = plusWord# a b
    in W64# s

--- for add with carry, result is (# high word aka carry , low word #)

{-# INLINE plusWord2 #-}
plusWord2 :: Word64 -> Word64 -> (# Word64, Word64 #)
plusWord2 (W64# a) (W64# b) =
    let (# !c, !s #) = plusWord2# a b
    in (# W64# c, W64# s #)

{-# INLINE plusWord3 #-}
plusWord3 :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
plusWord3 (W64# a) (W64# b) (W64# c) =
    let (# !c1, !s1 #) = plusWord2# a b
        (# !c2, !s2 #) = plusWord2# s1 c
        !c3 = plusWord# c1 c2
    in (# W64# c3, W64# s2 #)

{-# INLINE plusWord4 #-}
plusWord4 :: Word64 -> Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
plusWord4 (W64# a) (W64# b) (W64# c) (W64# d) =
    let (# !c1, !s1 #) = plusWord2# a b
        (# !c2, !s2 #) = plusWord2# c d
        (# !c3, !s3 #) = plusWord2# s1 s2
        !c4 = plusWord# c1 c2
        !carry = plusWord# c3 c4
    in (# W64# carry, W64# s3 #)

{-# INLINE minusWord2 #-}
minusWord2 :: Word64 -> Word64 -> (# Word64, Word64 #)
minusWord2 (W64# a) (W64# b) =
    let !diff = minusWord# a b
        -- TODO : Really need a minusWord2# PrimOp.
        !borrow = if isTrue# (ltWord# a b) then 1## else 0##
    in (# W64# borrow, W64# diff #)

{-# INLINE minusWord2C #-}
minusWord2C :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
minusWord2C (W64# a) (W64# b) (W64# c) =
    let (# W64# c1, W64# sum #) = plusWord2 (W64# b) (W64# c)
        !diff = minusWord# a sum
        !carry = if isTrue# (ltWord# a sum) then plusWord# c1 1## else c1
    in (# W64# carry, W64# diff #)

{-# INLINE timesWord2 #-}
timesWord2 :: Word64 -> Word64 -> (# Word64, Word64 #)
timesWord2 (W64# a) (W64# b) =
    let (# !ovf, !prod #) = timesWord2# a b
    in (# W64# ovf, W64# prod #)

{-# INLINE timesWord2C #-}
timesWord2C :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
timesWord2C (W64# a) (W64# b) (W64# c) =
    let (# !ovf, !prod #) = timesWord2# a b
        (# !cry, !prodc #) = plusWord2# prod c
        !carry = plusWord# ovf cry
    in (# W64# carry, W64# prodc #)

{-# INLINE timesWord2CC #-}
timesWord2CC :: Word64 -> Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
timesWord2CC (W64# a) (W64# b) (W64# c) (W64# d) =
    let (# !ovf, !prod #) = timesWord2# a b
        (# !c1, !sm #) = plusWord2# c d
        (# !cry, !prodc #) = plusWord2# prod sm
        !carry = plusWord# (plusWord# ovf cry) c1
    in (# W64# carry, W64# prodc #)

{-# INLINE shiftLWord2# #-}
-- Assumes shift amount is >= 0 && < WORD_SIZE_IN_BITS.
shiftLWord2# :: Word# -> Word# -> (# Word#, Word# #)
shiftLWord2# w s =
    let i# = word2Int# s
    in (# uncheckedShiftRL# w (WORD_SIZE_IN_BITS# -# i#), uncheckedShiftL# w i# #)

{-# INLINE shiftRWord64 #-}
shiftRWord64 :: Word64 -> Int -> Word64
shiftRWord64 (W64# w) (I# i) = W64# (uncheckedShiftRL# w i)

{-# INLINE quotRemWord64 #-}
quotRemWord64 :: Word64 -> Word64 -> (# Word64, Word64 #)
quotRemWord64 (W64# x) (W64# y) =
    let (# q, r #) = quotRemWord# x y
    in (# W64# q, W64# r #)

{-# INLINE quotRemWord2 #-}
quotRemWord2 :: Word64 -> Word64 -> Word64 -> (# Word64, Word64 #)
quotRemWord2 (W64# xhi) (W64# xlo) (W64# y) =
    let (# q, r #) = quotRemWord2# xhi xlo y
    in (# W64# q, W64# r #)


{-# INLINE wordSizeInBits #-}
wordSizeInBits :: Int
wordSizeInBits = I# WORD_SIZE_IN_BITS#

{-# INLINE wordSizeInBytes #-}
wordSizeInBytes :: Int
wordSizeInBytes = I# (word2Int# (uncheckedShiftRL# WORD_SIZE_IN_BITS## 3#))

{-# INLINE highestSetBit #-}
highestSetBit :: Word64 -> Int
highestSetBit (W64# w) = I# (word2Int# (minusWord# WORD_SIZE_IN_BITS## (clz# w)))

#elif WORD_SIZE_IN_BITS == 32
word2Nat

#else
#error "panic, neither 32 nor 64bit!"
#endif
