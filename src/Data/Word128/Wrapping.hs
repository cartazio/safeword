{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Data.Word128.Wrapping(
  --Word64(..)
  --,Word32(..)
  Word128(..)
  ,nativeWordSize
 )where

import Data.Word(
                Word64
                --,byteSwap32,byteSwap64
                )
import Data.Data (Data,Typeable)
import Data.Bits
import  qualified Data.CarryUtils.Word64 as CU64

#include "MachDeps.h"

nativeWordSize :: Word64
nativeWordSize = WORD_SIZE_IN_BITS

{-{-# inline oneBits #-}
oneBits :: (FiniteBits b) => b
oneBits = complement zeroBits
-}

#if WORD_SIZE_IN_BITS == 64 || WORD_SIZE_IN_BITS == 32
data Word128 =
    W128# {-# UNPACK #-} !Word64  -- high bits
          {-# UNPACK #-} !Word64  -- low bits
    deriving(Eq,Data,Typeable)

data Word256 =
    W256# {-# UNPACK #-} !Word128  -- high bits
          {-# UNPACK #-} !Word128  -- low bits
    deriving(Eq,Data,Typeable)
#else
#error "this is very strange, your platform isn't Word 32/64 native"
#endif
-- NB on 32bit systems we *may* be able to do a faster Ord Word128 instance
-- but this depends on the rep of word64 in that context
-- so not doing for now




instance Ord Word128 where
  compare = \  (W128# hw1 lw1) (W128# hw2 lw2) ->
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


{-

Prelude Data.Bits> map (\x -> (x , x .&. 7 )) $ [-8 ..  8] :: [(Int,Int)]
[(-8,0),(-7,1),(-6,2),(-5,3),(-4,4),(-3,5),(-2,6),(-1,7),(0,0),(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,0)]

-}

instance Bits Word128 where
    --{-# INLINE shift #-}
    {-# INLINE bit #-}
    {-# INLINE testBit #-}
    zeroBits = W128# 0 0
    {-# INLINE (.&.) #-}
    {-# INLINE (.|.) #-}
    {-# INLINE xor #-}
    (W128# hw1 lw1) .&.   (W128# hw2 lw2)  = W128# (hw1 .&. hw2) (lw1 .&. lw2)
    (W128# hw1 lw1) .|.   (W128# hw2 lw2)  = W128# (hw1 .|. hw2) (lw1 .|. lw2)
    (W128# hw1 lw1) `xor` (W128# hw2 lw2)  = W128# (hw1 `xor` hw2) (lw1 `xor` lw2)
    complement (W128# hw1 lw1)       = W128# (complement hw1) (complement lw1)
    x@(W128# _hw1 _lw1) `shift`   i | i<0       = x `shiftR` (-i)
                  | i>0       = x `shiftL` i
                  | otherwise = x
    w@(W128# _hw1 _lw1) `shiftL`   i | i >= 0  =  unsafeShiftL w i
              | otherwise = error "negative argument to shiftL Word128"
    (W128# hw lw) `unsafeShiftL` i =  W128# ((hw `unsafeShiftL` i)
                                              .|. (lw `shift` (i - 64)) )
                                            (lw `unsafeShiftL` i ) -- need to add negative handler
    w@(W128# _hw _lw) `shiftR`  i | i >= 0  =   unsafeShiftR w i
                               | otherwise = error  "negative index for shiftR Word128"
    (W128# hw lw) `unsafeShiftR` i       = W128# (hw `unsafeShiftR` i')  -- need to add negative handler
                                           ((hw `shift` negate (i - 64) )  .|.  (lw  `unsafeShiftR` i))
                               where
                                  !i' = i .&. 127
    w@(W128# _hw1 _lw1) `rotate` i = unsafeShiftL w modi  .|. unsafeShiftR w modtrani
        where
                    modi =  i .&. 127  -- equiv to  i `mod` 128
                    modtrani = 128 - modi
    --bw@(W128# hw lw) `rotateL` i
    --                            | i < 0 = error "negative Int argument to rotateL Word128"
    --                            | otherwise = W128# ((hw `unsafeShiftL` modi) .|. (lw `shift` modtrani))
    --                                                ((lw `unsafeShiftL` modi) .|. (hw `shift` modtrani))
    --            where
    --                modi =  i .&. 127  -- equiv to  i `mod` 128
    --                modtrani = modi - 64
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
  finiteBitSize  = \ _ -> 128
  -- todo: is there a better way to implement CLZ and CTZ?
  countLeadingZeros (W128# hw lw)  | hw /= 0 = countLeadingZeros hw
                                   | otherwise = 64 + countLeadingZeros lw

  countTrailingZeros (W128# hw lw) | lw /= 0 = countTrailingZeros lw
                                   | otherwise = 64 + countTrailingZeros hw

twosComplementNegateW128 :: Word128 -> Word128
twosComplementNegateW128 =  \ w ->  (complement w) + 1

--intMinBound, intMaxBound :: Integer
--intMaxBound = fromIntegral (maxBound :: Int)
--intMinBound = fromIntegral (minBound :: Int )

--word128IntegerMask :: Integer
--word128IntegerMask = 0xffffffffffffffffffffffffffffffff

--word64IntegerMask :: Integer
--word64IntegerMask = 0xffffffffffffffff
  --where
    --ones64 = complement (zeroBits :: Word64)




instance Num Word128 where
  (*) = \ (W128# hix lowx) (W128# hiy lowy ) ->
           let (# !lo2hiCarry , !lowres #)  = CU64.timesWord2 lowx lowy
           in  W128# (lowx * hiy + lowy* hix + lo2hiCarry) lowres
           -- we drop/dont use the carry bits or the  hix * hiy bits because
           -- we are doing wrapping math!

  (+) = \ (W128# hw1 lw1) (W128# hw2 lw2) ->
              let
                !(# hwcarry, lwres #) = CU64.plusWord2 lw1 lw2
                !(# _hhwcarry, hwres #) = CU64.plusWord3 hw1 hw2 hwcarry
                in
                  W128# hwres lwres
  abs = id
  signum = \ x ->  if x == W128# 0 0 then 0 else 1
  -- negate is kinda a strange critter on unsigned things :)
  negate = \ w -> twosComplementNegateW128 w
  -- binary int == "bin int" == bint shorthand,
  fromInteger bint |  bint >= fromIntegral (minBound :: Int)
                      && bint <= fromIntegral (maxBound :: Int)
                    = W128# 0 (fromIntegral (fromInteger bint :: Int ))
                  | bint > fromIntegral (maxBound :: Int)
                      = W128# (fromInteger $ (bint `unsafeShiftR` 64)) (fromInteger bint)
                  | otherwise -- negative and smaller than minBound:: Int
                      = let nbint = negate bint
                          in
                            fromInteger nbint

instance Real Word128 where
   toRational = \ wd ->      fromIntegral wd

instance Enum Word128 where
  fromEnum  = error "you called fromEnum on Word128, think about your goals and fix the code"
  toEnum = error "you called toEnum to convert an int to word128, think about this and be the change in your code"
  succ = \ x -> x + 1
  pred = \ x -> x - 1
  enumFrom x =  x : enumFrom (1 + x )
  enumFromTo lo hi | hi < lo = []
                   | otherwise =  lo : enumFromTo (lo + 1) hi
  enumFromThen lo loplusdelta =  enumFromDelta lo (loplusdelta - lo)
    where
      enumFromDelta mlo delta = mlo : enumFromDelta (mlo + delta) delta

  enumFromThenTo lo loplusdelta hi  = enumFromDeltaTo lo (loplusdelta - lo )
    where
      enumFromDeltaTo xlo delta  | xlo > hi = []
                                 | otherwise = xlo : enumFromDeltaTo (xlo + delta)  delta


{-
conceptually, at first you might think "how can we nicely define
 divmod for these big words in a nice way"
 option a) long division!
 option b)


type Integral :: * -> Constraint
class (Real a, Enum a) => Integral a where
  quot :: a -> a -> a
  rem :: a -> a -> a
  div :: a -> a -> a
  mod :: a -> a -> a
  quotRem :: a -> a -> (a, a)
  divMod :: a -> a -> (a, a)
  toInteger :: a -> Integer
  {-# MINIMAL quotRem, toInteger #-}
-}

instance Integral Word128 where
  toInteger  = \ (W128# hi lo) ->   unsafeShiftL (toInteger hi ) 64 + toInteger lo
  --divMod = \ num denom  ->  undefined
  quotRem = \ num@(W128# hiN loN) dem@(W128# hiD loD) ->
              if (hiD == 0 && loD == 0 ) then error "division by zero in  quotRem"
                else undefined hiD loD hiN loN dem num
  divMod = quotRem
  div = undefined
  quot = undefined



{-













-}


