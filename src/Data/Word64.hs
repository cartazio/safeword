{- | Data.Word64 is an implementation of


-}

{-# LANGUAGE BangPatterns, MagicHash #-}
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
data Word64 = W64# Word# Word#
#else
#error "uh oh, word is neither 32 or 64 bit"
#endif


#if WORD_SIZE_IN_BITS == 32

instance Num Word64



#endif




