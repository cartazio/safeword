-- | This module provides an interface and base instances for unsigned bigword algorithms
module Data.WordKit where


-- | the 'WordKit' class is an algorithmic toolkit for writing all the
-- miscellaneous algorithms you need for arbitrary fixed Big Word
-- data types with for now the presumption that we only care about
-- those whose "digits" are Word64 (uint_64 in c parlance)
-- The main challenge we face is that standard fp combinators
-- dont quite express the data flow we want!
-- we need a left or right zipWith with Carry (for addition)
-- we need a fold/map with a monoidal merge action, but for all the convolution pairs (for multiply)
-- this convolutional fold/map needs to have both carry and no carry variants
-- plus some other stuff i'm overlooking!
class WordKit w where
