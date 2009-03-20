{- ----------------------------------------------------------------------------------------
   what    : library Data.Bits, for Int variants
   expected: ok
---------------------------------------------------------------------------------------- -}

module DataBitsInt1 where

import Data.Bits
import Data.Int

main :: IO ()
main
  = do putStrLn ("Int8:")
       putStrLn (show (bitSize (2 :: Int8)))
       putStrLn (show (2 .&. 1 :: Int8))
       putStrLn (show (2 .|. 1 :: Int8))
       putStrLn (show ((2 :: Int8) `shiftL` (1 :: Int)))
       putStrLn (show ((2 :: Int8) `shiftR` (1 :: Int)))
       putStrLn (show ((-2 :: Int8) `shiftL` (1 :: Int)))
       putStrLn (show ((-2 :: Int8) `shiftR` (1 :: Int)))
       putStrLn (show (bit 1 :: Int8))
       putStrLn (show (complement 2 :: Int8))
       putStrLn (show ((2 :: Int8) `testBit` (1 :: Int)))
       putStrLn (show ((2 :: Int8) `testBit` (2 :: Int)))
       putStrLn (show ((2 :: Int8) `complementBit` (1 :: Int)))
       putStrLn (show ((2 :: Int8) `complementBit` (2 :: Int)))
       putStrLn (show ((2 :: Int8) `rotateL` (2 :: Int)))
       putStrLn (show ((2 :: Int8) `rotateR` (2 :: Int)))

       putStrLn ("\nInt16:")
       putStrLn (show (bitSize (2 :: Int16)))
       putStrLn (show (2 .&. 1 :: Int16))
       putStrLn (show (2 .|. 1 :: Int16))
       putStrLn (show ((2 :: Int16) `shiftL` (1 :: Int)))
       putStrLn (show ((2 :: Int16) `shiftR` (1 :: Int)))
       putStrLn (show ((-2 :: Int16) `shiftL` (1 :: Int)))
       putStrLn (show ((-2 :: Int16) `shiftR` (1 :: Int)))
       putStrLn (show (bit 1 :: Int16))
       putStrLn (show (complement 2 :: Int16))
       putStrLn (show ((2 :: Int16) `testBit` (1 :: Int)))
       putStrLn (show ((2 :: Int16) `testBit` (2 :: Int)))
       putStrLn (show ((2 :: Int16) `complementBit` (1 :: Int)))
       putStrLn (show ((2 :: Int16) `complementBit` (2 :: Int)))
       putStrLn (show ((2 :: Int16) `rotateL` (2 :: Int)))
       putStrLn (show ((2 :: Int16) `rotateR` (2 :: Int)))

       putStrLn ("\nInt32:")
       putStrLn (show (bitSize (2 :: Int32)))
       putStrLn (show (2 .&. 1 :: Int32))
       putStrLn (show (2 .|. 1 :: Int32))
       putStrLn (show ((2 :: Int32) `shiftL` (1 :: Int)))
       putStrLn (show ((2 :: Int32) `shiftR` (1 :: Int)))
       putStrLn (show ((-2 :: Int32) `shiftL` (1 :: Int)))
       putStrLn (show ((-2 :: Int32) `shiftR` (1 :: Int)))
       putStrLn (show (bit 1 :: Int32))
       putStrLn (show (complement 2 :: Int32))
       putStrLn (show ((2 :: Int32) `testBit` (1 :: Int)))
       putStrLn (show ((2 :: Int32) `testBit` (2 :: Int)))
       putStrLn (show ((2 :: Int32) `complementBit` (1 :: Int)))
       putStrLn (show ((2 :: Int32) `complementBit` (2 :: Int)))
       putStrLn (show ((2 :: Int32) `rotateL` (2 :: Int)))
       putStrLn (show ((2 :: Int32) `rotateR` (2 :: Int)))

       putStrLn ("\nInt64:")
       putStrLn (show (bitSize (2 :: Int64)))
       putStrLn (show (2 .&. 1 :: Int64))
       putStrLn (show (2 .|. 1 :: Int64))
       putStrLn (show ((2 :: Int64) `shiftL` (1 :: Int)))
       putStrLn (show ((2 :: Int64) `shiftR` (1 :: Int)))
       putStrLn (show ((-2 :: Int64) `shiftL` (1 :: Int)))
       putStrLn (show ((-2 :: Int64) `shiftR` (1 :: Int)))
       putStrLn (show (bit 1 :: Int64))
       putStrLn (show (complement 2 :: Int64))
       putStrLn (show ((2 :: Int64) `testBit` (1 :: Int)))
       putStrLn (show ((2 :: Int64) `testBit` (2 :: Int)))
       putStrLn (show ((2 :: Int64) `complementBit` (1 :: Int)))
       putStrLn (show ((2 :: Int64) `complementBit` (2 :: Int)))
       putStrLn (show ((2 :: Int64) `rotateL` (2 :: Int)))
       putStrLn (show ((2 :: Int64) `rotateR` (2 :: Int)))

       putStrLn ("\nInt:")
       putStrLn (show (bitSize (2 :: Int)))
       putStrLn (show (2 .&. 1 :: Int))
       putStrLn (show (2 .|. 1 :: Int))
       putStrLn (show ((2 :: Int) `shiftL` (1 :: Int)))
       putStrLn (show ((2 :: Int) `shiftR` (1 :: Int)))
       putStrLn (show ((-2 :: Int) `shiftL` (1 :: Int)))
       putStrLn (show ((-2 :: Int) `shiftR` (1 :: Int)))
       putStrLn (show (bit 1 :: Int))
       putStrLn (show (complement 2 :: Int))
       putStrLn (show ((2 :: Int) `testBit` (1 :: Int)))
       putStrLn (show ((2 :: Int) `testBit` (2 :: Int)))
       putStrLn (show ((2 :: Int) `complementBit` (1 :: Int)))
       putStrLn (show ((2 :: Int) `complementBit` (2 :: Int)))
       putStrLn (show ((2 :: Int) `rotateL` (2 :: Int)))
       putStrLn (show ((2 :: Int) `rotateR` (2 :: Int)))
