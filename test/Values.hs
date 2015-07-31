{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
module Values where

import Data.Set as Set (Set, fromList)
import Language.Haskell.TH.Instances ()

bitsInstances :: Set String
bitsInstances =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
      "instance Bits CChar","instance Bits CInt","instance Bits CIntMax","instance Bits CIntPtr","instance Bits CLLong","instance Bits CLong","instance Bits CPtrdiff","instance Bits CSChar","instance Bits CShort","instance Bits CSigAtomic","instance Bits CSize","instance Bits CUChar","instance Bits CUInt","instance Bits CUIntMax","instance Bits CUIntPtr","instance Bits CULLong","instance Bits CULong","instance Bits CUShort","instance Bits CWchar",
#endif
      "instance Bits Bool","instance Bits Int","instance Bits Integer","instance Bits Word","instance Bits Word16","instance Bits Word32","instance Bits Word64","instance Bits Word8",
      -- These come and go depending on the version of something.
      "instance Bits Int16","instance Bits Int32","instance Bits Int64","instance Bits Int8","instance Bits Natural"
    ]

enumInstances :: Set String
enumInstances =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
      "instance Enum (Fixed a)","instance Enum (Proxy s)","instance Enum (f a) => Enum (Alt f a)","instance Enum CChar","instance Enum CClock","instance Enum CDouble","instance Enum CFloat","instance Enum CInt","instance Enum CIntMax","instance Enum CIntPtr","instance Enum CLLong","instance Enum CLong","instance Enum CPtrdiff","instance Enum CSChar","instance Enum CSUSeconds","instance Enum CShort","instance Enum CSigAtomic","instance Enum CSize","instance Enum CTime","instance Enum CUChar","instance Enum CUInt","instance Enum CUIntMax","instance Enum CUIntPtr","instance Enum CULLong","instance Enum CULong","instance Enum CUSeconds","instance Enum CUShort","instance Enum CWchar","instance Enum Day","instance Enum NominalDiffTime",
#endif
      "instance Enum ()","instance Enum Bool","instance Enum Char","instance Enum Double","instance Enum Float","instance Enum Int","instance Enum Int16","instance Enum Int32","instance Enum Int64","instance Enum Int8","instance Enum Integer","instance Enum Natural","instance Enum Ordering","instance Enum Word","instance Enum Word16","instance Enum Word32","instance Enum Word64","instance Enum Word8","instance Integral a => Enum (Ratio a)"
    ]

arrayInstances :: Set String
arrayInstances =
  Set.fromList ["instance IArray UArray (FunPtr a)",
                "instance IArray UArray (Ptr a)",
                "instance IArray UArray (StablePtr a)",
                "instance IArray UArray Bool",
                "instance IArray UArray Char",
                "instance IArray UArray Double",
                "instance IArray UArray Float",
                "instance IArray UArray Int",
                "instance IArray UArray Int16",
                "instance IArray UArray Int32",
                "instance IArray UArray Int64",
                "instance IArray UArray Int8",
                "instance IArray UArray Word",
                "instance IArray UArray Word16",
                "instance IArray UArray Word32",
                "instance IArray UArray Word64",
                "instance IArray UArray Word8"]

class MyClass a
class MyMPClass a b
data Wrapper a = Wrapper a

instance MyClass Int
instance MyClass a => MyClass (Wrapper a)

instance MyMPClass a Int
instance MyMPClass a b => MyMPClass a (Wrapper b)
