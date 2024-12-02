module EVM.Concrete where

import Prelude hiding (Word)
import EVM.RLP
import EVM.Types

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Witch (unsafeInto, into)

byteStringSliceWithDefaultZeroes :: Int -> Int -> ByteString -> ByteString
byteStringSliceWithDefaultZeroes offset size bs =
  if size == 0
  then ""
  else
    let bs' = BS.take size (BS.drop offset bs)
    in bs' <> BS.replicate (size - BS.length bs') 0

sliceMemory :: W256 -> W256 -> ByteString -> ByteString
sliceMemory o s =
  byteStringSliceWithDefaultZeroes (unsafeInto o) (unsafeInto s)

writeMemory :: ByteString -> W256 -> W256 -> W256 -> ByteString -> ByteString
writeMemory bs1 n src dst bs0 =
  let
    (a, b) = BS.splitAt (unsafeInto dst) bs0
    a'     = BS.replicate (unsafeInto dst - BS.length a) 0
    -- sliceMemory should work for both cases, but we are using 256 bit
    -- words, whereas ByteString is only defined up to 64 bit. For large n,
    -- src, dst this will cause problems (often in GeneralStateTests).
    -- Later we could reimplement ByteString for 256 bit arguments.
    c      = if src > unsafeInto (BS.length bs1)
             then BS.replicate (unsafeInto n) 0
             else sliceMemory src n bs1
    b'     = BS.drop (unsafeInto n) b
  in
    a <> a' <> c <> b'

createAddress :: Addr -> W64 -> Expr EAddr
createAddress a n = LitAddr . unsafeInto . keccak' . rlpList $ [rlpAddrFull a, rlpWord256 (into n)]

create2Address :: Addr -> W256 -> ByteString -> Expr EAddr
create2Address a s b = LitAddr $ unsafeInto $ keccak' $ mconcat
  [BS.singleton 0xff, word160Bytes a, word256Bytes s, word256Bytes $ keccak' b]
