module EVM.Sign where

import qualified Crypto.Hash as Crypto
import Crypto.Hash (Digest)
import Crypto.PubKey.ECC.ECDSA (signDigestWith, PrivateKey(..), Signature(..))
import Crypto.PubKey.ECC.Types (getCurveByName, CurveName(..), Point(..))
import Crypto.PubKey.ECC.Generate (generateQ)

import EVM.ABI (encodeAbiValue, AbiValue (..))
import qualified Data.ByteString   as BS
import EVM.Types
import EVM.Expr (exprToAddr)


-- Given a secret key, generates the address
deriveAddr :: Integer -> Maybe Addr
deriveAddr sk = case pubPoint of
           PointO -> Nothing
           Point x y ->
             -- See yellow paper #286
               let pub = BS.concat [ encodeInt x, encodeInt y ]
                   addr = Lit . W256 . word256 . BS.drop 12 . BS.take 32 . keccakBytes $ pub
                in exprToAddr addr
         where
          curve = getCurveByName SEC_p256k1
          pubPoint = generateQ curve (num sk)
          encodeInt = encodeAbiValue . AbiUInt 256 . fromInteger


sign :: (Digest Crypto.Keccak_256) -> Integer -> (W256, W256, W256)
sign digest sk = (txR, txS, 27)
  where
    curve = getCurveByName SEC_p256k1
    priv = PrivateKey curve sk
    n = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 :: Integer
    lowS = if sign_s sig > n `div` 2 then n-(sign_s sig)
                               else sign_s sig
    sig = ethsign priv digest
    txR = num $ sign_r sig
    txS = num lowS

-- | We don't wanna introduce the machinery needed to sign with a random nonce,
-- so we just use the same nonce every time (420). This is obviusly very
-- insecure, but fine for testing purposes.
ethsign :: PrivateKey -> Digest Crypto.Keccak_256 -> Signature
ethsign sk digest = go 420
  where
    go k = case signDigestWith k sk digest of
       Nothing  -> go (k + 1)
       Just sig -> sig


