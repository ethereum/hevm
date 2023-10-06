module EVM.FeeSchedule where

import Data.Word (Word64)

class FeeSchedule n where
  g_zero :: n
  g_base :: n
  g_verylow :: n
  g_low :: n
  g_mid :: n
  g_high :: n
  g_extcode :: n
  g_balance :: n
  g_sload :: n
  g_jumpdest :: n
  g_sset :: n
  g_sreset :: n
  r_sclear :: n
  g_selfdestruct :: n
  g_selfdestruct_newaccount :: n
  r_selfdestruct :: n
  g_create :: n
  g_codedeposit :: n
  g_call :: n
  g_callvalue :: n
  g_callstipend :: n
  g_newaccount :: n
  g_exp :: n
  g_expbyte :: n
  g_memory :: n
  g_txcreate :: n
  g_txdatazero :: n
  g_txdatanonzero :: n
  g_transaction :: n
  g_log :: n
  g_logdata :: n
  g_logtopic :: n
  g_sha3 :: n
  g_sha3word :: n
  g_initcodeword :: n
  g_copy :: n
  g_blockhash :: n
  g_extcodehash :: n
  g_quaddivisor :: n
  g_ecadd :: n
  g_ecmul :: n
  g_pairing_point :: n
  g_pairing_base :: n
  g_fround :: n
  r_block :: n
  g_cold_sload :: n
  g_cold_account_access :: n
  g_warm_storage_read :: n
  g_access_list_address :: n
  g_access_list_storage_key :: n

instance FeeSchedule Word64 where
  {-# INLINE g_zero #-}
  g_zero = 0
  {-# INLINE g_base #-}
  g_base = 2
  {-# INLINE g_verylow #-}
  g_verylow = 3
  {-# INLINE g_low #-}
  g_low = 5
  {-# INLINE g_mid #-}
  g_mid = 8
  {-# INLINE g_high #-}
  g_high = 10
  {-# INLINE g_extcode #-}
  g_extcode = 2600
  {-# INLINE g_balance #-}
  g_balance = 2600
  {-# INLINE g_sload #-}
  g_sload = 100
  {-# INLINE g_jumpdest #-}
  g_jumpdest = 1
  {-# INLINE g_sset #-}
  g_sset = 20000
  {-# INLINE g_sreset #-}
  g_sreset = 2900
  {-# INLINE r_sclear #-}
  r_sclear = 15000
  {-# INLINE g_selfdestruct #-}
  g_selfdestruct = 5000
  {-# INLINE g_selfdestruct_newaccount #-}
  g_selfdestruct_newaccount = 25000
  {-# INLINE r_selfdestruct #-}
  r_selfdestruct = 24000
  {-# INLINE g_create #-}
  g_create = 32000
  {-# INLINE g_codedeposit #-}
  g_codedeposit = 200
  {-# INLINE g_call #-}
  g_call = 2600
  {-# INLINE g_callvalue #-}
  g_callvalue = 9000
  {-# INLINE g_callstipend #-}
  g_callstipend = 2300
  {-# INLINE g_newaccount #-}
  g_newaccount = 25000
  {-# INLINE g_exp #-}
  g_exp = 10
  {-# INLINE g_expbyte #-}
  g_expbyte = 50
  {-# INLINE g_memory #-}
  g_memory = 3
  {-# INLINE g_txcreate #-}
  g_txcreate = 32000
  {-# INLINE g_txdatazero #-}
  g_txdatazero = 4
  {-# INLINE g_txdatanonzero #-}
  g_txdatanonzero = 16
  {-# INLINE g_transaction #-}
  g_transaction = 21000
  {-# INLINE g_log #-}
  g_log = 375
  {-# INLINE g_logdata #-}
  g_logdata = 8
  {-# INLINE g_logtopic #-}
  g_logtopic = 375
  {-# INLINE g_sha3 #-}
  g_sha3 = 30
  {-# INLINE g_sha3word #-}
  g_sha3word = 6
  {-# INLINE g_initcodeword #-}
  g_initcodeword = 2
  {-# INLINE g_copy #-}
  g_copy = 3
  {-# INLINE g_blockhash #-}
  g_blockhash = 20
  {-# INLINE g_extcodehash #-}
  g_extcodehash = 2600
  {-# INLINE g_quaddivisor #-}
  g_quaddivisor = 20
  {-# INLINE g_ecadd #-}
  g_ecadd = 150
  {-# INLINE g_ecmul #-}
  g_ecmul = 6000
  {-# INLINE g_pairing_point #-}
  g_pairing_point = 34000
  {-# INLINE g_pairing_base #-}
  g_pairing_base = 45000
  {-# INLINE g_fround #-}
  g_fround = 1
  {-# INLINE r_block #-}
  r_block = 2000000000000000000
  {-# INLINE g_cold_sload #-}
  g_cold_sload = 2100
  {-# INLINE g_cold_account_access #-}
  g_cold_account_access = 2600
  {-# INLINE g_warm_storage_read #-}
  g_warm_storage_read = 100
  {-# INLINE g_access_list_address #-}
  g_access_list_address = 2400
  {-# INLINE g_access_list_storage_key #-}
  g_access_list_storage_key = 1900
