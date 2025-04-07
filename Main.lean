import Sp1Poc
import Lake
import Lean

open Lean

namespace Sp1

-- set_option maxHeartbeats 1000000
-- lemma sp1_addOperation
--   -- main local variables
--   (V00 V01 V02 V03 V04 V05 V06 V07 V08 V09 V10 V11 V12 V13 V14 : BabyBear)
--   -- extracted Babybear constraints
--   (C01: 1 * ((V00 + V04 - V08)       * (V00 + V04 - V08       - 256)) = 0)
--   (C02: 1 * ((V01 + V05 - V09 + V12) * (V01 + V05 - V09 + V12 - 256)) = 0)
--   (C03: 1 * ((V02 + V06 - V10 + V13) * (V02 + V06 - V10 + V13 - 256)) = 0)
--   (C04: 1 * ((V03 + V07 - V11 + V14) * (V03 + V07 - V11 + V14 - 256)) = 0)
--   (C05: 1 * (V12 * (V00 + V04 - V08       - 256)) = 0)
--   (C06: 1 * (V13 * (V01 + V05 - V09 + V12 - 256)) = 0)
--   (C07: 1 * (V14 * (V02 + V06 - V10 + V13 - 256)) = 0)
--   (C08: 1 * ((V12 - 1) * (V00 + V04 - V08))       = 0)
--   (C09: 1 * ((V13 - 1) * (V01 + V05 - V09 + V12)) = 0)
--   (C10: 1 * ((V14 - 1) * (V02 + V06 - V10 + V13)) = 0)
--   (C11: 1 * (V12 * (V12 - 1)) = 0)
--   (C12: 1 * (V13 * (V13 - 1)) = 0)
--   (C13: 1 * (V14 * (V14 - 1)) = 0)
--   (C14: 1 * (1 - 1) = 0)
--   -- extracted lookup/permutation argument constraints
--   (C15: V00.val < 256) (C16: V01.val < 256) (C17: V02.val < 256) (C18: V03.val < 256)
--   (C19: V04.val < 256) (C20: V05.val < 256) (C21: V06.val < 256) (C22: V07.val < 256)
--   (C23: V08.val < 256) (C24: V09.val < 256) (C25: V10.val < 256) (C26: V11.val < 256) :
--     -- human-readable specification of wrap-around byte-by-byte 32-bit addition
--     ( ( V00.val + 256 * V01.val + 65536 * V02.val + 16777216 * V03.val ) +
--       ( V04.val + 256 * V05.val + 65536 * V06.val + 16777216 * V07.val ) ) % 4294967296 =
--     ( V08.val + 256 * V09.val + 65536 * V10.val + 16777216 * V11.val )
--      := by sorry
-- --   simp [sub_eq_zero (b := (1 : BabyBear))] at *
-- --   rcases C11 <;> rcases C12 <;> rcases C13 <;> subst_eqs <;>
-- --   simp [BabyBearPrime, Fin.add_def, Fin.sub_def] at * <;>
-- --   omega

end Sp1

open Sp1 in
unsafe def main (args : List String) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  enableInitializersExecution
  cli.validate args
