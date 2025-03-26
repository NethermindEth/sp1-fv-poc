import Sp1Poc

set_option maxHeartbeats 1000000
lemma sp1_addOperation
  -- main local variables
  (V00 V01 V02 V03 V04 V05 V06 V07 V08 V09 V10 V11 V12 V13 V14 : BabyBear)
  -- extracted Babybear constraints
  (C01:  (V00 + V04) - V08        = 0 ∨  (V00 + V04) - V08        = 256)
  (C02: ((V01 + V05) - V09) + V12 = 0 ∨ ((V01 + V05) - V09) + V12 = 256)
  (C03: ((V02 + V06) - V10) + V13 = 0 ∨ ((V02 + V06) - V10) + V13 = 256)
  (C04: ((V03 + V07) - V11) + V14 = 0 ∨ ((V03 + V07) - V11) + V14 = 256)
  (C05: V12 = 0 ∨  (V00 + V04) - V08        = 256)
  (C06: V13 = 0 ∨ ((V01 + V05) - V09) + V12 = 256)
  (C07: V14 = 0 ∨ ((V02 + V06) - V10) + V13 = 256)
  (C08: V12 = 1 ∨  (V00 + V04) - V08        = 0)
  (C09: V13 = 1 ∨ ((V01 + V05) - V09) + V12 = 0)
  (C10: V14 = 1 ∨ ((V02 + V06) - V10) + V13 = 0)
  (C11: V12 = 0 ∨ V12 = 1)
  (C12: V13 = 0 ∨ V13 = 1)
  (C13: V14 = 0 ∨ V14 = 1)
  (C14: 0 = 0)
  -- extracted lookup/permutation argument constraints
  (C15: V00.val < 256) (C16: V01.val < 256) (C17: V02.val < 256) (C18: V03.val < 256)
  (C19: V04.val < 256) (C20: V05.val < 256) (C21: V06.val < 256) (C22: V07.val < 256)
  (C23: V08.val < 256) (C24: V09.val < 256) (C25: V10.val < 256) (C26: V11.val < 256) :
    -- human-readable specification of wrap-around byte-by-byte 32-bit addition
    ( ( V00.val + 256 * V01.val + 65536 * V02.val + 16777216 * V03.val ) +
      ( V04.val + 256 * V05.val + 65536 * V06.val + 16777216 * V07.val ) ) % 4294967296 =
    ( V08.val + 256 * V09.val + 65536 * V10.val + 16777216 * V11.val )
     := by
  -- constrains not required as implied by the other constraints
  clear C01 C02 C03 C14

  rcases C11 with C11 | C11 <;>
  rcases C12 with C12 | C12 <;>
  rcases C13 with C13 | C13 <;>
  rcases C04 with C04 | C04 <;> subst_eqs <;>
  simp [Fin.add_def, Fin.sub_def, ←sub_eq_zero, BabyBearPrime] at * <;> simp at * <;> omega
