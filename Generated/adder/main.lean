import Sp1Poc 
namespace Sp1 

def spec_0
  (ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 : BabyBear) : Prop :=
    ( ( ML0.val + 256 * ML1.val + 65536 * ML2.val + 16777216 * ML3.val ) +
      ( ML4.val + 256 * ML5.val + 65536 * ML6.val + 16777216 * ML7.val ) ) % 4294967296 =
    ( ML8.val + 256 * ML9.val + 65536 * ML10.val + 16777216 * ML11.val )

set_option maxHeartbeats 1000000 in
theorem lemma_0
  {ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 : BabyBear}
  (C00 : if 1 = 1 then (ML0 < 256 ∧ ML1 < 256) else True)
  (C01 : if 1 = 1 then (ML2 < 256 ∧ ML3 < 256) else True)
  (C02 : if 1 = 1 then (ML4 < 256 ∧ ML5 < 256) else True)
  (C03 : if 1 = 1 then (ML6 < 256 ∧ ML7 < 256) else True)
  (C04 : if 1 = 1 then (ML8 < 256 ∧ ML9 < 256) else True)
  (C05 : if 1 = 1 then (ML10 < 256 ∧ ML11 < 256) else True)
  (C06 : True)
  (C07 : True)
  (C08 : True)
  (C09 : (((ML0 + ML4) - ML8) * (((ML0 + ML4) - ML8) - 256)) = 0)
  (C10 : ((((ML1 + ML5) - ML9) + ML12) * ((((ML1 + ML5) - ML9) + ML12) - 256)) = 0)
  (C11 : ((((ML2 + ML6) - ML10) + ML13) * ((((ML2 + ML6) - ML10) + ML13) - 256)) = 0)
  (C12 : ((((ML3 + ML7) - ML11) + ML14) * ((((ML3 + ML7) - ML11) + ML14) - 256)) = 0)
  (C13 : (ML12 * (((ML0 + ML4) - ML8) - 256)) = 0)
  (C14 : (ML13 * ((((ML1 + ML5) - ML9) + ML12) - 256)) = 0)
  (C15 : (ML14 * ((((ML2 + ML6) - ML10) + ML13) - 256)) = 0)
  (C16 : ((ML12 - 1) * ((ML0 + ML4) - ML8)) = 0)
  (C17 : ((ML13 - 1) * (((ML1 + ML5) - ML9) + ML12)) = 0)
  (C18 : ((ML14 - 1) * (((ML2 + ML6) - ML10) + ML13)) = 0)
  (C19 : (ML12 * (ML12 - 1)) = 0)
  (C20 : (ML13 * (ML13 - 1)) = 0)
  (C21 : (ML14 * (ML14 - 1)) = 0) : spec_0 ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 := by
  unfold spec_0
  simp [sub_eq_zero (b := (1 : BabyBear))] at *; casesm* _ ∧ _; rw [Fin.lt_iff_val_lt_val] at *
  rcases C19 <;> rcases C20 <;> rcases C21 <;> subst_eqs <;>
  simp [BabyBearPrime, Fin.add_def, Fin.sub_def] at * <;>
  omega

end Sp1
