import Sp1Poc.Specs

namespace Sp1

def spec_ML16_1
  (ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 : BabyBear) : Prop :=
  (ML16 = 1) →
    spec_32_bit_wrap_add ML1 ML2 ML3 ML4 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15

set_option maxHeartbeats 1000000 in
theorem conformance_ML16_1
  {ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 : BabyBear}
  (C00 :
    if ML16 = 0 then True else
    if ML16 = 1
    then match 4 with
         | 4 => if ML16 = 1
                then ML8.val < 256 ∧ ML9.val < 256
                else if ML16 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C01 :
    if ML16 = 0 then True else
    if ML16 = 1
    then match 4 with
         | 4 => if ML16 = 1
                then ML10.val < 256 ∧ ML11.val < 256
                else if ML16 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C02 :
    if ML16 = 0 then True else
    if ML16 = 1
    then match 4 with
         | 4 => if ML16 = 1
                then ML12.val < 256 ∧ ML13.val < 256
                else if ML16 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C03 :
    if ML16 = 0 then True else
    if ML16 = 1
    then match 4 with
         | 4 => if ML16 = 1
                then ML14.val < 256 ∧ ML15.val < 256
                else if ML16 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C04 :
    if ML16 = 0 then True else
    if ML16 = 1
    then match 4 with
         | 4 => if ML16 = 1
                then ML1.val < 256 ∧ ML2.val < 256
                else if ML16 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C05 :
    if ML16 = 0 then True else
    if ML16 = 1
    then match 4 with
         | 4 => if ML16 = 1
                then ML3.val < 256 ∧ ML4.val < 256
                else if ML16 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C06 : if (ML17 * 2013265920) = 0 || (ML17 * 2013265920) = BabyBearPrime - 1 then True else undefined)
  (C07 : if (ML18 * 2013265920) = 0 || (ML18 * 2013265920) = BabyBearPrime - 1 then True else undefined)
  (C08 : True)
  (C09 : True)
  (C10 : True)
  (C11 : (ML17 * (ML17 - 1)) = 0)
  (C12 : (ML18 * (ML18 - 1)) = 0)
  (C13 : ((ML17 + ML18) * ((ML17 + ML18) - 1)) = 0)
  (C14 : (ML16 * (((ML8 + ML12) - ML1) * (((ML8 + ML12) - ML1) - 256))) = 0)
  (C15 : (ML16 * ((((ML9 + ML13) - ML2) + ML5) * ((((ML9 + ML13) - ML2) + ML5) - 256))) = 0)
  (C16 : (ML16 * ((((ML10 + ML14) - ML3) + ML6) * ((((ML10 + ML14) - ML3) + ML6) - 256))) = 0)
  (C17 : (ML16 * ((((ML11 + ML15) - ML4) + ML7) * ((((ML11 + ML15) - ML4) + ML7) - 256))) = 0)
  (C18 : (ML16 * (ML5 * (((ML8 + ML12) - ML1) - 256))) = 0)
  (C19 : (ML16 * (ML6 * ((((ML9 + ML13) - ML2) + ML5) - 256))) = 0)
  (C20 : (ML16 * (ML7 * ((((ML10 + ML14) - ML3) + ML6) - 256))) = 0)
  (C21 : (ML16 * ((ML5 - 1) * ((ML8 + ML12) - ML1))) = 0)
  (C22 : (ML16 * ((ML6 - 1) * (((ML9 + ML13) - ML2) + ML5))) = 0)
  (C23 : (ML16 * ((ML7 - 1) * (((ML10 + ML14) - ML3) + ML6))) = 0)
  (C24 : (ML16 * (ML5 * (ML5 - 1))) = 0)
  (C25 : (ML16 * (ML6 * (ML6 - 1))) = 0)
  (C26 : (ML16 * (ML7 * (ML7 - 1))) = 0)
  (C27 : (ML16 * (ML16 * (ML16 - 1))) = 0)
  (C28 : (ML16 * ((ML17 + ML18) - 1)) = 0) : spec_ML16_1 ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 := by
    unfold spec_ML16_1; intro HML16; unfold spec_32_bit_wrap_add
    subst_eqs; simp [sub_eq_zero (b := (1 : BabyBear))] at *
    rcases C24 <;> rcases C25 <;> rcases C26 <;> subst_eqs <;>
    simp [BabyBearPrime, Fin.add_def, Fin.sub_def] at * <;>
    omega

end Sp1
