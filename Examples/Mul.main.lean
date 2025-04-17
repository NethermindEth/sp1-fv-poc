import Sp1Poc.Specs
namespace Sp1

def spec_ML38_1_MUL
  (ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 ML19 ML20 ML21 ML22 ML23 ML24 ML25 ML26 ML27 ML28 ML29 ML30 ML31 ML32 ML33 ML34 ML35 ML36 ML37 ML38 : BabyBear) : Prop :=
  (ML38 = 1) → (ML13 = 1) →
    ((((ML34 * 10) + (ML35 * 11)) + (ML36 * 12)) + (ML37 * 13)) = 10 →
      spec_32_bit_wrap_mul ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12

set_option maxHeartbeats 5000000 in
theorem conformance_ML38_ML13
  {ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 ML19 ML20 ML21 ML22 ML23 ML24 ML25 ML26 ML27 ML28 ML29 ML30 ML31 ML32 ML33 ML34 ML35 ML36 ML37 ML38 : BabyBear}
  (C00 :
    if ML38 = 1
      then ML8.val < 256 ∧
           (ML8.val < 128 → ML30 = 0) ∧
           (128 ≤ ML8.val → ML30 = 1)
      else if ML38 = 0 then True else undefined)
  (C01 :
    if ML38 = 1
      then ML12.val < 256 ∧
           (ML12.val < 128 → ML31 = 0) ∧
           (128 ≤ ML12.val → ML31 = 1)
      else if ML38 = 0 then True else undefined)
  (C02 :
    if ML38 = 1
      then ML14.val < 65536
      else if ML38 = 0 then True else undefined)
  (C03 :
    if ML38 = 1
      then ML15.val < 65536
      else if ML38 = 0 then True else undefined)
  (C04 :
    if ML38 = 1
      then ML16.val < 65536
      else if ML38 = 0 then True else undefined)
  (C05 :
    if ML38 = 1
      then ML17.val < 65536
      else if ML38 = 0 then True else undefined)
  (C06 :
    if ML38 = 1
      then ML18.val < 65536
      else if ML38 = 0 then True else undefined)
  (C07 :
    if ML38 = 1
      then ML19.val < 65536
      else if ML38 = 0 then True else undefined)
  (C08 :
    if ML38 = 1
      then ML20.val < 65536
      else if ML38 = 0 then True else undefined)
  (C09 :
    if ML38 = 1
      then ML21.val < 65536
      else if ML38 = 0 then True else undefined)
  (C10 :
    if ML38 = 0 then True else
    if ML38 = 1
    then match 4 with
         | 4 => if ML38 = 1
                then ML22.val < 256 ∧ ML23.val < 256
                else if ML38 = 0 then True else undefined
         | 7 => if ML38 = 1
                then ML22.val < 256 ∧
                     (ML22.val < 128 → 0 = 0) ∧
                     (128 ≤ ML22.val → 0 = 1)
                else if ML38 = 0 then True else undefined
         | 8 => if ML38 = 1
                then ML22.val < 65536
                else if ML38 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C11 :
    if ML38 = 0 then True else
    if ML38 = 1
    then match 4 with
         | 4 => if ML38 = 1
                then ML24.val < 256 ∧ ML25.val < 256
                else if ML38 = 0 then True else undefined
         | 7 => if ML38 = 1
                then ML24.val < 256 ∧
                     (ML24.val < 128 → 0 = 0) ∧
                     (128 ≤ ML24.val → 0 = 1)
                else if ML38 = 0 then True else undefined
         | 8 => if ML38 = 1
                then ML24.val < 65536
                else if ML38 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C12 :
    if ML38 = 0 then True else
    if ML38 = 1
    then match 4 with
         | 4 => if ML38 = 1
                then ML26.val < 256 ∧ ML27.val < 256
                else if ML38 = 0 then True else undefined
         | 7 => if ML38 = 1
                then ML26.val < 256 ∧
                     (ML26.val < 128 → 0 = 0) ∧
                     (128 ≤ ML26.val → 0 = 1)
                else if ML38 = 0 then True else undefined
         | 8 => if ML38 = 1
                then ML26.val < 65536
                else if ML38 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C13 :
    if ML38 = 0 then True else
    if ML38 = 1
    then match 4 with
         | 4 => if ML38 = 1
                then ML28.val < 256 ∧ ML29.val < 256
                else if ML38 = 0 then True else undefined
         | 7 => if ML38 = 1
                then ML28.val < 256 ∧
                     (ML28.val < 128 → 0 = 0) ∧
                     (128 ≤ ML28.val → 0 = 1)
                else if ML38 = 0 then True else undefined
         | 8 => if ML38 = 1
                then ML28.val < 65536
                else if ML38 = 0 then True else undefined
         | _ => undefined
    else undefined)
  (C14 :
    if (ML38 * 2013265920) = 0 then True
    else if (ML38 * 2013265920) = 1 ∨ (ML38 * 2013265920) = BabyBearPrime - 1
         then ML1.val < 256 ∧ ML2.val < 256 ∧ ML3.val < 256 ∧ ML4.val < 256 ∧
              ML5.val < 256 ∧ ML6.val < 256 ∧ ML7.val < 256 ∧ ML8.val < 256 ∧
              ML9.val < 256 ∧ ML10.val < 256 ∧ ML11.val < 256 ∧ ML12.val < 256
         else undefined)
  (C15 : True)
  (C16 : True)
  (C17 : True)
  (C18 : (ML32 - (((ML35 + ML37) - (ML35 * ML37)) * ML30)) = 0)
  (C19 : (ML33 - (ML35 * ML31)) = 0)
  (C20 : (ML22 - ((ML5 * ML9) - (ML14 * 256))) = 0)
  (C21 : (ML23 - ((((ML5 * ML10) + (ML6 * ML9)) + ML14) - (ML15 * 256))) = 0)
  (C22 : (ML24 - (((((ML5 * ML11) + (ML6 * ML10)) + (ML7 * ML9)) + ML15) - (ML16 * 256))) = 0)
  (C23 : (ML25 - ((((((ML5 * ML12) + (ML6 * ML11)) + (ML7 * ML10)) + (ML8 * ML9)) + ML16) - (ML17 * 256))) = 0)
  (C24 : (ML26 - (((((((ML5 * (ML33 * 255)) + (ML6 * ML12)) + (ML7 * ML11)) + (ML8 * ML10)) + ((ML32 * 255) * ML9)) + ML17) - (ML18 * 256))) = 0)
  (C25 : (ML27 - ((((((((ML5 * (ML33 * 255)) + (ML6 * (ML33 * 255))) + (ML7 * ML12)) + (ML8 * ML11)) + ((ML32 * 255) * ML10)) + ((ML32 * 255) * ML9)) + ML18) - (ML19 * 256))) = 0)
  (C26 : (ML28 - (((((((((ML5 * (ML33 * 255)) + (ML6 * (ML33 * 255))) + (ML7 * (ML33 * 255))) + (ML8 * ML12)) + ((ML32 * 255) * ML11)) + ((ML32 * 255) * ML10)) + ((ML32 * 255) * ML9)) + ML19) - (ML20 * 256))) = 0)
  (C27 : (ML29 - ((((((((((ML5 * (ML33 * 255)) + (ML6 * (ML33 * 255))) + (ML7 * (ML33 * 255))) + (ML8 * (ML33 * 255))) + ((ML32 * 255) * ML12)) + ((ML32 * 255) * ML11)) + ((ML32 * 255) * ML10)) + ((ML32 * 255) * ML9)) + ML20) - (ML21 * 256))) = 0)
  (C28 : (ML13 * (ML34 * (ML22 - ML1))) = 0)
  (C29 : (ML13 * (((ML35 + ML36) + ML37) * (ML26 - ML1))) = 0)
  (C30 : (ML13 * (ML34 * (ML23 - ML2))) = 0)
  (C31 : (ML13 * (((ML35 + ML36) + ML37) * (ML27 - ML2))) = 0)
  (C32 : (ML13 * (ML34 * (ML24 - ML3))) = 0)
  (C33 : (ML13 * (((ML35 + ML36) + ML37) * (ML28 - ML3))) = 0)
  (C34 : (ML13 * (ML34 * (ML25 - ML4))) = 0)
  (C35 : (ML13 * (((ML35 + ML36) + ML37) * (ML29 - ML4))) = 0)
  (C36 : (ML30 * (ML30 - 1)) = 0)
  (C37 : (ML31 * (ML31 - 1)) = 0)
  (C38 : (ML32 * (ML32 - 1)) = 0)
  (C39 : (ML33 * (ML33 - 1)) = 0)
  (C40 : (ML34 * (ML34 - 1)) = 0)
  (C41 : (ML35 * (ML35 - 1)) = 0)
  (C42 : (ML36 * (ML36 - 1)) = 0)
  (C43 : (ML37 * (ML37 - 1)) = 0)
  (C44 : (ML38 * (ML38 - 1)) = 0)
  (C45 : (ML32 * (ML30 - 1)) = 0)
  (C46 : (ML33 * (ML31 - 1)) = 0)
  (C47 : (ML38 * ((((ML34 + ML35) + ML36) + ML37) - 1)) = 0)
  (C48 : (ML13 * (ML38 - 1)) = 0) : spec_ML38_1_MUL ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 ML19 ML20 ML21 ML22 ML23 ML24 ML25 ML26 ML27 ML28 ML29 ML30 ML31 ML32 ML33 ML34 ML35 ML36 ML37 ML38 := by
    unfold spec_ML38_1_MUL; intros HML38 H_is_real H_op_a_not_0; unfold spec_32_bit_wrap_mul
    subst_eqs; simp_arith [sub_eq_zero (b := (1 : BabyBear))] at *
    have Hopcode: ML34 = 1 ∧ ML35 = 0 ∧ ML36 = 0 ∧ ML37 = 0 := by
      rcases C40 <;> rcases C41 <;> rcases C42 <;> rcases C43 <;> subst_eqs <;> simp
    rcases Hopcode with ⟨ HML34, HML35, HML36, HML37 ⟩
    subst_eqs <;> simp at * <;> subst_eqs <;> simp at *
    simp [sub_eq_zero] at C20 C21 C22 C23 C24 C25 C26 C27; subst_eqs
    simp [sub_eq_zero] at C28 C30 C32 C34; subst_eqs
    clear C15 C16 C17 C29 C31 C33 C35 C38 C39 C40 C41 C42 C43 C45 C46
    rcases C10 with ⟨ C15, C16 ⟩
    rcases C11 with ⟨ C17, C18 ⟩
    rcases C12 with ⟨ C19, C20 ⟩
    rcases C13 with ⟨ C21, C22 ⟩
    rcases C14 with ⟨ C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34 ⟩
    constructor; exact C23
    constructor; exact C24
    constructor; exact C25
    constructor; exact C26
    constructor; exact C27
    constructor; exact C28
    constructor; exact C29
    constructor; exact C30
    constructor; exact C31
    constructor; exact C32
    constructor; exact C33
    constructor; exact C34
    simp [BabyBearPrime, Fin.add_def, Fin.sub_def, Fin.mul_def] at *
    rw [@Nat.mod_eq_of_lt (ML14.val * _) 2013265921,
        @Nat.mod_eq_of_lt (ML15.val * _) 2013265921,
        @Nat.mod_eq_of_lt (ML16.val * _) 2013265921,
        @Nat.mod_eq_of_lt (ML17.val * _) 2013265921] <;> try omega

    have H_ub_5_09 : ML5.val * ML9.val ≤ 65025 := by nlinarith
    have H_ub_6_09 : ML6.val * ML9.val ≤ 65025 := by nlinarith
    have H_ub_7_09 : ML7.val * ML9.val ≤ 65025 := by nlinarith
    have H_ub_8_09 : ML8.val * ML9.val ≤ 65025 := by nlinarith
    have H_ub_5_10 : ML5.val * ML10.val ≤ 65025 := by nlinarith
    have H_ub_6_10 : ML6.val * ML10.val ≤ 65025 := by nlinarith
    have H_ub_7_10 : ML7.val * ML10.val ≤ 65025 := by nlinarith
    have H_ub_5_11 : ML5.val * ML11.val ≤ 65025 := by nlinarith
    have H_ub_6_11 : ML6.val * ML11.val ≤ 65025 := by nlinarith
    have H_ub_5_12 : ML5.val * ML12.val ≤ 65025 := by nlinarith

    have H_14_lb: ML14.val * 256 ≤ ML5.val * ML9.val := by omega
    have H_14_ub: ML5.val * ML9.val < (ML14.val + 1) * 256 := by omega
    have H_15_lb: ML15.val * 256 ≤ (ML5.val * ML10.val) + (ML6.val * ML9.val) + ML14.val := by omega
    have H_15_ub: (ML5.val * ML10.val) + (ML6.val * ML9.val) + ML14 < (ML15.val + 1) * 256 := by omega
    have H_16_lb: ML16.val * 256 ≤ (((↑ML5 * ↑ML11) + (↑ML6 * ↑ML10)) + (↑ML7 * ↑ML9)) + ↑ML15 := by omega
    have H_16_ub: (((↑ML5 * ↑ML11) + (↑ML6 * ↑ML10)) + (↑ML7 * ↑ML9)) + ↑ML15 < (ML16.val + 1) * 256 := by omega
    have H_17_lb: ML17.val * 256 ≤ ((((↑ML5 * ↑ML12) + (↑ML6 * ↑ML11)) + (↑ML7 * ↑ML10)) + (↑ML8 * ↑ML9)) + ↑ML16 := by omega
    have H_17_ub: ((((↑ML5 * ↑ML12) + (↑ML6 * ↑ML11)) + (↑ML7 * ↑ML10)) + (↑ML8 * ↑ML9)) + ↑ML16 < (ML17.val + 1) * 256 := by omega

    ring_nf; omega

end Sp1
