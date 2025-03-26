import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921
abbrev BabyBear : Type := Fin BabyBearPrime
instance : NeZero BabyBearPrime := by constructor; decide

@[simp]
lemma lt_Bear : 256 < BabyBearPrime := by decide

lemma bb_val_ofNat {x : ℕ} (Hlt : x < BabyBearPrime) :
  ↑(@OfNat.ofNat (Fin BabyBearPrime) x Fin.instOfNat) = x := by simpa [OfNat.ofNat]

lemma bb_to_subst_eq_01 {a b c d : BabyBear} (Heq : (a + b) - c = d) : c = a + b - d := by
  rw [←Heq, sub_sub_cancel]

lemma bb_to_subst_eq_02 {a b c d e : BabyBear} (Heq : a + b - c + d = e) :
  c = a + b + d - e := by simp [Heq.symm]
