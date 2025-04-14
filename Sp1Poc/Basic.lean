import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921
lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by sorry

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  have : IsDomain (ZMod BabyBearPrime) := ZMod.instIsDomain (hp := ⟨prime_BabyBearPrime⟩)
  simp [ZMod] at this
  infer_instance
