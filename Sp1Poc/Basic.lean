import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace Sp1

abbrev BabyBearPrime : ℕ := 2013265921
lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by sorry

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  have : IsDomain (ZMod BabyBearPrime) := ZMod.instIsDomain (hp := ⟨prime_BabyBearPrime⟩)
  simp [ZMod] at this
  infer_instance

syntax "PROOF" : term
macro_rules | `(PROOF) => `(sorry)

end Sp1
