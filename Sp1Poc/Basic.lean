import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace Sp1

abbrev BabyBearPrime : ℕ := 2013265921
axiom prime_BabyBearPrime : Nat.Prime BabyBearPrime -- := by norm_num

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  have : IsDomain (ZMod BabyBearPrime) := ZMod.instIsDomain (hp := ⟨prime_BabyBearPrime⟩)
  simp [ZMod] at this
  infer_instance

lemma trans_lt_le {a b c : ℕ} : a < b → b ≤ c → a < c := by omega
lemma nat_sub_add_cancel {a b : ℕ} : b ≤ a → (a - b) + b = a := by omega
lemma lt_add_cancel_right {a b c : ℕ} : a < b → a + c < b + c := by omega
lemma lt_sub_cancel_left {a b c : ℕ} : b < c → c < a → a - c < a - b := by omega

syntax "PROOF" : term
macro_rules | `(PROOF) => `(sorry)

end Sp1
