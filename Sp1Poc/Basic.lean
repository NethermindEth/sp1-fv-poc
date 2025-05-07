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

lemma fin_val_simp {n : ℕ} (Hlt : n < BabyBearPrime) :
  (@Fin.val Sp1.BabyBearPrime (@OfNat.ofNat.{0} Sp1.BabyBear n (@Fin.instOfNat Sp1.BabyBearPrime Sp1.instNeZeroNatBabyBearPrime n))) = n := by
  simp [BabyBearPrime, OfNat.ofNat] at *; assumption

syntax "PROOF" : term
macro_rules | `(PROOF) => `(sorry)

end Sp1
