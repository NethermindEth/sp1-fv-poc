import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921
axiom BabyBearPrimeIsPrime : Nat.Prime BabyBearPrime

abbrev BabyBear : Type := Fin BabyBearPrime
instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  constructor; intros a b Heq; rw [Fin.mul_def] at Heq; by_contra Hneq; simp at *
  rw [@Fin.mk_eq_zero _ a] at Hneq; rw [@Fin.mk_eq_zero _ b] at Hneq
  have Hncp_ab : ¬ Nat.Coprime BabyBearPrime (a.1 * b.1) := by
    rw [← Nat.Prime.dvd_iff_not_coprime BabyBearPrimeIsPrime]; omega
  apply Hncp_ab
  apply Nat.Coprime.mul_right <;> [
    apply Nat.coprime_of_lt_prime <;> [ omega; exact a.2; exact BabyBearPrimeIsPrime ];
    apply Nat.coprime_of_lt_prime <;> [ omega; exact b.2; exact BabyBearPrimeIsPrime ]
  ]
