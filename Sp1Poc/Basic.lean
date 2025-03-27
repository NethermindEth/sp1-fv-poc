import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921
abbrev BabyBear : Type := Fin BabyBearPrime
instance : NeZero BabyBearPrime := by constructor; decide
