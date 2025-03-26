import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

abbrev BabyBear : Type := Fin 2013265921

lemma bb_val_ofNat ( x : ℕ ) :
  x < 2013265921 → ↑(@OfNat.ofNat (Fin 2013265921) x Fin.instOfNat) = x := by
  intro Hlt
  unfold OfNat.ofNat; unfold Fin.instOfNat; simp
  rw [Nat.mod_eq_of_lt]; assumption

lemma bb_to_subst_eq_01 (a b c d : BabyBear) :
  a < 256 → b < 256 → c < 256 →
    (a + b) - c = d →
      c = a + b - d :=
  by
  intro Ha Hb Hc Heq
  rw [← Fin.val_eq_val] at *
  rw [Fin.sub_def] at *; rw [Fin.add_def] at *; simp at *
  omega

lemma bb_to_subst_eq_02 (a b c d e : BabyBear) :
  a < 256 → b < 256 → c < 256 → d < 256 →
    a + b - c + d = e →
      c = a + b + d - e :=
  by
  intro Ha Hb Hc Hd Heq
  rw [← Fin.val_eq_val] at *
  rw [Fin.sub_def] at *; rw [Fin.add_def] at *; simp at *
  omega
