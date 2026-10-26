import Mathlib

example (p δ : ℕ) (h : δ ≤ p + 1) :
    (p + 1 - δ) + (p + 1 + δ) = 2 * p + 2 := by
  omega

example (p δ : ℕ) (h : 3 ∣ δ) :
    (p + 1 + δ) ≡ p + 1 [MOD 3] := by
  obtain ⟨k, hk⟩ := h
  subst δ
  omega

example (p δ : ℕ) (hδ : 3 ∣ δ) (h : δ ≤ p + 1) :
    (p + 1 - δ) ≡ p + 1 [MOD 3] := by
  obtain ⟨k, hk⟩ := hδ
  subst δ
  omega

example :
    Nat.Prime 5 ∧ Nat.Prime 11 := by
  norm_num
