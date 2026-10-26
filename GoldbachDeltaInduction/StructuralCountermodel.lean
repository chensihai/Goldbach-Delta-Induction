import GoldbachDeltaInduction.Basic

/-! Abstract set model. P is not the set of actual primes. -/
namespace GoldbachDeltaInduction.StructuralCountermodel

def P (n : ℕ) : Prop :=
  n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 ∨ n = 17 ∨ n = 19 ∨
    n = 23 ∨ n = 29 ∨ n = 31 ∨
    (101 ≤ n ∧ n % 2 = 1 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0)

def G (N : ℕ) : Prop := ∃ a b, P a ∧ P b ∧ a + b = N

def Adj (p q : ℕ) : Prop :=
  P p ∧ P q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ P r

theorem even_ge_108_goldbach : ∀ N, 108 ≤ N → N % 2 = 0 → G N := by
  intro N hN hEven
  have hmod : N % 30 < 30 := Nat.mod_lt _ (by omega)
  interval_cases h : N % 30 <;> norm_num at h
  all_goals first
    | exact ⟨3, N - 3, by norm_num [P], by
        unfold P
        right; right; right; right; right; right; right; right
        omega, by omega⟩
    | exact ⟨5, N - 5, by norm_num [P], by
        unfold P
        right; right; right; right; right; right; right; right
        omega, by omega⟩
    | exact ⟨7, N - 7, by norm_num [P], by
        unfold P
        right; right; right; right; right; right; right; right
        omega, by omega⟩
    | omega

theorem full_gap_four_windows :
    ∀ p, P p → P (p + 4) → ∀ j ≤ 4, G (2 * (p + j)) := by
  intro p hp hp4 j hj
  by_cases hpLarge : 101 ≤ p
  · apply even_ge_108_goldbach
    · omega
    · omega
  · have hpSmall : p < 101 := by omega
    have hpCases : p = 3 ∨ p = 7 ∨ p = 13 ∨ p = 19 := by
      unfold P at hp hp4
      omega
    rcases hpCases with rfl | rfl | rfl | rfl <;> interval_cases j <;>
      norm_num at hj ⊢ <;>
      first
      | exact ⟨3, 3, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨3, 5, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨3, 7, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨5, 5, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨5, 7, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨5, 11, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨3, 17, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨7, 7, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨7, 11, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨11, 11, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨11, 17, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨17, 17, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨3, 23, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨11, 17, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨13, 17, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨17, 23, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨13, 19, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨3, 31, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨7, 31, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨11, 31, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨13, 31, by norm_num [P], by norm_num [P], by omega⟩
      | exact ⟨23, 23, by norm_num [P], by norm_num [P], by omega⟩
      | omega

theorem gap_six_failure : Adj 23 29 ∧ ¬ G 56 := by
  constructor
  · refine ⟨by norm_num [P], by norm_num [P], by norm_num, ?_⟩
    intro r hLow hHigh hP
    unfold P at hP
    omega
  · intro hG
    rcases hG with ⟨a, b, ha, hb, hab⟩
    unfold P at ha hb
    omega

theorem infinitely_many_gap_four (t : ℕ) :
    Adj (103 + 30 * t) (107 + 30 * t) := by
  refine ⟨?_, ?_, by omega, ?_⟩
  · unfold P
    right; right; right; right; right; right; right; right
    omega
  · unfold P
    right; right; right; right; right; right; right; right
    omega
  · intro r hLow hHigh hP
    unfold P at hP
    omega

end GoldbachDeltaInduction.StructuralCountermodel