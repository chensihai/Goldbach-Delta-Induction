import GoldbachDeltaInduction.Basic

/-! A finite pigeonhole argument that extracts one parameter uniformly
over all radii and all lower bounds on the witness. -/

namespace GoldbachDeltaInduction

private theorem finite_bad_thresholds {P : ℕ → ℕ → ℕ → Prop}
    (K : Finset ℕ)
    (hmono : ∀ k R S p, R ≤ S → P k S p → P k R p)
    (hbad : ∀ k ∈ K, ∃ R X, ∀ p, X < p → ¬ P k R p) :
    ∃ R X, ∀ k ∈ K, ∀ p, X < p → ¬ P k R p := by
  classical
  induction K using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨R₀, X₀, h₀⟩ := ih (by
        intro k hk
        exact hbad k (Finset.mem_insert_of_mem hk))
      obtain ⟨R₁, X₁, h₁⟩ := hbad a (Finset.mem_insert_self a s)
      refine ⟨max R₀ R₁, max X₀ X₁, ?_⟩
      intro k hk p hp
      rcases Finset.mem_insert.mp hk with rfl | hks
      · intro hP
        have hleR : R₁ ≤ max R₀ R₁ := le_max_right _ _
        have hleX : X₁ ≤ max X₀ X₁ := le_max_right _ _
        exact h₁ p (by omega) (hmono k R₁ (max R₀ R₁) p hleR hP)
      · intro hP
        have hleR : R₀ ≤ max R₀ R₁ := le_max_left _ _
        have hleX : X₀ ≤ max X₀ X₁ := le_max_left _ _
        exact h₀ k hks p (by omega) (hmono k R₀ (max R₀ R₁) p hleR hP)

/-- If every radius and every witness threshold is met by some member of a
finite parameter set, and the property passes from larger radii to smaller
ones, one parameter works for every radius and every witness threshold. -/
theorem exists_fixed_parameter {P : ℕ → ℕ → ℕ → Prop} (K : Finset ℕ)
    (hmono : ∀ k R S p, R ≤ S → P k S p → P k R p)
    (h : ∀ R X, ∃ k ∈ K, ∃ p, X < p ∧ P k R p) :
    ∃ k ∈ K, ∀ R X, ∃ p, X < p ∧ P k R p := by
  classical
  by_contra hgoal
  have hbad : ∀ k ∈ K, ∃ R X, ∀ p, X < p → ¬ P k R p := by
    intro k hk
    have hkfail : ¬ ∀ R X, ∃ p, X < p ∧ P k R p := by
      intro hall
      exact hgoal ⟨k, hk, hall⟩
    push Not at hkfail
    obtain ⟨R, X, hp⟩ := hkfail
    exact ⟨R, X, fun p hXp hP => hp p hXp hP⟩
  obtain ⟨R, X, hR⟩ := finite_bad_thresholds K hmono hbad
  obtain ⟨k, hk, p, hXp, hP⟩ := h R X
  exact hR k hk p hXp hP

end GoldbachDeltaInduction
