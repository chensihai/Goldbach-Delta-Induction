import GoldbachDeltaInduction.GlobalWindowReduction

namespace GoldbachDeltaInduction

/-- Under the full gap-four premise, a failure of global Goldbach has a
least failed gap parameter and a noncentral failed label. No ordering of
the target sums is asserted by the smaller-parameter hypotheses. -/
theorem global_failure_has_first_noncentral_window
    (hB2 : B2) (hfail : ¬ GlobalGoldbach) :
    ∃ k p j : ℕ, 3 ≤ k ∧
      (∀ i, i < k → WindowStatement i) ∧
      AdjacentPrimes p (p + 2 * k) ∧
      0 < j ∧ j < 2 * k ∧ j ≠ k ∧
      ¬ Goldbach (2 * (p + j)) := by
  classical
  have hex : ∃ k, ¬ WindowStatement k := by
    by_contra hn
    push Not at hn
    exact hfail (globalGoldbach_iff_all_windows.mpr hn)
  let k := Nat.find hex
  have hbad : ¬ WindowStatement k := Nat.find_spec hex
  have hlow : ∀ i, i < k → WindowStatement i := by
    intro i hi
    by_contra hnot
    exact (Nat.find_min hex hi) hnot
  have hk0 : k ≠ 0 := by
    intro heq
    apply hbad
    rw [heq]
    exact windowStatement_zero
  have hk1 : k ≠ 1 := by
    intro heq
    apply hbad
    rw [heq]
    exact windowStatement_one
  have hk2 : k ≠ 2 := by
    intro heq
    apply hbad
    rw [heq]
    exact windowStatement_two_iff_B2.mpr hB2
  have hk : 3 ≤ k := by omega
  have hbad' := hbad
  unfold WindowStatement FullGoldbachWindow at hbad'
  push Not at hbad'
  obtain ⟨p, hadj, j, hj, hnot⟩ := hbad'
  have hj0 : j ≠ 0 := by
    intro heq
    subst j
    apply hnot
    exact ⟨p, p, hadj.1, hadj.1, by omega⟩
  have hjtop : j ≠ 2 * k := by
    intro heq
    subst j
    apply hnot
    exact ⟨p + 2 * k, p + 2 * k, hadj.2.1, hadj.2.1, by omega⟩
  have hjcenter : j ≠ k := by
    intro heq
    subst j
    apply hnot
    exact ⟨p, p + 2 * k, hadj.1, hadj.2.1, by omega⟩
  exact ⟨k, p, j, hk, hlow, hadj, by omega, by omega, hjcenter, hnot⟩

end GoldbachDeltaInduction
