import GoldbachDeltaInduction.OffsetRadiusExamples

namespace GoldbachDeltaInduction

/-- Every noncentral interior label of every adjacent-prime gap has a
symmetric prime pair whose offset is at most `C * k`. -/
def GapRadiusBound (C : ℕ) : Prop :=
  ∀ p q k j : ℕ, AdjacentPrimes p q → q = p + 2*k →
    0 < j → j < 2*k → j ≠ k →
    ∃ delta, SymmetricPrimePair (p+j) delta ∧ delta ≤ C*k

/-- The certified exact minimum rules out every offset below 261, including
zero, because `ExactOffsetMinimum` excludes all `e` in `Finset.range 261`. -/
theorem radius_oneTwentyEight_forces_offset_ge_261
    {delta : ℕ} (hpair : SymmetricPrimePair 12638 delta)
    (hmin : ExactOffsetMinimum 12638 261) : 261 ≤ delta := by
  by_contra h
  have hlt : delta < 261 := by omega
  exact hmin.2 delta (Finset.mem_range.mpr hlt) hpair

theorem gapRadiusBound_128_fails : ¬ GapRadiusBound 128 := by
  intro hbound
  rcases radius_oneTwentyEight_fails with ⟨hadj, hmin, hgap⟩
  obtain ⟨delta, hpair, hsize⟩ := hbound 12637 12641 2 1 hadj (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hlarge : 261 ≤ delta := radius_oneTwentyEight_forces_offset_ge_261 hpair hmin
  omega

theorem gapRadiusBound_le_128_fails {C : ℕ} (hC : C ≤ 128) :
    ¬ GapRadiusBound C := by
  intro hbound
  rcases radius_oneTwentyEight_fails with ⟨hadj, hmin, hgap⟩
  obtain ⟨delta, hpair, hsize⟩ := hbound 12637 12641 2 1 hadj (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hlarge : 261 ≤ delta := radius_oneTwentyEight_forces_offset_ge_261 hpair hmin
  omega

end GoldbachDeltaInduction
