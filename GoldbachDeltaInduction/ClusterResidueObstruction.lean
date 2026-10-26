import GoldbachDeltaInduction.DeltaGap

namespace GoldbachDeltaInduction

/-- Two endpoints congruent to `T` cannot sum to `2 * (T + h + 1)`
when `h` is divisible by a modulus greater than two. This is only a local
algebraic obstruction; it asserts no existence of such endpoints. -/
theorem cluster_residue_sum_obstruction
    {B a b T h : ℤ}
    (hB : 2 < B)
    (ha : B ∣ a - T)
    (hb : B ∣ b - T)
    (hh : B ∣ h)
    (hsum : a + b = 2 * (T + h + 1)) : False := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  rcases hh with ⟨z, hz⟩
  have hdiv : B ∣ 2 := by
    refine ⟨x + y - 2*z, ?_⟩
    calc
      (2:ℤ) = (a-T) + (b-T) - 2*h := by omega
      _ = (B*x + B*y) - 2*(B*z) := by rw [hx, hy, hz]
      _ = B * (x + y - 2*z) := by ring
  have h2 : (0:ℤ) < 2 := by norm_num
  have hle : B ≤ 2 := Int.le_of_dvd h2 hdiv
  omega

end GoldbachDeltaInduction
