import GoldbachDeltaInduction.ModularTransferObstruction
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace GoldbachDeltaInduction

/-- Infinitely far out, the diagonal Goldbach source `p + p` has no endpoint
that can transfer to the target `2*p + 2` by the nearest-source shift. -/
theorem arbitrarily_large_blocked_goldbach_sources (X : ℕ) :
    ∃ p : ℕ, X < p ∧ p.Prime ∧ p % 210 = 199 ∧ Goldbach (2 * p) ∧
      ∀ a b : ℕ, a.Prime → b.Prime → a + b = 2 * p →
        ¬ (a + 2).Prime ∧ ¬ (b + 2).Prime := by
  obtain ⟨p, hpX, hp, hres⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max X 199) (q := 210) (a := 199)
      (by omega) (by decide)
  have hpmod : p % 210 = 199 := by
    simpa [Nat.ModEq] using hres
  have hsource : Goldbach (2 * p) := by
    exact ⟨p, p, hp, hp, by omega⟩
  refine ⟨p, by omega, hp, hpmod, hsource, ?_⟩
  intro a b ha hb hab
  apply all_source_pairs_blocked_mod30 (M := 2 * p) (a := a) (b := b) ?_ ?_ ha hb hab
  · have : 199 ≤ p := by omega
    omega
  · omega

end GoldbachDeltaInduction
