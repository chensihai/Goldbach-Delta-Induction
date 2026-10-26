import GoldbachDeltaInduction.UniversalSourceTransfer

namespace GoldbachDeltaInduction

/-- A diagonal representation of a prime-centered source blocks universal
transfer whenever its target complement falls in an adjacent prime gap. -/
theorem prime_center_transfer_blocked_by_gap
    {p q r N : ℕ} (hadj : AdjacentPrimes p q) (hr : r.Prime)
    (hlo : p + r < N) (hhi : N < q + r) :
    ¬ UniversalSourceTransfer (2 * r) N := by
  intro hsafe
  have hpair := hsafe r r hr hr (by omega)
  rcases hpair with ⟨hle, hprime⟩ | ⟨hle, hprime⟩
  all_goals exact hadj.2.2.2 (N - r) (by omega) (by omega) hprime

/-- The lower endpoint's self-sum is never a universally safe source for
a noncentral target in the left half of its own doubled gap window. -/
theorem lower_endpoint_source_blocked
    {p k j : ℕ} (hadj : AdjacentPrimes p (p + 2 * k))
    (hj : 0 < j) (hjk : j < k) :
    ¬ UniversalSourceTransfer (2 * p) (2 * (p + j)) := by
  apply prime_center_transfer_blocked_by_gap hadj hadj.1 <;> omega

/-- The upper endpoint's self-sum is similarly blocked in the right half. -/
theorem upper_endpoint_source_blocked
    {p k j : ℕ} (hadj : AdjacentPrimes p (p + 2 * k))
    (hkj : k < j) (hj : j < 2 * k) :
    ¬ UniversalSourceTransfer (2 * (p + 2 * k)) (2 * (p + j)) := by
  apply prime_center_transfer_blocked_by_gap hadj hadj.2.1 <;> omega

end GoldbachDeltaInduction
