import GoldbachDeltaInduction.Basic

namespace GoldbachDeltaInduction

/-- A prime-bounded window containing a center strictly inside an adjacent
prime gap must be at least as wide as that gap. This is about where a base
case can be applied directly; it does not rule out arithmetic transport. -/
theorem prime_window_containing_center_not_shorter
    {p q s t c : ℕ}
    (hadj : AdjacentPrimes p q)
    (hs : s.Prime) (ht : t.Prime)
    (hpc : p < c) (hcq : c < q)
    (hsc : s ≤ c) (hct : c ≤ t) :
    q - p ≤ t - s := by
  rcases hadj with ⟨_, _, hpq, hgap⟩
  have hsp : s ≤ p := by
    by_contra hn
    exact hgap s (by omega) (by omega) hs
  have hqt : q ≤ t := by
    by_contra hn
    exact hgap t (by omega) (by omega) ht
  omega

/-- A full gap-four base window cannot directly cover the center of a
larger prime gap. This does not prove non-implication for actual primes. -/
theorem gap_four_window_excludes_larger_gap_center
    {p q s c : ℕ}
    (hadj : AdjacentPrimes p q) (hwidth : 4 < q - p)
    (hs : s.Prime) (hs4 : (s + 4).Prime)
    (hpc : p < c) (hcq : c < q) :
    ¬ (s ≤ c ∧ c ≤ s + 4) := by
  rintro ⟨hsc, hcs⟩
  have hw := prime_window_containing_center_not_shorter
    hadj hs hs4 hpc hcq hsc hcs
  omega

end GoldbachDeltaInduction
