import GoldbachDeltaInduction.OffsetRadiusExamples

namespace GoldbachDeltaInduction

/-- Inside consecutive squares, testing prime divisors through the lower
square root is an exact primality test, not merely a necessary screen. -/
theorem square_interval_prime_iff_screened {m n : ℕ}
    (hm : 1 ≤ m) (hlo : m ^ 2 < n) (hhi : n < (m + 1) ^ 2) :
    n.Prime ↔ ∀ ell : ℕ, ell.Prime → ell ≤ m → ¬ ell ∣ n := by
  have hn : 1 < n := by nlinarith
  have hmn : m < n := by nlinarith
  constructor
  · intro hp ell hell hle hdiv
    have heq := hp.eq_one_or_self_of_dvd ell hdiv
    have htwo := hell.two_le
    omega
  · intro hscreen
    by_contra hnp
    have hfac : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hbound : n.minFac ≤ m := by
      by_contra h
      have hmfac : m + 1 ≤ n.minFac := by omega
      nlinarith
    exact hscreen n.minFac hfac hbound (Nat.minFac_dvd n)

theorem primes_in_square_block_nine {a : ℕ} (hlo : 81 < a) (hhi : a < 100) :
    a.Prime ↔ a = 83 ∨ a = 89 ∨ a = 97 := by
  interval_cases a <;> norm_num [Nat.Prime] at *

/-- Even a target next to the square block's midpoint can require both
prime summands outside that block, despite three primes inside it. -/
theorem no_internal_square_pair_182 :
    ¬ ∃ a b : ℕ, a.Prime ∧ b.Prime ∧
      81 < a ∧ a < 100 ∧ 81 < b ∧ b < 100 ∧ a + b = 182 := by
  rintro ⟨a, b, ha, hb, halo, hahi, hblo, hbhi, hab⟩
  have ha' := (primes_in_square_block_nine halo hahi).mp ha
  have hb' := (primes_in_square_block_nine hblo hbhi).mp hb
  omega

theorem exact_offset_minimum_91 : ExactOffsetMinimum 91 12 := by
  let factors : List ℕ := [7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2]
  have hc : OffsetFactorCertificate 91 12 factors := by decide
  exact ⟨by norm_num [SymmetricPrimePair], factor_certificate_excludes hc⟩

end GoldbachDeltaInduction
