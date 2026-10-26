import GoldbachDeltaInduction.GlobalWindowReduction

namespace GoldbachDeltaInduction

/-- Explicit conditional input; no assertion of Legendre's conjecture. -/
def PrimeBetweenSquares : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ r : ℕ, r.Prime ∧ m ^ 2 < r ∧ r < (m + 1) ^ 2

def TwoPrimesBetweenSquares : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ r s : ℕ,
    r.Prime ∧ s.Prime ∧ m ^ 2 < r ∧ r < s ∧ s < (m + 1) ^ 2

theorem twoPrimesBetweenSquares_imp_one (h : TwoPrimesBetweenSquares) :
    PrimeBetweenSquares := by
  intro m hm
  obtain ⟨r, s, hr, _, hlo, hrs, hhi⟩ := h m hm
  exact ⟨r, hr, hlo, lt_trans hrs hhi⟩

/-- An internal even gap fits a strictly smaller numerical square index. -/
theorem half_gap_lt_internal_square_index
    {m p k : ℕ} (hlo : m ^ 2 < p) (hhi : p + 2 * k < (m + 1) ^ 2) :
    k < m := by
  by_contra h
  have hkm : m ≤ k := by omega
  nlinarith

/-- Legendre's one-prime input bounds even the windows crossing square
boundaries. This is a bound on the gap parameter, not a Goldbach proof. -/
theorem square_center_half_gap_bound
    (hL : PrimeBetweenSquares) {m c p k : ℕ} (hm : 2 ≤ m)
    (hc : m ^ 2 ≤ c ∧ c < (m + 1) ^ 2)
    (hadj : AdjacentPrimes p (p + 2 * k))
    (hpc : p < c) (hcq : c < p + 2 * k) :
    k ≤ 2 * m + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = t + 2 := ⟨m - 2, by omega⟩
  obtain ⟨a, ha, halo, hahi⟩ := hL (t + 1) (by omega)
  obtain ⟨b, hb, hblo, hbhi⟩ := hL (t + 2) (by omega)
  obtain ⟨d, hd, hdlo, hdhi⟩ := hL (t + 3) (by omega)
  have hap : a ≤ p := by
    by_contra h
    apply hadj.2.2.2 a (by omega) (by nlinarith) ha
  have hqd : p + 2 * k ≤ d := by
    by_contra h
    apply hadj.2.2.2 d (by nlinarith) (by omega) hd
  by_cases hbc : b ≤ c
  · have hbp : b ≤ p := by
      by_contra h
      exact hadj.2.2.2 b (by omega) (by omega) hb
    by_contra h
    have hk : 2 * (t + 2) + 2 ≤ k := by omega
    nlinarith
  · have hqb : p + 2 * k ≤ b := by
      by_contra h
      exact hadj.2.2.2 b (by omega) (by omega) hb
    by_contra h
    have hk : 2 * (t + 2) + 2 ≤ k := by omega
    nlinarith

/-- For a fixed square block only finitely many *global* gap statements
are needed under the explicit square-prime hypothesis. Those global
statements are not consequences of the previous square block. -/
theorem goldbach_in_square_block_of_bounded_windows
    (hL : PrimeBetweenSquares) {m : ℕ} (hm : 2 ≤ m)
    (hW : ∀ k, k ≤ 2 * m + 1 → WindowStatement k)
    {c : ℕ} (hc : m ^ 2 ≤ c ∧ c < (m + 1) ^ 2) :
    Goldbach (2 * c) := by
  by_cases hp : c.Prime
  · exact ⟨c, c, hp, hp, by omega⟩
  · have hc4 : 4 ≤ c := by nlinarith
    obtain ⟨p, q, hp3, hpp, hqp, hpc, hcq, hgap⟩ := prime_bracket c hc4 hp
    have hpo : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h <;> omega
    have hqo : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h | h <;> omega
    let k := (q - p) / 2
    have hqeq : q = p + 2 * k := by dsimp [k]; omega
    have hadj : AdjacentPrimes p (p + 2 * k) := by
      rw [← hqeq]
      exact ⟨hpp, hqp, by omega, hgap⟩
    have hcq' : c < p + 2 * k := by omega
    have hkb := square_center_half_gap_bound hL hm hc hadj hpc hcq'
    have hgold := hW k hkb p hadj (c - p) (by omega)
    have heq : 2 * (p + (c - p)) = 2 * c := by omega
    exact heq ▸ hgold

end GoldbachDeltaInduction
