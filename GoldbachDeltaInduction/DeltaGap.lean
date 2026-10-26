import GoldbachDeltaInduction.Basic

namespace GoldbachDeltaInduction

def SymmetricPrimePair (c delta : ℕ) : Prop :=
  delta ≤ c ∧ (c-delta).Prime ∧ (c+delta).Prime

instance (c delta : ℕ) : Decidable (SymmetricPrimePair c delta) :=
  inferInstanceAs (Decidable (delta ≤ c ∧ (c-delta).Prime ∧ (c+delta).Prime))

/-- Exact conversion between a Goldbach representation and symmetric offsets.
This provides no new existence claim. -/
theorem goldbach_iff_symmetric (c : ℕ) :
    Goldbach (2*c) ↔ ∃ delta, SymmetricPrimePair c delta := by
  constructor
  · rintro ⟨a,b,ha,hb,hsum⟩
    rcases le_total a b with hab | hba
    · have hac : a≤c := by omega
      refine ⟨c-a,by omega,?_,?_⟩
      · convert ha using 1; omega
      · convert hb using 1; omega
    · have hbc : b≤c := by omega
      refine ⟨c-b,by omega,?_,?_⟩
      · convert hb using 1; omega
      · convert ha using 1; omega
  · rintro ⟨delta,hd,ha,hb⟩
    exact ⟨c-delta,c+delta,ha,hb,by omega⟩

theorem endpoint_symmetric_pair {p k : ℕ}
    (hp : p.Prime) (hq : (p+2*k).Prime) :
    SymmetricPrimePair (p+k) k := by
  refine ⟨by omega,?_,?_⟩
  · convert hp using 1; omega
  · convert hq using 1; omega

/-- A symmetric pair about an interior center must cross both gap endpoints. -/
theorem symmetric_pair_crosses_gap {p q c delta : ℕ}
    (hadj : AdjacentPrimes p q) (hpc : p<c) (hcq : c<q)
    (hpair : SymmetricPrimePair c delta) : c-delta≤p ∧ q≤c+delta := by
  rcases hadj with ⟨hp,hq,hpq,hgap⟩
  rcases hpair with ⟨hd,ha,hb⟩
  constructor
  · by_contra h
    exact hgap (c-delta) (by omega) (by omega) ha
  · by_contra h
    exact hgap (c+delta) (by omega) (by omega) hb

/-- The offset at label j has to reach BOTH boundaries of the prime-free gap. -/
theorem gap_delta_lower_bound {p q k j delta : ℕ}
    (hadj : AdjacentPrimes p q) (hqeq : q=p+2*k)
    (hj : 0<j) (hjk : j<2*k)
    (hpair : SymmetricPrimePair (p+j) delta) :
    max j (2*k-j) ≤ delta := by
  have hx := symmetric_pair_crosses_gap hadj (by omega) (by omega) hpair
  rcases hpair with ⟨hd,ha,hb⟩
  exact max_le (by omega) (by omega)

/-- A central offset shorter than k contradicts adjacency. Thus a scan of
the central minimum can detect non-adjacency, not solve other labels. -/
theorem shorter_central_offset_not_adjacent {p k delta : ℕ}
    (hshort : delta<k) (hpair : SymmetricPrimePair (p+k) delta) :
    ¬AdjacentPrimes p (p+2*k) := by
  intro hadj
  have hx := gap_delta_lower_bound hadj rfl (by omega) (by omega) hpair
  omega

theorem central_offset_minimal {p q k delta : ℕ}
    (hadj : AdjacentPrimes p q) (hqeq : q=p+2*k)
    (hpair : SymmetricPrimePair (p+k) delta) : k≤delta := by
  have hk : 0<k := by have hpq := hadj.2.2.1; omega
  have hx := gap_delta_lower_bound hadj hqeq hk (by omega) hpair
  omega

/-- Every noncentral label requires an offset strictly larger than the
already-known endpoint offset. The central scan cannot supply this witness. -/
theorem noncentral_offset_gt_half_gap {p q k j delta : ℕ}
    (hadj : AdjacentPrimes p q) (hqeq : q=p+2*k)
    (hj : 0<j) (hjk : j<2*k) (hne : j≠k)
    (hpair : SymmetricPrimePair (p+j) delta) : k<delta := by
  have hx := gap_delta_lower_bound hadj hqeq hj hjk hpair
  have hx1 : j≤delta := le_trans (le_max_left _ _) hx
  have hx2 : 2*k-j≤delta := le_trans (le_max_right _ _) hx
  omega

/-- A finite illustration of the center mismatch in the historical scan. -/
theorem cousin_centers_differ :
    AdjacentPrimes 7 11 ∧ SymmetricPrimePair 9 2 ∧
      ¬SymmetricPrimePair 8 2 ∧ SymmetricPrimePair 8 3 := by
  refine ⟨?_,by decide,by decide,by decide⟩
  refine ⟨by decide,by decide,by decide,?_⟩
  intro r hrlo hrhi
  have hcases : r=8 ∨ r=9 ∨ r=10 := by omega
  rcases hcases with h | h | h <;> subst r <;> decide

end GoldbachDeltaInduction
