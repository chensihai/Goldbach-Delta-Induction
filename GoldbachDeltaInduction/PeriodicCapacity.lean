import Mathlib.Tactic

namespace GoldbachDeltaInduction

/-- Every residue has a representative in any interval of length M. -/
theorem residue_in_interval (M z r : ℕ) (hM : 0 < M) :
    ∃ a : ℕ, z < a ∧ a ≤ z+M ∧ a % M = r % M := by
  let a : ℕ := z+M-((z+M-r%M)%M)
  have hr : r%M < M := Nat.mod_lt r hM
  have hd : (z+M-r%M)%M < M := Nat.mod_lt _ hM
  have hb : r%M ≤ z+M := by omega
  refine ⟨a, by dsimp [a]; omega, by dsimp [a]; omega, ?_⟩
  have heq : z+M-r%M = M*((z+M-r%M)/M)+(z+M-r%M)%M := by
    have hdiv := Nat.mod_add_div (z+M-r%M) M
    omega
  have hae : a = M*((z+M-r%M)/M)+r%M := by dsimp [a]; omega
  rw [hae]
  simp

/-- Once the whole residue period fits, a bounded interval loses no periodic pattern. -/
theorem all_residues_realized (M z p : ℕ) (hM : 0 < M) (hp : z+M ≤ p) :
    ∀ r : ℕ, ∃ a : ℕ, z < a ∧ a ≤ p ∧ a%M=r%M := by
  intro r
  obtain ⟨a,hza,haz,har⟩ := residue_in_interval M z r hM
  exact ⟨a,hza,le_trans haz hp,har⟩

/-- Any pointwise capacity bound on the interval is then a bound on every
admissible residue; this is an equivalence, not an assumed analytic estimate. -/
theorem periodic_bound_iff (M z p h : ℕ) (hM : 0 < M) (hp : z+M ≤ p)
    (admissible : ℕ → Prop) (capacity : ℕ → ℕ)
    (hadmissible : ∀ a b, a%M=b%M → (admissible a ↔ admissible b))
    (hcapacity : ∀ a b, a%M=b%M → capacity a=capacity b) :
    (∀ a, z<a → a≤p → admissible a → capacity a<h) ↔
    (∀ r, admissible r → capacity r<h) := by
  constructor
  · intro hlocal r hr
    obtain ⟨a,hza,hap,har⟩ := all_residues_realized M z p hM hp r
    have haa : admissible a := (hadmissible a r har).2 hr
    have hbound := hlocal a hza hap haa
    simpa [hcapacity a r har] using hbound
  · intro hglobal a _ _ ha
    exact hglobal a ha

end GoldbachDeltaInduction
