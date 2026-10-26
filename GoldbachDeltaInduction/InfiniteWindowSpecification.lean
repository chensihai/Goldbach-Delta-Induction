import GoldbachDeltaInduction.OffsetRadiusExamples

namespace GoldbachDeltaInduction

/-- Every even target in the closed doubled adjacent-prime window. -/
def FullGoldbachWindow (p k : ℕ) : Prop :=
  ∀ j ≤ 2 * k, Goldbach (2 * (p + j))

/-- The exact local witness used in the infinite-family paper deduction.
This predicate supplies no analytic existence theorem. -/
def WindowOffsetWitness (k R p : ℕ) : Prop :=
  2 ≤ k ∧ AdjacentPrimes p (p + 2 * k) ∧ FullGoldbachWindow p k ∧
    ∀ delta ≤ R, ¬ SymmetricPrimePair (p + 1) delta

theorem windowOffsetWitness_mono {k R S p : ℕ} (hRS : R ≤ S)
    (h : WindowOffsetWitness k S p) : WindowOffsetWitness k R p := by
  rcases h with ⟨hk, hadj, hfull, hexclude⟩
  exact ⟨hk, hadj, hfull, fun delta hd => hexclude delta (hd.trans hRS)⟩

/-- Full-window success supplies a genuine finite minimum at the noncentral
left target, while isolation forces that minimum beyond the given radius. -/
theorem windowOffsetWitness_has_exact_minimum {k R p : ℕ}
    (h : WindowOffsetWitness k R p) :
    ∃ delta, R < delta ∧ ExactOffsetMinimum (p + 1) delta := by
  rcases h with ⟨hk, _hadj, hfull, hexclude⟩
  have hgold : Goldbach (2 * (p + 1)) := hfull 1 (by omega)
  have hex : ∃ delta, SymmetricPrimePair (p + 1) delta :=
    (goldbach_iff_symmetric (p + 1)).mp hgold
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hn
    exact hexclude _ (by omega) (Nat.find_spec hex)
  · intro e he
    exact Nat.find_min hex (Finset.mem_range.mp he)

end GoldbachDeltaInduction
