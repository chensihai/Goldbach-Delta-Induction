import GoldbachDeltaInduction.Basic

/-! Finite counting for translated Goldbach windows. -/

namespace GoldbachDeltaInduction

/-- Starts in `S` whose translated window has at least one non-Goldbach target. -/
noncomputable def badStarts (S : Finset ℕ) (L : ℕ) : Finset ℕ := by
  classical
  exact S.filter fun n => ∃ j ∈ Finset.range (L + 1), ¬ Goldbach (2 * n + 2 * j)

/-- A covered set of exceptional targets bounds the number of bad starts by
`(L + 1)` times the number of exceptional targets. -/
theorem badStarts_card_le (S E : Finset ℕ) (L : ℕ)
    (hcover : ∀ n ∈ S, ∀ j ≤ L,
      ¬ Goldbach (2 * n + 2 * j) → 2 * n + 2 * j ∈ E) :
    (badStarts S L).card ≤ (L + 1) * E.card := by
  classical
  let Bad := {n // n ∈ badStarts S L}
  let Code := Fin (L + 1) × {e // e ∈ E}
  have bad_spec (n : Bad) : n.1 ∈ S ∧ ∃ j ∈ Finset.range (L + 1),
      ¬ Goldbach (2 * n.1 + 2 * j) := by
    have hn := n.2
    simpa only [badStarts, Finset.mem_filter] using hn
  let witness : Bad → ℕ := fun n => Classical.choose (bad_spec n).2
  have witness_spec (n : Bad) : witness n ∈ Finset.range (L + 1) ∧
      ¬ Goldbach (2 * n.1 + 2 * witness n) := Classical.choose_spec (bad_spec n).2
  let encode : Bad → Code := fun n =>
    (⟨witness n, by
        have := Finset.mem_range.mp (witness_spec n).1
        omega⟩,
      ⟨2 * n.1 + 2 * witness n,
        hcover n.1 (bad_spec n).1 (witness n)
          (by have := Finset.mem_range.mp (witness_spec n).1; omega) (witness_spec n).2⟩)
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    have hj : witness a = witness b := congrArg Fin.val (congrArg Prod.fst hab)
    have hn : 2 * a.1 + 2 * witness a = 2 * b.1 + 2 * witness b :=
      congrArg Subtype.val (congrArg Prod.snd hab)
    omega
  have hle : Fintype.card Bad ≤ Fintype.card Code := Fintype.card_le_of_injective encode hinj
  simpa [Bad, Code, Fintype.card_coe] using hle

/-- If exceptional targets are too sparse to cover every translated window,
some start in `S` has Goldbach representations throughout the window. -/
theorem exists_good_window (S E : Finset ℕ) (L : ℕ)
    (hcover : ∀ n ∈ S, ∀ j ≤ L,
      ¬ Goldbach (2 * n + 2 * j) → 2 * n + 2 * j ∈ E)
    (hsmall : (L + 1) * E.card < S.card) :
    ∃ n ∈ S, ∀ j ≤ L, Goldbach (2 * n + 2 * j) := by
  classical
  have hbound := badStarts_card_le S E L hcover
  by_contra h
  push Not at h
  have hsub : S ⊆ badStarts S L := by
    intro n hnS
    have ⟨j, hj, hbad⟩ := h n hnS
    apply Finset.mem_filter.mpr
    refine ⟨hnS, j, Finset.mem_range.mpr (by omega), hbad⟩
  have hcard := Finset.card_le_card hsub
  omega

end GoldbachDeltaInduction
