import GoldbachDeltaInduction.ExceptionalWindows

/-! A weighted finite detection bound for Goldbach exceptions. -/

namespace GoldbachDeltaInduction

theorem exists_weighted_prime_detection
    (H S E : Finset ℕ) (L : ℕ) (w : ℕ → ℝ) (M : ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n)
    (hM : 0 ≤ M)
    (hup : ∀ n ∈ S, w n ≤ M)
    (hcover : ∀ n ∈ S, ∀ j ≤ L,
      ¬ Goldbach (2 * n + 2 * j) → 2 * n + 2 * j ∈ E)
    (hlarge : ∑ n ∈ S,
        (((H.filter fun h => (n + h).Prime).card : ℝ) - 1) * w n
      > (H.card : ℝ) * M * (((L + 1) * E.card : ℕ) : ℝ)) :
    ∃ n ∈ S,
      2 ≤ (H.filter fun h => (n + h).Prime).card ∧
      ∀ j ≤ L, Goldbach (2 * n + 2 * j) := by
  classical
  by_contra hnot
  push Not at hnot
  let bad := badStarts S L
  have hcount (n : ℕ) (hn : n ∈ S) :
      ((H.filter fun h => (n + h).Prime).card : ℝ) ≤ H.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hterm_bad (n : ℕ) (hn : n ∈ S) (hb : n ∈ bad) :
      ((((H.filter fun h => (n + h).Prime).card : ℝ) - 1) * w n)
        ≤ (H.card : ℝ) * M := by
    have hc := hcount n hn
    have hw' := hw n hn
    have hu := hup n hn
    have hfactor :
        (((H.filter fun h => (n + h).Prime).card : ℝ) - 1)
          ≤ (H.card : ℝ) := by linarith
    calc
      ((((H.filter fun h => (n + h).Prime).card : ℝ) - 1) * w n)
          ≤ (H.card : ℝ) * w n := by
            exact mul_le_mul_of_nonneg_right hfactor hw'
      _ ≤ (H.card : ℝ) * M := mul_le_mul_of_nonneg_left hu (by positivity)
  have hterm_good (n : ℕ) (hn : n ∈ S) (hgood : n ∉ bad) :
      ((((H.filter fun h => (n + h).Prime).card : ℝ) - 1) * w n) ≤ 0 := by
    have hwindow : ∀ j ≤ L, Goldbach (2 * n + 2 * j) := by
      intro j hj
      by_contra hg
      have hb : n ∈ bad := Finset.mem_filter.mpr
        ⟨hn, j, Finset.mem_range.mpr (by omega), hg⟩
      exact hgood hb
    have hsmall : ¬ 2 ≤ (H.filter fun h => (n + h).Prime).card := by
      intro hh
      obtain ⟨j, hj, hbad⟩ := hnot n hn hh
      exact hbad (hwindow j hj)
    have hcard : (H.filter fun h => (n + h).Prime).card ≤ 1 := by omega
    have hfactor :
        (((H.filter fun h => (n + h).Prime).card : ℝ) - 1) ≤ 0 := by
      have hc' : ((H.filter fun h => (n + h).Prime).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hfactor (hw n hn)
  have hsum_bound :
      (∑ n ∈ S,
          (((H.filter fun h => (n + h).Prime).card : ℝ) - 1) * w n)
        ≤ (bad.card : ℝ) * (H.card : ℝ) * M := by
    calc
      _ ≤ ∑ n ∈ S, if n ∈ bad then (H.card : ℝ) * M else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs with hb
        · exact hterm_bad n hn hb
        · exact hterm_good n hn hb
      _ = (S.filter fun n => n ∈ bad).card * ((H.card : ℝ) * M) := by
        simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
        congr 1
      _ ≤ (bad.card : ℝ) * (H.card : ℝ) * M := by
        have hsub : S.filter (fun n => n ∈ bad) ⊆ bad := by
          intro n hn
          exact (Finset.mem_filter.mp hn).2
        have hcard : (S.filter fun n => n ∈ bad).card ≤ bad.card :=
          Finset.card_le_card hsub
        have hcoef : 0 ≤ (H.card : ℝ) * M := mul_nonneg (by positivity) hM
        have hcard' : ((S.filter fun n => n ∈ bad).card : ℝ) ≤ bad.card := by
          exact_mod_cast hcard
        calc
          ((S.filter fun n => n ∈ bad).card : ℝ) * ((H.card : ℝ) * M)
              ≤ (bad.card : ℝ) * ((H.card : ℝ) * M) :=
                mul_le_mul_of_nonneg_right hcard' hcoef
          _ = (bad.card : ℝ) * (H.card : ℝ) * M := by ring
  have hbad := badStarts_card_le S E L hcover
  have hbound : (bad.card : ℝ) * (H.card : ℝ) * M ≤
      (H.card : ℝ) * M * (((L + 1) * E.card : ℕ) : ℝ) := by
    have hcard : (bad.card : ℝ) ≤ (((L + 1) * E.card : ℕ) : ℝ) := by
      exact_mod_cast hbad
    have hcoef : 0 ≤ (H.card : ℝ) * M := mul_nonneg (by positivity) hM
    nlinarith [mul_le_mul_of_nonneg_left hcard hcoef]
  linarith

end GoldbachDeltaInduction
