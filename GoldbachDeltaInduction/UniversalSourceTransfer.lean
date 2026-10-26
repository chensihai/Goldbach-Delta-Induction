import GoldbachDeltaInduction.InfiniteWindowSpecification

namespace GoldbachDeltaInduction

/-- A source representation transfers to a target when one of its prime
endpoints stays at most the target and has a prime complementary endpoint. -/
def UniversalSourceTransfer (M N : ℕ) : Prop :=
  ∀ a b : ℕ, a.Prime → b.Prime → a + b = M →
    (a ≤ N ∧ (N - a).Prime) ∨ (b ≤ N ∧ (N - b).Prime)

theorem universalSourceTransfer_goldbach {M N : ℕ}
    (hSafe : UniversalSourceTransfer M N) (hG : Goldbach M) : Goldbach N := by
  rcases hG with ⟨a, b, ha, hb, hab⟩
  rcases hSafe a b ha hb hab with h | h
  · exact ⟨a, N - a, ha, h.2, by omega⟩
  · exact ⟨b, N - b, hb, h.2, by omega⟩

private theorem source44_unordered_pairs {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a + b = 44) (hle : a ≤ b) :
    (a = 3 ∧ b = 41) ∨ (a = 7 ∧ b = 37) ∨ (a = 13 ∧ b = 31) := by
  have ha22 : a ≤ 22 := by omega
  have hbval : b = 44 - a := by omega
  subst b
  interval_cases a <;> norm_num [Nat.Prime] at *

theorem source44_safe_at (N : ℕ) (hN : N = 48 ∨ N = 50 ∨ N = 54 ∨ N = 56) :
    UniversalSourceTransfer 44 N := by
  intro a b ha hb hab
  rcases le_total a b with hab' | hba'
  · rcases source44_unordered_pairs ha hb hab hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases hN with rfl | rfl | rfl | rfl <;> norm_num [Nat.Prime]
  · have hpairs := source44_unordered_pairs hb ha (by omega) hba'
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases hN with rfl | rfl | rfl | rfl <;> norm_num [Nat.Prime]

theorem source44_safe :
    ∀ N ∈ ({48, 50, 54, 56} : Finset ℕ), UniversalSourceTransfer 44 N := by
  intro N hN
  have hcases : N = 48 ∨ N = 50 ∨ N = 54 ∨ N = 56 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hN
  exact source44_safe_at N hcases

/-- The source 44 certificate fills the four interior labels other than the
center of the window from 23 through 29. -/
theorem goldbach44_implies_window23_29 (hG : Goldbach 44) :
    FullGoldbachWindow 23 3 := by
  intro j hj
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hjcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨23, 23, by norm_num, by norm_num, by norm_num⟩
  · simpa using universalSourceTransfer_goldbach (source44_safe_at 48 (by omega)) hG
  · simpa using universalSourceTransfer_goldbach (source44_safe_at 50 (by omega)) hG
  · exact ⟨23, 29, by norm_num, by norm_num, by norm_num⟩
  · simpa using universalSourceTransfer_goldbach (source44_safe_at 54 (by omega)) hG
  · simpa using universalSourceTransfer_goldbach (source44_safe_at 56 (by omega)) hG
  · exact ⟨29, 29, by norm_num, by norm_num, by norm_num⟩

def B2 : Prop :=
  ∀ p : ℕ, AdjacentPrimes p (p + 4) → FullGoldbachWindow p 2

theorem not_universalSourceTransfer_92_96 :
    ¬ UniversalSourceTransfer 92 96 := by
  intro h
  have hends := h 31 61 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hends

theorem B2_implies_window23_29 (hB2 : B2) : FullGoldbachWindow 23 3 := by
  have hadj : AdjacentPrimes 19 23 := (radius_four_fails).1
  have hwindow := hB2 19 hadj
  have hG44 : Goldbach 44 := by
    have h := hwindow 3 (by norm_num [FullGoldbachWindow])
    simpa [FullGoldbachWindow] using h
  exact goldbach44_implies_window23_29 hG44

end GoldbachDeltaInduction
