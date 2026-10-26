import GoldbachDeltaInduction.PeriodicCapacity
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GoldbachDeltaInduction

/-- Divisibility screening preserves a prime equal to a screening modulus. -/
def Screened (P : Finset ℕ) (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ ell ∈ P, ¬ell ∣ n ∨ n=ell

theorem prime_screened (P : Finset ℕ) {n : ℕ} (hn : n.Prime)
    (hP : ∀ ell ∈ P, ell.Prime) : Screened P n := by
  refine ⟨hn.two_le,?_⟩
  intro ell hell
  by_cases hd : ell ∣ n
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq (hP ell hell) hn).1 hd).symm
  · exact Or.inl hd

def residueEligible (P : Finset ℕ) (a : ℕ) : Prop :=
  ∀ ell ∈ P, a % ell ≠ 0

def residualAllowed (P : Finset ℕ) (N a : ℕ) : Prop :=
  ∀ ell ∈ P, N % ell ≠ a % ell

/-- Away from the small-prime exceptions, the modular form is exactly the
original screen on the positive complement, not just a formal analogue. -/
theorem screened_complement_iff (P : Finset ℕ) {N a : ℕ}
    (haN : a ≤ N) (h2 : 2 ≤ N-a)
    (hlarge : ∀ ell ∈ P, ell < N-a) :
    Screened P (N-a) ↔ residualAllowed P N a := by
  constructor
  · intro hs ell hell hmod
    have hd : ell ∣ N-a := (Nat.modEq_iff_dvd' haN).1 hmod.symm
    rcases hs.2 ell hell with hnot | heq
    · exact hnot hd
    · have ht := hlarge ell hell
      omega
  · intro hr
    refine ⟨h2,?_⟩
    intro ell hell
    left
    intro hd
    have heq : a%ell=N%ell := (Nat.modEq_iff_dvd' haN).2 hd
    exact hr ell hell heq.symm

theorem prime_complement_allowed (P : Finset ℕ) {N a : ℕ}
    (haN : a ≤ N) (hn : (N-a).Prime)
    (hP : ∀ ell ∈ P, ell.Prime) (hlarge : ∀ ell ∈ P, ell<N-a) :
    residualAllowed P N a := by
  exact (screened_complement_iff P haN hn.two_le hlarge).1 (prime_screened P hn hP)

instance (P : Finset ℕ) (N a : ℕ) : Decidable (residualAllowed P N a) :=
  inferInstanceAs (Decidable (∀ ell ∈ P, N % ell ≠ a % ell))

def residueCapacity (P targets : Finset ℕ) (a : ℕ) : ℕ :=
  (targets.filter (fun N => residualAllowed P N a)).card

theorem residueEligible_congr (P : Finset ℕ) (a b : ℕ)
    (hab : a % P.prod id = b % P.prod id) :
    residueEligible P a ↔ residueEligible P b := by
  have hsmall : ∀ ell ∈ P, a % ell = b % ell := by
    intro ell hell
    exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem id hell) hab
  constructor <;> intro h ell hell
  · rw [← hsmall ell hell]
    exact h ell hell
  · rw [hsmall ell hell]
    exact h ell hell

theorem residualAllowed_congr (P : Finset ℕ) (N a b : ℕ)
    (hab : a % P.prod id = b % P.prod id) :
    residualAllowed P N a ↔ residualAllowed P N b := by
  have hsmall : ∀ ell ∈ P, a % ell = b % ell := by
    intro ell hell
    exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem id hell) hab
  constructor <;> intro h ell hell
  · rw [← hsmall ell hell]
    exact h ell hell
  · rw [hsmall ell hell]
    exact h ell hell

theorem residueCapacity_congr (P targets : Finset ℕ) (a b : ℕ)
    (hab : a % P.prod id = b % P.prod id) :
    residueCapacity P targets a = residueCapacity P targets b := by
  unfold residueCapacity
  congr 1
  ext N
  simp only [Finset.mem_filter]
  rw [residualAllowed_congr P N a b hab]

/-- This instantiates the periodic theorem with the actual finite-modulus
capacity, so periodicity is proved rather than left as a hypothesis.
Small prime anchors equal to a modulus are intentionally handled separately.
-/
theorem bounded_sieve_bound_iff (P targets : Finset ℕ) (z p h : ℕ)
    (hpositive : 0 < P.prod id) (hp : z+P.prod id ≤ p) :
    (∀ a, z<a → a≤p → residueEligible P a → residueCapacity P targets a<h) ↔
    (∀ r, residueEligible P r → residueCapacity P targets r<h) := by
  exact periodic_bound_iff (P.prod id) z p h hpositive hp
    (residueEligible P) (residueCapacity P targets)
    (residueEligible_congr P) (residueCapacity_congr P targets)

/-- A periodic obstruction always acquires a bounded integer realization
once an entire period fits. No primality of that integer is asserted. -/
theorem high_capacity_realized (P targets : Finset ℕ) (z p h r : ℕ)
    (hpositive : 0 < P.prod id) (hp : z+P.prod id ≤ p)
    (hr : residueEligible P r) (hhigh : h ≤ residueCapacity P targets r) :
    ∃ a, z<a ∧ a≤p ∧ residueEligible P a ∧ h≤residueCapacity P targets a := by
  obtain ⟨a,hza,hap,har⟩ := all_residues_realized (P.prod id) z p hpositive hp r
  refine ⟨a,hza,hap,(residueEligible_congr P a r har).2 hr,?_⟩
  rw [residueCapacity_congr P targets a r har]
  exact hhigh

end GoldbachDeltaInduction
