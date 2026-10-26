import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! Exact specifications for the adjacent-prime Goldbach research.
No analytic prime-existence assumption is imported as an axiom.
-/

namespace GoldbachDeltaInduction

def Goldbach (N : ℕ) : Prop :=
  ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a + b = N

def AdjacentPrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

def Covers (p N a : ℕ) : Prop :=
  a.Prime ∧ a ≤ p ∧ (N - a).Prime

/-- Every interior Goldbach representation crosses the prime-free gap. -/
theorem representation_crosses_gap {p q N a b : ℕ}
    (hadj : AdjacentPrimes p q) (hNlo : 2*p < N) (hNhi : N < 2*q)
    (ha : a.Prime) (hb : b.Prime) (hab : a ≤ b) (hsum : a+b=N) :
    a ≤ p ∧ q ≤ b := by
  rcases hadj with ⟨hp, hq, hpq, hgap⟩
  have halq : a < q := by omega
  have hap : a ≤ p := by
    by_contra h
    exact hgap a (by omega) halq ha
  have hbgt : p < b := by omega
  have hqb : q ≤ b := by
    by_contra h
    exact hgap b hbgt (by omega) hb
  exact ⟨hap, hqb⟩

/-- Restricted anchors recover the full Goldbach proposition in the interior. -/
theorem goldbach_iff_anchor {p q N : ℕ}
    (hadj : AdjacentPrimes p q) (hNlo : 2*p < N) (hNhi : N < 2*q) :
    Goldbach N ↔ ∃ a, Covers p N a := by
  constructor
  · rintro ⟨a,b,ha,hb,hsum⟩
    rcases le_total a b with hab | hba
    · have hx := representation_crosses_gap hadj hNlo hNhi ha hb hab hsum
      exact ⟨a,ha,hx.1,by simpa [← hsum] using hb⟩
    · have hsum' : b+a=N := by omega
      have hx := representation_crosses_gap hadj hNlo hNhi hb ha hba hsum'
      exact ⟨b,hb,hx.1,by simpa [← hsum'] using ha⟩
  · rintro ⟨a,ha,hap,hb⟩
    exact ⟨a,N-a,ha,hb,by omega⟩

/-- For the even targets in this research, the anchor 2 is impossible,
so the exact anchor model really uses the odd primes in [3,p]. -/
theorem goldbach_iff_odd_anchor {p q N : ℕ}
    (hadj : AdjacentPrimes p q) (hp3 : 3 ≤ p)
    (hNlo : 2*p<N) (hNhi : N<2*q) (heven : N%2=0) :
    Goldbach N ↔ ∃ a, 3≤a ∧ Covers p N a := by
  rw [goldbach_iff_anchor hadj hNlo hNhi]
  constructor
  · rintro ⟨a,ha,hap,hcomp⟩
    have ha2 := ha.two_le
    have hane : a ≠ 2 := by
      intro heq
      rcases hcomp.eq_two_or_odd with hc | hc <;> omega
    exact ⟨a,by omega,ha,hap,hcomp⟩
  · rintro ⟨a,_,ha⟩
    exact ⟨a,ha⟩

/-- The central label is supplied by the endpoints without another existence claim. -/
theorem central_goldbach {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqeq : q=p+2*k) : Goldbach (2*p+2*k) := by
  exact ⟨p,q,hp,hq,by omega⟩

end GoldbachDeltaInduction
