import GoldbachDeltaInduction.UniversalSourceTransfer
import Mathlib.Data.Nat.Prime.Infinite

namespace GoldbachDeltaInduction

def WindowStatement (k : ℕ) : Prop :=
  ∀ p : ℕ, AdjacentPrimes p (p + 2*k) → FullGoldbachWindow p k

def GlobalGoldbach : Prop :=
  ∀ N : ℕ, 4 ≤ N → N % 2 = 0 → Goldbach N

theorem windowStatement_zero : WindowStatement 0 := by
  intro p hp j hj
  have hp' := hp.1
  have hj0 : j = 0 := by omega
  subst j
  exact ⟨p, p, hp', hp', by omega⟩

theorem windowStatement_one : WindowStatement 1 := by
  intro p hadj j hj
  have hp := hadj.1
  have hq := hadj.2.1
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl | rfl
  · exact ⟨p, p, hp, hp, by omega⟩
  · exact ⟨p, p + 2, hp, hq, by omega⟩
  · exact ⟨p + 2, p + 2, hq, hq, by omega⟩

theorem globalGoldbach_imp_windows (hG : GlobalGoldbach) :
    ∀ k, WindowStatement k := by
  intro k p hadj j hj
  have hp := hadj.1
  have hN : 4 ≤ 2 * (p + j) := by have := hp.two_le; omega
  have heven : (2 * (p + j)) % 2 = 0 := by omega
  exact hG (2 * (p + j)) hN heven

theorem prime_bracket (c : ℕ) (hc : 4 ≤ c) (hnp : ¬ c.Prime) :
    ∃ p q, 3 ≤ p ∧ p.Prime ∧ q.Prime ∧ p < c ∧ c < q ∧
      ∀ r, p < r → r < q → ¬ r.Prime := by
  have hex : ∃ n, c < n ∧ n.Prime := by
    obtain ⟨n, hn, hnprime⟩ := Nat.exists_infinite_primes (c + 1)
    exact ⟨n, by omega, hnprime⟩
  let q := Nat.find hex
  have hqspec := Nat.find_spec hex
  have hqmin : ∀ n, c < n → n.Prime → q ≤ n := by
    intro n hcn hn
    exact Nat.find_min' hex ⟨hcn, hn⟩
  let S : Finset ℕ := (Finset.range (c+1)).filter Nat.Prime
  have hS : S.Nonempty := by
    refine ⟨3, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simp [Finset.mem_range]; omega, by norm_num⟩
  let p := S.max' hS
  have hpmem : p ∈ S := Finset.max'_mem S hS
  have h3mem : 3 ∈ S := Finset.mem_filter.mpr
    ⟨by simp [Finset.mem_range]; omega, by norm_num⟩
  have h3p : 3 ≤ p := by simpa [p] using (Finset.le_max' S 3 h3mem)
  have hple : p ≤ c := by
    have := (Finset.mem_filter.mp hpmem).1
    simp only [Finset.mem_range] at this
    omega
  have hpprime : p.Prime := (Finset.mem_filter.mp hpmem).2
  have hplt : p < c := by
    by_contra h
    have : p = c := by omega
    have hEq : p = c := by omega
    exact hnp (hEq ▸ hpprime)
  refine ⟨p, q, h3p, hpprime, hqspec.2, hplt, hqspec.1, ?_⟩
  intro r hpr hrq hrprime
  by_cases hrc : r ≤ c
  · have hrmem : r ∈ S := by simp [S, Finset.mem_range, hrprime, hrc]
    have hle := Finset.le_max' S r hrmem
    omega
  · have hrgt : c < r := by omega
    have hle := hqmin r hrgt hrprime
    omega

theorem globalGoldbach_iff_all_windows :
    GlobalGoldbach ↔ ∀ k, WindowStatement k := by
  constructor
  · exact globalGoldbach_imp_windows
  · intro hWindows N hN hEven
    let c := N / 2
    have hNc : N = 2*c := by dsimp [c]; omega
    by_cases hcEq : c = 2
    · subst c
      exact ⟨2, 2, by norm_num, by norm_num, by omega⟩
    · by_cases hcPrime : c.Prime
      · exact ⟨c, c, hcPrime, hcPrime, by omega⟩
      · have hc4 : 4 ≤ c := by
          have hc3 : 3 ≤ c := by omega
          by_contra h
          have hcval : c = 3 := by omega
          exact hcPrime (hcval ▸ by norm_num)
        obtain ⟨p,q,hp3,hp,hq,hpc,hcq,hgap⟩ := prime_bracket c hc4 hcPrime
        have hoddp : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with heq | ho <;> omega
        have hoddq : q % 2 = 1 := by
          rcases hq.eq_two_or_odd with heq | ho <;> omega
        have hevenGap : (q-p) % 2 = 0 := by omega
        let k := (q-p)/2
        have hqeq : q = p + 2*k := by dsimp [k]; omega
        have hadj : AdjacentPrimes p (p+2*k) := by
          refine ⟨hp, ?_, ?_, ?_⟩
          · simpa [hqeq] using hq
          · omega
          · intro r hpr hrq'
            apply hgap r hpr
            simpa [hqeq] using hrq'
        have hjle : c-p ≤ 2*k := by omega
        have hwin := hWindows k p hadj
        have hgold := hwin (c-p) hjle
        have htarget : 2 * (p + (c-p)) = N := by omega
        exact htarget ▸ hgold

theorem windowStatement_two_iff_B2 : WindowStatement 2 ↔ B2 := by
  rfl

theorem conditional_window_induction (hB2 : B2)
    (hstep : ∀ k, 3 ≤ k → (∀ i, i < k → WindowStatement i) → WindowStatement k) :
    GlobalGoldbach := by
  apply (globalGoldbach_iff_all_windows).2
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      exact windowStatement_zero
    · by_cases hk1 : k = 1
      · subst k
        exact windowStatement_one
      · by_cases hk2 : k = 2
        · subst k
          exact hB2
        · apply hstep k (by omega)
          intro i hik
          exact ih i hik

end GoldbachDeltaInduction
