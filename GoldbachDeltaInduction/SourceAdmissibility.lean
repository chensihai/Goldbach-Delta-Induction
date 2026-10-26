import GoldbachDeltaInduction.Basic

namespace GoldbachDeltaInduction

/-- Every prime modulus has a residue avoiding the three zero conditions
for `a`, `M - a`, and `N - a` (expressed as residues of `a`). -/
def SourceLocallyAdmissible (M N : ℕ) : Prop :=
  ∀ ell : ℕ, ell.Prime →
    ∃ a ∈ Finset.range ell, a ≠ 0 ∧ a ≠ M % ell ∧ a ≠ N % ell

/-- For even source and target, the only local obstruction is the three
residue classes modulo three. -/
theorem source_locally_admissible_iff_mod_three
    {M N : ℕ} (hM : M % 2 = 0) (hN : N % 2 = 0) :
    SourceLocallyAdmissible M N ↔ M % 3 = 0 ∨ N % 3 = 0 ∨ M % 3 = N % 3 := by
  constructor
  · intro h
    by_contra hbad
    have hM3 : M % 3 < 3 := Nat.mod_lt _ (by omega)
    have hN3 : N % 3 < 3 := Nat.mod_lt _ (by omega)
    have hMne : M % 3 ≠ 0 := by omega
    have hNne : N % 3 ≠ 0 := by omega
    have hMneqN : M % 3 ≠ N % 3 := by omega
    obtain ⟨a, ha, ha0, haM, haN⟩ := h 3 (by norm_num)
    have ha_lt : a < 3 := Finset.mem_range.mp ha
    have ha1 : a = 1 ∨ a = 2 := by omega
    rcases ha1 with ha1 | ha2 <;> omega
  · intro hgood ell hell
    have hell2 : ell = 2 ∨ ell = 3 ∨ 5 ≤ ell := by
      have htwo : 2 ≤ ell := hell.two_le
      have hnot4 : ell ≠ 4 := by
        intro heq
        subst ell
        norm_num at hell
      omega
    rcases hell2 with rfl | rfl | hell5
    · refine ⟨1, by simp, by norm_num, ?_, ?_⟩ <;> omega
    · have hM3 : M % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hN3 : N % 3 < 3 := Nat.mod_lt _ (by norm_num)
      by_cases hMzero : M % 3 = 0
      · by_cases hNone : N % 3 = 1
        · refine ⟨2, by norm_num, by norm_num, ?_, ?_⟩ <;> omega
        · refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩ <;> omega
      · by_cases hMone : M % 3 = 1
        · refine ⟨2, by norm_num, by norm_num, ?_, ?_⟩ <;>
            rcases hgood with hMz | hNz | hEq <;> omega
        · have hMtwo : M % 3 = 2 := by omega
          refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩ <;>
            rcases hgood with hMz | hNz | hEq <;> omega
    · let bad : Finset ℕ := {0, M % ell, N % ell}
      have hbadCard : bad.card ≤ 3 := by
        dsimp [bad]
        calc
          (insert 0 (insert (M % ell) ({N % ell} : Finset ℕ))).card
              ≤ (insert (M % ell) ({N % ell} : Finset ℕ)).card + 1 :=
                Finset.card_insert_le _ _
          _ ≤ ({N % ell} : Finset ℕ).card + 1 + 1 := by
                exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = 3 := by simp
      have hcard : bad.card < (Finset.range ell).card := by
        rw [Finset.card_range]
        omega
      obtain ⟨a, haRange, haNotBad⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hcard
      have ha0 : a ≠ 0 := by
        intro hz
        subst a
        exact haNotBad (by simp [bad])
      have haM : a ≠ M % ell := by
        intro hz
        subst a
        exact haNotBad (by simp [bad])
      have haN : a ≠ N % ell := by
        intro hz
        subst a
        exact haNotBad (by simp [bad])
      exact ⟨a, haRange, ha0, haM, haN⟩

/-- If the source and target residues modulo three are distinct and nonzero,
then any prime transfer `a+b=M`, `a+c=N` must use the prime three. -/
theorem three_prime_transfer_exception
    {M N a b c : ℕ}
    (hM : M % 3 ≠ 0) (hN : N % 3 ≠ 0) (hMN : M % 3 ≠ N % 3)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a + b = M) (hac : a + c = N) :
    a = 3 ∨ b = 3 ∨ c = 3 := by
  by_contra hnot
  have ha3 : a % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ a := Nat.dvd_of_mod_eq_zero hz
    rcases (Nat.dvd_prime ha).mp hd with h | h <;> omega
  have hb3 : b % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ b := Nat.dvd_of_mod_eq_zero hz
    rcases (Nat.dvd_prime hb).mp hd with h | h <;> omega
  have hc3 : c % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ c := Nat.dvd_of_mod_eq_zero hz
    rcases (Nat.dvd_prime hc).mp hd with h | h <;> omega
  have halt : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hblt : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hclt : c % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hMlt : M % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hNlt : N % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hMsum : (a + b) % 3 = M % 3 := by rw [hab]
  have hNsum : (a + c) % 3 = N % 3 := by rw [hac]
  push Not at hnot
  omega

end GoldbachDeltaInduction
