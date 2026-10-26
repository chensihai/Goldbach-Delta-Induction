import GoldbachDeltaInduction.UniversalSourceTransfer

namespace GoldbachDeltaInduction

/-- If an even source is 8 modulo 30, shifting either prime endpoint by two
hits a proper multiple of three. -/
theorem all_source_pairs_blocked_mod30 {M a b : ℕ}
    (hM : 8 < M) (hmod : M % 30 = 8)
    (ha : a.Prime) (hb : b.Prime) (hsum : a + b = M) :
    ¬ (a + 2).Prime ∧ ¬ (b + 2).Prime := by
  have hMeven : M % 2 = 0 := by omega
  have ha2 : a ≠ 2 := by
    intro heq
    subst a
    have hbEven : b % 2 = 0 := by omega
    rcases hb.eq_two_or_odd with hb2 | hbodd
    · omega
    · omega
  have hb2 : b ≠ 2 := by
    intro heq
    subst b
    have haEven : a % 2 = 0 := by omega
    rcases ha.eq_two_or_odd with ha2 | haodd
    · omega
    · omega
  have hM5 : M % 5 = 3 := by omega
  have haNe3 : a ≠ 3 := by
    intro heq
    subst a
    have hbdiv5 : 5 ∣ b := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have hbgt5 : 5 < b := by omega
    rcases (Nat.dvd_prime hb).mp hbdiv5 with h | h <;> omega
  have hbNe3 : b ≠ 3 := by
    intro heq
    subst b
    have hadiv5 : 5 ∣ a := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have hagt5 : 5 < a := by omega
    rcases (Nat.dvd_prime ha).mp hadiv5 with h | h <;> omega
  have ha3 : a % 3 ≠ 0 := by
    intro hzero
    have hadiv : 3 ∣ a := Nat.dvd_of_mod_eq_zero hzero
    rcases (Nat.dvd_prime ha).mp hadiv with h | h <;> omega
  have hb3 : b % 3 ≠ 0 := by
    intro hzero
    have hbdiv : 3 ∣ b := Nat.dvd_of_mod_eq_zero hzero
    rcases (Nat.dvd_prime hb).mp hbdiv with h | h <;> omega
  have haodd : a % 2 = 1 := by
    rcases ha.eq_two_or_odd with h | h <;> omega
  have hbodd : b % 2 = 1 := by
    rcases hb.eq_two_or_odd with h | h <;> omega
  have hM3 : M % 3 = 2 := by omega
  have hares : a % 3 = 1 := by
    have hlt : a % 3 < 3 := Nat.mod_lt _ (by omega)
    have hblt : b % 3 < 3 := Nat.mod_lt _ (by omega)
    omega
  have hbres : b % 3 = 1 := by
    have hlt : a % 3 < 3 := Nat.mod_lt _ (by omega)
    have hblt : b % 3 < 3 := Nat.mod_lt _ (by omega)
    omega
  have hdiva : 3 ∣ a + 2 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hdivb : 3 ∣ b + 2 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hgtA : 3 < a + 2 := by
    have := ha.two_le
    omega
  have hgtB : 3 < b + 2 := by
    have := hb.two_le
    omega
  constructor
  · intro hprime
    have hcases := (Nat.dvd_prime hprime).mp hdiva
    rcases hcases with h | h <;> omega
  · intro hprime
    have hcases := (Nat.dvd_prime hprime).mp hdivb
    rcases hcases with h | h <;> omega

end GoldbachDeltaInduction
