import GoldbachDeltaInduction.StructuralCountermodel

/-! An abstract set model, not a counterexample about actual primes. -/
namespace GoldbachDeltaInduction.SquareDenseCountermodel

def P (n : ℕ) : Prop :=
  StructuralCountermodel.P n ∨ n = 41 ∨ n = 47 ∨ n = 59 ∨ n = 61 ∨
    n = 67 ∨ n = 71 ∨ n = 73 ∨ n = 79 ∨ n = 83 ∨ n = 89 ∨ n = 97

def G (N : ℕ) : Prop := ∃ a b, P a ∧ P b ∧ a + b = N

def Adj (p q : ℕ) : Prop :=
  P p ∧ P q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ P r

theorem oldP_inclusion {n : ℕ} (h : StructuralCountermodel.P n) : P n := Or.inl h

theorem even_ge_108_goldbach (N : ℕ) (hN : 108 ≤ N) (heven : N % 2 = 0) :
    G N := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    StructuralCountermodel.even_ge_108_goldbach N hN heven
  exact ⟨a, b, oldP_inclusion ha, oldP_inclusion hb, hab⟩

theorem full_gap_four_windows :
    ∀ p, P p → P (p + 4) → ∀ j ≤ 4, G (2 * (p + j)) := by
  intro p hp hp4 j hj
  by_cases hlarge : 54 ≤ p
  · exact even_ge_108_goldbach _ (by omega) (by omega)
  · have hcases : p = 3 ∨ p = 7 ∨ p = 13 ∨ p = 19 := by
      unfold P StructuralCountermodel.P at hp hp4
      omega
    have holdp : StructuralCountermodel.P p := by
      rcases hcases with rfl | rfl | rfl | rfl <;>
        norm_num [StructuralCountermodel.P]
    have holdp4 : StructuralCountermodel.P (p + 4) := by
      rcases hcases with rfl | rfl | rfl | rfl <;>
        norm_num [StructuralCountermodel.P]
    obtain ⟨a, b, ha, hb, hab⟩ :=
      StructuralCountermodel.full_gap_four_windows p holdp holdp4 j hj
    exact ⟨a, b, oldP_inclusion ha, oldP_inclusion hb, hab⟩

theorem gap_six_failure : Adj 23 29 ∧ ¬ G 56 := by
  constructor
  · refine ⟨by norm_num [P, StructuralCountermodel.P],
      by norm_num [P, StructuralCountermodel.P], by norm_num, ?_⟩
    intro r hlo hhi hr
    unfold P StructuralCountermodel.P at hr
    omega
  · rintro ⟨a, b, ha, hb, hab⟩
    unfold P StructuralCountermodel.P at ha hb
    omega

theorem two_members_per_square_interval (m : ℕ) (hm : 1 ≤ m) :
    ∃ p q, P p ∧ P q ∧ m ^ 2 < p ∧ p < q ∧ q < (m + 1) ^ 2 := by
  by_cases hlarge : 19 ≤ m
  · let t := m ^ 2 / 30 + 1
    have hm2 : 361 ≤ m ^ 2 := by nlinarith
    have hp101 : 101 ≤ 30 * t + 1 := by dsimp [t]; omega
    have hq101 : 101 ≤ 30 * t + 7 := by omega
    have hp : P (30 * t + 1) := by
      unfold P StructuralCountermodel.P
      omega
    have hq : P (30 * t + 7) := by
      unfold P StructuralCountermodel.P
      omega
    have hplow : m ^ 2 < 30 * t + 1 := by dsimp [t]; omega
    have hqupper : 30 * t + 7 ≤ m ^ 2 + 37 := by dsimp [t]; omega
    refine ⟨30 * t + 1, 30 * t + 7, hp, hq, hplow, by omega, ?_⟩
    nlinarith
  · have hsmall : m ≤ 18 := by omega
    interval_cases m
    · exact ⟨2, 3, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 7, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 13, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 19, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨29, 31, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨41, 47, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨59, 61, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨67, 71, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨83, 89, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨101, 103, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨127, 131, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨149, 151, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨173, 179, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨197, 199, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨227, 229, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨257, 263, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨293, 307, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩
    · exact ⟨331, 337, by norm_num [P, StructuralCountermodel.P],
        by norm_num [P, StructuralCountermodel.P], by norm_num, by norm_num, by norm_num⟩

theorem adjacent_pair_per_square_interval (m : ℕ) (hm : 1 ≤ m) :
    ∃ p q, Adj p q ∧ m ^ 2 < p ∧ q < (m + 1) ^ 2 := by
  classical
  obtain ⟨p, b, hp, hb, hlo, hpb, hbhi⟩ := two_members_per_square_interval m hm
  have hex : ∃ q, p < q ∧ P q := ⟨b, hpb, hb⟩
  let q := Nat.find hex
  have hq := Nat.find_spec hex
  have hqb : q ≤ b := Nat.find_min' hex ⟨hpb, hb⟩
  refine ⟨p, q, ⟨hp, hq.2, hq.1, ?_⟩, hlo, lt_of_le_of_lt hqb hbhi⟩
  intro r hpr hrq hr
  have hqr : q ≤ r := Nat.find_min' hex ⟨hpr, hr⟩
  omega

end GoldbachDeltaInduction.SquareDenseCountermodel
