import GoldbachDeltaInduction.ClusterResidueObstruction

namespace GoldbachDeltaInduction

/-- If every prime in the indicated window lies in the residue class of `T`
modulo a divisor `B > 2`, then a symmetric prime pair centered at
`T + h + 1` must have offset larger than the isolation radius. -/
theorem isolated_primes_force_offset_gt
    (T L R h delta : ℕ) (B : ℤ)
    (hB : 2 < B)
    (hh : B ∣ (h : ℤ))
    (hhL : h ≤ L)
    (hpair : SymmetricPrimePair (T + h + 1) delta)
    (hisolate : ∀ z : ℕ,
      T - R ≤ z → z ≤ T + L + R + 2 → z.Prime →
        B ∣ ((z : ℤ) - (T : ℤ))) :
    R < delta := by
  by_contra hnot
  have hdeltaR : delta ≤ R := by omega
  rcases hpair with ⟨hdelta, hleft, hright⟩
  have hleftlo : T - R ≤ T + h + 1 - delta := by omega
  have hlefthi : T + h + 1 - delta ≤ T + L + R + 2 := by omega
  have hrightlo : T - R ≤ T + h + 1 + delta := by omega
  have hrighthi : T + h + 1 + delta ≤ T + L + R + 2 := by omega
  have hleftdiv := hisolate (T + h + 1 - delta) hleftlo hlefthi hleft
  have hrightdiv := hisolate (T + h + 1 + delta) hrightlo hrighthi hright
  have hsum :
      ((T + h + 1 - delta : ℕ) : ℤ) +
        ((T + h + 1 + delta : ℕ) : ℤ) =
        2 * ((T : ℤ) + (h : ℤ) + 1) := by
    omega
  exact cluster_residue_sum_obstruction hB hleftdiv hrightdiv hh hsum

end GoldbachDeltaInduction
