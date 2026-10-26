import GoldbachDeltaInduction.DeltaGap

namespace GoldbachDeltaInduction

def OffsetFactorCertificate (c delta : ℕ) (factors : List ℕ) : Prop :=
  factors.length=delta ∧ ∀ e : Fin delta,
    let f := factors[e.val]!
    1<f ∧ ((f ∣ c-e.val ∧ f<c-e.val) ∨ (f ∣ c+e.val ∧ f<c+e.val))

instance (c delta : ℕ) (factors : List ℕ) :
    Decidable (OffsetFactorCertificate c delta factors) :=
  inferInstanceAs (Decidable (factors.length=delta ∧ ∀ e : Fin delta,
    let f := factors[e.val]!
    1<f ∧ ((f ∣ c-e.val ∧ f<c-e.val) ∨ (f ∣ c+e.val ∧ f<c+e.val))))

theorem proper_factor_not_prime {n f : ℕ}
    (hf : 1<f) (hfn : f<n) (hdiv : f ∣ n) : ¬n.Prime := by
  intro hp
  have hx := hp.eq_one_or_self_of_dvd f hdiv
  omega

/-- Each smaller offset comes with a proper factor of at least one endpoint.
The factor data are checked by integer division, without rerunning primality
searches for every excluded endpoint. -/
theorem factor_certificate_excludes {c delta : ℕ} {factors : List ℕ}
    (hcert : OffsetFactorCertificate c delta factors) :
    ∀ e ∈ Finset.range delta, ¬SymmetricPrimePair c e := by
  intro e he hpair
  have hf := hcert.2 ⟨e,Finset.mem_range.1 he⟩
  rcases hf with ⟨hgt,hleft | hright⟩
  · exact proper_factor_not_prime hgt hleft.2 hleft.1 hpair.2.1
  · exact proper_factor_not_prime hgt hright.2 hright.1 hpair.2.2

end GoldbachDeltaInduction
