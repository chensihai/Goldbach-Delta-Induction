import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

namespace GoldbachDeltaInduction

/-- A single residue class in any integer interval differs from its rational
length/modulus main term by strictly less than one. This is an unconditional
integer counting estimate; it is not a prime-distribution estimate. -/
theorem residue_count_error (a b r v : ℤ) (hab : a≤b) (hr : 0<r) :
    |((((Finset.Ico a b).filter (fun x => Int.ModEq r x v)).card : ℕ) : ℚ)
        - ((b-a : ℤ) : ℚ)/(r : ℚ)| < 1 := by
  let X : ℚ := (a-v : ℤ)/(r : ℚ)
  let Y : ℚ := (b-v : ℤ)/(r : ℚ)
  have hrq : (0 : ℚ)<r := by exact_mod_cast hr
  have hxy : X≤Y := by
    dsimp [X,Y]
    apply div_le_div_of_nonneg_right _ hrq.le
    exact_mod_cast sub_le_sub_right hab v
  have hceil : Int.ceil X ≤ Int.ceil Y := Int.ceil_mono hxy
  have hcount : (((Finset.Ico a b).filter (fun x => Int.ModEq r x v)).card : ℤ)
      = max (Int.ceil Y - Int.ceil X) 0 := by
    simpa only [X,Y,Int.cast_sub] using (Int.Ico_filter_modEq_card a b hr v)
  have hcount' : (((Finset.Ico a b).filter (fun x => Int.ModEq r x v)).card : ℤ)
      = Int.ceil Y - Int.ceil X := by
    simpa only [max_eq_left (sub_nonneg.mpr hceil)] using hcount
  have hc : ((((Finset.Ico a b).filter (fun x => Int.ModEq r x v)).card : ℕ) : ℚ)
      = (Int.ceil Y : ℚ) - (Int.ceil X : ℚ) := by exact_mod_cast hcount'
  have hxlo := Int.le_ceil X
  have hxhi := Int.ceil_lt_add_one X
  have hylo := Int.le_ceil Y
  have hyhi := Int.ceil_lt_add_one Y
  have hdiff : Y-X=((b-a : ℤ) : ℚ)/(r : ℚ) := by
    dsimp [X,Y]
    push_cast
    ring
  rw [hc]
  apply abs_lt.mpr
  constructor <;> linarith

end GoldbachDeltaInduction
