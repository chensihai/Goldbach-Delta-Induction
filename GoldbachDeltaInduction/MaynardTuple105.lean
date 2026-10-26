import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace GoldbachDeltaInduction

/-- Maynard's published 105-tuple, scaled by two. -/
def scaledMaynardTuple105 : Finset ℕ :=
  ({0, 10, 12, 24, 28, 30, 34, 42, 48, 52, 54, 64, 70, 72, 78, 82,
    90, 94, 100, 112, 114, 118, 120, 124, 132, 138, 148, 154, 168, 174, 178, 180, 184, 190, 192,
    202, 204, 208, 220, 222, 232, 234, 250, 252, 258, 262, 264, 268, 280, 288, 294, 300, 310, 322,
    324, 328, 330, 334, 342, 352, 358, 360, 364, 372, 378, 384, 390, 394, 400, 402, 408, 412, 418,
    420, 430, 432, 442, 444, 450, 454, 462, 468, 472, 478, 484, 490, 492, 498, 504, 510, 528, 532,
    534, 538, 544, 558, 562, 570, 574, 580, 582, 588, 594, 598, 600} : Finset ℕ).image (fun h => 2 * h)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem scaledMaynardTuple105_shape :
    scaledMaynardTuple105.card = 105 ∧
      ∀ h ∈ scaledMaynardTuple105, h % 4 = 0 ∧ h ≤ 1200 := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem scaledMaynardTuple105_admissible (p : ℕ) (hp : p.Prime) :
    ∃ a ∈ Finset.range p, a ∉ scaledMaynardTuple105.image (fun h => h % p) := by
  by_cases h : p < 106
  · have small : ∀ q ∈ Finset.range 106, q.Prime →
        ∃ a ∈ Finset.range q, a ∉ scaledMaynardTuple105.image (fun h => h % q) := by
      decide
    exact small p (Finset.mem_range.mpr h) hp
  · apply Finset.exists_mem_notMem_of_card_lt_card
    exact Finset.card_image_le.trans_lt
      (by simpa [scaledMaynardTuple105_shape.1] using (show 105 < p by omega))

end GoldbachDeltaInduction
