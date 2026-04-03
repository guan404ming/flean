import Flean.Core.NearestAway

/-!
# Flean.Core.RoundRound

Ordering relationships between rounding modes.
-/

namespace Flean

/-! ## Three-way ordering: DN ≤ NNE ≤ UP -/

theorem roundDN_le_roundNNE_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundNNE fmt x ∧ roundNNE fmt x ≤ roundUP fmt x :=
  ⟨roundNNE_ge_roundDN fmt x, roundNNE_le_roundUP fmt x⟩

/-! ## roundTZ ordering relative to DN and UP -/

theorem roundDN_le_roundTZ_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    roundDN fmt x ≤ roundTZ fmt x :=
  (roundDN_eq_roundTZ_nonneg fmt hx).le

theorem roundTZ_le_roundUP_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    roundTZ fmt x ≤ roundUP fmt x := by
  rw [← roundDN_eq_roundTZ_nonneg fmt hx]
  exact le_trans (roundDN_le fmt x) (roundUP_ge fmt x)

/-! ## DN ≤ UP -/

theorem roundDN_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundUP fmt x :=
  le_trans (roundDN_le fmt x) (roundUP_ge fmt x)

/-! ## NNA ordering -/

theorem roundDN_le_roundNNA_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundNNA fmt x ∧ roundNNA fmt x ≤ roundUP fmt x :=
  ⟨roundNNA_ge_roundDN fmt x, roundNNA_le_roundUP fmt x⟩

end Flean
