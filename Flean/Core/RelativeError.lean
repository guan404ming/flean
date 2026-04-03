import Flean.Core.NearestAway

/-!
# Flean.Core.RelativeError

Relative error bounds in the form `|round(x) - x| / |x| ≤ ε`.
-/

namespace Flean

/-- Normal range hypothesis: x is in the normal range if |x| ≥ β^(emin+prec-1). -/
private theorem normal_abs_pos (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) : 0 < |x| :=
  lt_of_lt_of_le (zpow_pos fmt.β_pos _) hx

theorem relative_error_roundTZ (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundTZ fmt x - x| / |x| ≤ machineEpsilon fmt := by
  have hx_pos : 0 < |x| := normal_abs_pos fmt hx
  rw [div_le_iff₀ hx_pos]
  exact roundTZ_error fmt hx

theorem relative_error_roundNNE (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundNNE fmt x - x| / |x| ≤ machineEpsilon fmt / 2 := by
  have hx_pos : 0 < |x| := normal_abs_pos fmt hx
  rw [div_le_iff₀ hx_pos]
  have h := roundNNE_error_rel fmt hx
  rwa [abs_sub_comm]

theorem relative_error_roundDN (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundDN fmt x - x| / |x| ≤ machineEpsilon fmt := by
  have hx_pos : 0 < |x| := normal_abs_pos fmt hx
  rw [div_le_iff₀ hx_pos]
  exact roundDN_error_rel fmt hx

theorem relative_error_roundUP (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundUP fmt x - x| / |x| ≤ machineEpsilon fmt := by
  have hx_pos : 0 < |x| := normal_abs_pos fmt hx
  rw [div_le_iff₀ hx_pos]
  exact roundUP_error_rel fmt hx

theorem relative_error_roundNNA (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNA fmt x| / |x| ≤ machineEpsilon fmt / 2 := by
  have hx_pos : 0 < |x| := normal_abs_pos fmt hx
  rw [div_le_iff₀ hx_pos]
  exact roundNNA_error_rel fmt hx

end Flean
