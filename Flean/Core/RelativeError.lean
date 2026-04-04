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

/-! ## Existential standard model form: round(x) = x * (1 + δ) -/

private theorem x_ne_zero_of_normal (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) : x ≠ 0 := by
  intro h; subst h; simp at hx; linarith [zpow_pos fmt.β_pos (fmt.emin + ↑fmt.prec - 1)]

/-- Helper: given |round(x) - x| / |x| ≤ ε and x ≠ 0,
    produce δ = (round(x) - x) / x with |δ| ≤ ε and round(x) = x * (1 + δ). -/
private theorem relative_error_ex_of_div_le {x r ε : ℝ} (hx_ne : x ≠ 0)
    (hrel : |r - x| / |x| ≤ ε) :
    ∃ δ : ℝ, |δ| ≤ ε ∧ r = x * (1 + δ) := by
  refine ⟨(r - x) / x, ?_, ?_⟩
  · rwa [abs_div, div_le_iff₀ (abs_pos.mpr hx_ne), ← div_le_iff₀ (abs_pos.mpr hx_ne)]
  · ring_nf; field_simp; ring

theorem relative_error_NNE_ex (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    ∃ δ : ℝ, |δ| ≤ machineEpsilon fmt / 2 ∧ roundNNE fmt x = x * (1 + δ) :=
  relative_error_ex_of_div_le (x_ne_zero_of_normal fmt hx)
    (relative_error_roundNNE fmt hx)

theorem relative_error_NNA_ex (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    ∃ δ : ℝ, |δ| ≤ machineEpsilon fmt / 2 ∧ roundNNA fmt x = x * (1 + δ) := by
  have hx_ne := x_ne_zero_of_normal fmt hx
  have hrel := relative_error_roundNNA fmt hx
  rw [abs_sub_comm] at hrel
  exact relative_error_ex_of_div_le hx_ne hrel

theorem relative_error_roundTZ_ex (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    ∃ δ : ℝ, |δ| ≤ machineEpsilon fmt ∧ roundTZ fmt x = x * (1 + δ) :=
  relative_error_ex_of_div_le (x_ne_zero_of_normal fmt hx)
    (relative_error_roundTZ fmt hx)

theorem relative_error_roundDN_ex (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    ∃ δ : ℝ, |δ| ≤ machineEpsilon fmt ∧ roundDN fmt x = x * (1 + δ) :=
  relative_error_ex_of_div_le (x_ne_zero_of_normal fmt hx)
    (relative_error_roundDN fmt hx)

theorem relative_error_roundUP_ex (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    ∃ δ : ℝ, |δ| ≤ machineEpsilon fmt ∧ roundUP fmt x = x * (1 + δ) :=
  relative_error_ex_of_div_le (x_ne_zero_of_normal fmt hx)
    (relative_error_roundUP fmt hx)

end Flean
