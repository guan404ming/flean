import Flean.Core.NearestRound

/-!
# Flean.Core.ULP

Unit in the Last Place (ULP) on the abstract real-number model.
Provides the real-valued ULP function and key lemmas:
- ulp definition via cexp
- rounding error bounded by ulp
- Sterbenz lemma
-/

namespace Flean

/-! ## ULP definition -/

/-- ULP of x: the weight of the least significant digit of x
    in the canonical representation. ulp(x) = β^(cexp(x)). -/
noncomputable def ulp (fmt : FloatFormat) (x : ℝ) : ℝ :=
  bpow fmt (cexp fmt x)

theorem ulp_pos (fmt : FloatFormat) (x : ℝ) : 0 < ulp fmt x :=
  bpow_pos fmt _

theorem ulp_ne_zero (fmt : FloatFormat) (x : ℝ) : ulp fmt x ≠ 0 :=
  ne_of_gt (ulp_pos fmt x)

/-! ## Generic ULP error bounds -/

/-- Any ZrndFn-based rounding has error at most one ULP. -/
theorem roundGeneric_error_le_ulp (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    |roundGeneric zr fmt x - x| ≤ ulp fmt x :=
  roundGeneric_sub_abs_le zr fmt x

/-- Any nearest-type rounding has error at most half a ULP. -/
theorem roundGenericNearest_error_le_half_ulp (zr : ZrndNearest) (fmt : FloatFormat) (x : ℝ) :
    |roundGeneric zr.toZrndFn fmt x - x| ≤ ulp fmt x / 2 :=
  roundGenericNearest_sub_abs_le zr fmt x

/-! ## Per-mode ULP error bounds -/

theorem roundTZ_error_lt_ulp (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x - x| < ulp fmt x :=
  roundTZ_error_abs fmt x

/-- Rounding toward zero never increases the absolute value. -/
theorem roundTZ_abs_le (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x| ≤ |x| :=
  roundTZ_le_abs fmt x

theorem roundDN_error_lt_ulp (fmt : FloatFormat) (x : ℝ) :
    |roundDN fmt x - x| < ulp fmt x :=
  roundDN_error_abs fmt x

theorem roundUP_error_lt_ulp (fmt : FloatFormat) (x : ℝ) :
    |roundUP fmt x - x| < ulp fmt x :=
  roundUP_error_abs fmt x

theorem roundNNE_error_le_half_ulp (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt x| ≤ ulp fmt x / 2 :=
  roundNNE_sub_abs_le fmt x

theorem roundNNA_error_le_half_ulp (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNA fmt x| ≤ ulp fmt x / 2 :=
  roundNNA_sub_abs_le fmt x

/-! ## ULP basic properties -/

theorem ulp_zero (fmt : FloatFormat) : ulp fmt 0 = bpow fmt fmt.emin := by
  unfold ulp; rw [cexp_zero]

theorem ulp_le_ulp_of_abs_le (fmt : FloatFormat) {x y : ℝ} (hxy : |x| ≤ |y|) :
    ulp fmt x ≤ ulp fmt y := by
  unfold ulp bpow
  exact zpow_le_zpow_right₀ fmt.β_one_lt.le (cexp_le_cexp_of_abs_le fmt hxy)

theorem ulp_le_abs (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    ulp fmt x ≤ |x| := by
  unfold ulp
  have h := bpow_cexp_le_machineEpsilon_mul_abs fmt hx
  have heps : machineEpsilon fmt ≤ 1 := by
    unfold machineEpsilon
    have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
    have : 1 - (fmt.prec : ℤ) ≤ 0 := by omega
    calc (fmt.β : ℝ) ^ (1 - (fmt.prec : ℤ))
        ≤ (fmt.β : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ fmt.β_one_lt.le this
      _ = 1 := zpow_zero _
  have habs : 0 ≤ |x| := abs_nonneg x
  calc bpow fmt (cexp fmt x) ≤ machineEpsilon fmt * |x| := h
    _ ≤ 1 * |x| := by exact mul_le_mul_of_nonneg_right heps habs
    _ = |x| := one_mul _

/-! ## ULP symmetry -/

theorem ulp_neg (fmt : FloatFormat) (x : ℝ) : ulp fmt (-x) = ulp fmt x := by
  unfold ulp; rw [cexp_neg]

end Flean
