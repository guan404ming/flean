import Flean.Core.RoundProps

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

/-! ## ULP and rounding error -/

/-- The absolute rounding error of roundTZ is strictly less than one ULP. -/
theorem roundTZ_error_lt_ulp (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x - x| < ulp fmt x :=
  roundTZ_error_abs fmt x

/-- Rounding toward zero never increases the absolute value. -/
theorem roundTZ_abs_le (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x| ≤ |x| :=
  roundTZ_le_abs fmt x

/-! ## ULP symmetry -/

theorem ulp_neg (fmt : FloatFormat) (x : ℝ) : ulp fmt (-x) = ulp fmt x := by
  unfold ulp; rw [cexp_neg]

/-! ## Sterbenz lemma -/

/-- Helper: express x - y at the smaller exponent. -/
private theorem repr_diff_at_lower_exp (fmt : FloatFormat)
    {x y : ℝ} {mx my : ℤ} {ex ey : ℤ} (hle : ey ≤ ex)
    (hxval : x = (mx : ℝ) * (fmt.β : ℝ) ^ ex)
    (hyval : y = (my : ℝ) * (fmt.β : ℝ) ^ ey) :
    x - y = ((mx * (fmt.β : ℤ) ^ (ex - ey).toNat - my : ℤ) : ℝ) * (fmt.β : ℝ) ^ ey := by
  rw [hxval, hyval]; push_cast
  rw [sub_mul, mul_assoc, ← zpow_natCast, ← zpow_add₀ (FloatFormat.β_ne_zero fmt)]
  congr 1; rw [Int.toNat_of_nonneg (Int.sub_nonneg.mpr hle)]; ring

/-- Sterbenz lemma: if y/2 ≤ x ≤ 2y for representable x, y ≥ 0,
    then x - y is exactly representable (no rounding error). -/
theorem sterbenz (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundTZ fmt (x - y) = x - y := by
  apply roundTZ_repr_fixed
  obtain ⟨mx, ex, hxval, hmx, hex⟩ := hx
  obtain ⟨my, ey, hyval, hmy, hey⟩ := hy
  have hmx0 : 0 ≤ mx := by
    by_contra h; push Not at h
    linarith [show x < 0 from hxval ▸
      mul_neg_of_neg_of_pos (by exact_mod_cast h) (zpow_pos fmt.β_pos ex)]
  have hmy0 : 0 ≤ my := by
    by_contra h; push Not at h
    linarith [show y < 0 from hyval ▸
      mul_neg_of_neg_of_pos (by exact_mod_cast h) (zpow_pos fmt.β_pos ey)]
  by_cases heq : x = y
  · rw [heq, sub_self]; exact zero_isRepresentable fmt
  · by_cases hle : ey ≤ ex
    · -- Express x - y at exponent ey with significand d
      set d := mx * (fmt.β : ℤ) ^ (ex - ey).toNat - my
      have hval := repr_diff_at_lower_exp fmt hle hxval hyval
      -- hval : x - y = ↑d * β^ey (in ℝ, with zpow)
      have hval_bpow : x - y = (d : ℝ) * bpow fmt ey := by unfold bpow; exact hval
      refine ⟨d, ey, hval_bpow, ?_, hey⟩
      -- Need |d| < β^prec. Key: |x-y| ≤ y, so |d| * β^ey ≤ my * β^ey, so |d| ≤ my.
      have habs_xy : |x - y| ≤ y := by rw [abs_le]; constructor <;> linarith
      have hbp := zpow_pos fmt.β_pos ey
      have h1 : |(d : ℝ)| * (fmt.β : ℝ) ^ ey = |x - y| := by
        rw [hval, abs_mul, abs_of_pos hbp]
      have h2 : |(d : ℝ)| * (fmt.β : ℝ) ^ ey ≤ (my : ℝ) * (fmt.β : ℝ) ^ ey := by
        rw [h1]; linarith [hyval]
      have hd_le : |(d : ℝ)| ≤ (my : ℝ) := le_of_mul_le_mul_of_pos_right h2 hbp
      calc |d| ≤ my := by exact_mod_cast hd_le
        _ ≤ |my| := le_abs_self _
        _ < _ := hmy
    · -- ex < ey: express y - x at exponent ex, then negate
      push Not at hle
      have hle' := le_of_lt hle
      set d' := my * (fmt.β : ℤ) ^ (ey - ex).toNat - mx
      have hval' := repr_diff_at_lower_exp fmt hle' hyval hxval
      -- hval' : y - x = ↑d' * β^ex
      set d := -d'
      have hval : x - y = (d : ℝ) * (fmt.β : ℝ) ^ ex := by
        have : x - y = -((d' : ℝ) * (fmt.β : ℝ) ^ ex) := by linarith [hval']
        simp only [d, Int.cast_neg]; linarith
      have hval_bpow : x - y = (d : ℝ) * bpow fmt ex := by unfold bpow; exact hval
      refine ⟨d, ex, hval_bpow, ?_, hex⟩
      have habs_xy : |x - y| ≤ x := by rw [abs_le]; constructor <;> linarith
      have hbp := zpow_pos fmt.β_pos ex
      have h1 : |(d : ℝ)| * (fmt.β : ℝ) ^ ex = |x - y| := by
        rw [hval, abs_mul, abs_of_pos hbp]
      have h2 : |(d : ℝ)| * (fmt.β : ℝ) ^ ex ≤ (mx : ℝ) * (fmt.β : ℝ) ^ ex := by
        rw [h1]; linarith [hxval]
      have hd_le : |(d : ℝ)| ≤ (mx : ℝ) := le_of_mul_le_mul_of_pos_right h2 hbp
      calc |d| ≤ mx := by exact_mod_cast hd_le
        _ ≤ |mx| := le_abs_self _
        _ < _ := hmx

end Flean
