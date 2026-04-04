import Flean.Core.Representable
import Flean.Core.ULP

/-!
# Flean.Core.Sterbenz

Sterbenz lemma in two forms:
1. `sterbenz`: for `isRepresentable` and `roundTZ`.
2. `sterbenz_generic`: for `generic_format` and arbitrary `ZrndFn`.

Corresponds to Flocq's `sterbenz` in `Flocq.Core.Sterbenz`.
-/

namespace Flean

/-! ## isRepresentable version -/

/-- Helper: express x - y at the smaller exponent. -/
private theorem repr_diff_at_lower_exp (fmt : FloatFormat)
    {x y : ℝ} {mx my : ℤ} {ex ey : ℤ} (hle : ey ≤ ex)
    (hxval : x = (mx : ℝ) * (fmt.β : ℝ) ^ ex)
    (hyval : y = (my : ℝ) * (fmt.β : ℝ) ^ ey) :
    x - y = ((mx * (fmt.β : ℤ) ^ (ex - ey).toNat - my : ℤ) : ℝ) * (fmt.β : ℝ) ^ ey := by
  rw [hxval, hyval]; push_cast
  rw [sub_mul, mul_assoc, ← zpow_natCast, ← zpow_add₀ (FloatFormat.β_ne_zero fmt)]
  congr 1; rw [Int.toNat_of_nonneg (Int.sub_nonneg.mpr hle)]; ring_nf

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
    · set d := mx * (fmt.β : ℤ) ^ (ex - ey).toNat - my
      have hval := repr_diff_at_lower_exp fmt hle hxval hyval
      have hval_bpow : x - y = (d : ℝ) * bpow fmt ey := by unfold bpow; exact hval
      refine ⟨d, ey, hval_bpow, ?_, hey⟩
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
    · push Not at hle
      have hle' := le_of_lt hle
      set d' := my * (fmt.β : ℤ) ^ (ey - ex).toNat - mx
      have hval' := repr_diff_at_lower_exp fmt hle' hyval hxval
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

/-! ## generic_format version -/

/-- Generic Sterbenz lemma: if y/2 ≤ x ≤ 2y for representable x, y ≥ 0,
    then x - y is in generic_format (hence exactly representable). -/
theorem sterbenz_generic (fmt : FloatFormat) {x y : ℝ}
    (hx : generic_format fmt x) (hy : generic_format fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    generic_format fmt (x - y) := by
  rw [generic_format_iff_roundTZ_fixed]
  rw [generic_format_iff_repr] at hx hy
  exact sterbenz fmt hx hy hx0 hy0 hxy hyx

/-- Generic Sterbenz: any rounding of x - y equals x - y. -/
theorem sterbenz_round_exact (zr : ZrndFn) (fmt : FloatFormat) {x y : ℝ}
    (hx : generic_format fmt x) (hy : generic_format fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundGeneric zr fmt (x - y) = x - y :=
  generic_format_round_fixed zr fmt (sterbenz_generic fmt hx hy hx0 hy0 hxy hyx)

/-- Sterbenz for roundNNE specifically. -/
theorem sterbenz_roundNNE (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundNNE fmt (x - y) = x - y := by
  rw [roundNNE_eq_generic]
  exact sterbenz_round_exact zrndNNE.toZrndFn fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

/-- Sterbenz for roundNNA specifically. -/
theorem sterbenz_roundNNA (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundNNA fmt (x - y) = x - y := by
  rw [roundNNA_eq_generic]
  exact sterbenz_round_exact zrndNNA.toZrndFn fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

/-- Sterbenz for roundUP specifically. -/
theorem sterbenz_roundUP (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundUP fmt (x - y) = x - y := by
  rw [roundUP_eq_generic]
  exact sterbenz_round_exact zrndUP fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

/-- Sterbenz for roundDN specifically. -/
theorem sterbenz_roundDN (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundDN fmt (x - y) = x - y := by
  rw [roundDN_eq_generic]
  exact sterbenz_round_exact zrndDN fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

end Flean
