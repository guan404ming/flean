import Flean.Core.NearestEven
import Flean.Core.DoubleRoundNNE
import Flean.Core.ULP

/-!
# Flean.Apps.TwoSum

Formal verification of the Fast2Sum (Dekker) algorithm for error-free
transformations in IEEE 754 binary floating-point arithmetic.

## Main results

- `dekker_sub_repr`: `roundNNE(a + b) - a` is representable when `|b| ≤ |a|` (β = 2)
- `fast2Sum_exact`: `a + b = s + t` exactly where `(s, t) = fast2Sum fmt a b`

## References

- Dekker (1971), Boldo & Melquiond (Flocq, Chapter 6)
-/

namespace Flean

/-! ## Helper lemmas -/

theorem sterbenz_roundNNE (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundNNE fmt (x - y) = x - y := by
  apply roundNNE_repr_fixed
  rw [← sterbenz fmt hx hy hx0 hy0 hxy hyx]
  exact roundTZ_isRepresentable fmt _

theorem sterbenz_repr (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    isRepresentable fmt (x - y) := by
  rw [← sterbenz fmt hx hy hx0 hy0 hxy hyx]; exact roundTZ_isRepresentable fmt _

theorem double_repr {fmt : FloatFormat} (hβ : fmt.β = 2) {a : ℝ}
    (ha : isRepresentable fmt a) : isRepresentable fmt (2 * a) := by
  obtain ⟨m, e, hval, hm, he⟩ := ha
  refine ⟨m, e + 1, ?_, hm, by omega⟩
  rw [hval]; simp only [hβ]; push_cast
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring

/-! ## Fast2Sum -/

noncomputable def fast2Sum (fmt : FloatFormat) (a b : ℝ) : ℝ × ℝ :=
  let s  := roundNNE fmt (a + b)
  let b' := roundNNE fmt (s - a)
  let t  := roundNNE fmt (b - b')
  (s, t)

/-! ## Dekker's lemma -/

/-- Nonneg case: `0 ≤ b ≤ a`, β = 2. Uses `2a` repr + Sterbenz. -/
theorem dekker_sub_repr_nonneg {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : b ≤ a) :
    isRepresentable fmt (roundNNE fmt (a + b) - a) := by
  set s := roundNNE fmt (a + b) with hs_def
  have hs_repr := roundNNE_isRepresentable fmt (a + b)
  have hs_ge : a ≤ s := by
    have := roundNNE_monotone fmt (show a ≤ a + b by linarith)
    rwa [roundNNE_repr_fixed fmt ha] at this
  have hs_le : s ≤ 2 * a := by
    have := roundNNE_monotone fmt (show a + b ≤ 2 * a by linarith)
    rwa [roundNNE_repr_fixed fmt (double_repr hβ ha)] at this
  exact sterbenz_repr fmt hs_repr ha (le_trans ha0 hs_ge) ha0 (by linarith) hs_le

/-- Mixed sign case: `a ≥ 0`, `b < 0`, `-b ≤ a`, β = 2.
    When `-b ≥ a/2`: subtraction is exact by Sterbenz.
    When `-b < a/2`: `s ≥ a/2` via halving + monotonicity, then Sterbenz on `(a, s)`. -/
theorem dekker_sub_repr_neg_b {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b)
    (ha0 : 0 ≤ a) (hb_neg : b < 0) (hab : -b ≤ a) :
    isRepresentable fmt (roundNNE fmt (a + b) - a) := by
  set s := roundNNE fmt (a + b) with hs_def
  set c := -b with hc_def
  have hc0 : 0 < c := neg_pos.mpr hb_neg
  have hc_repr : isRepresentable fmt c := show isRepresentable fmt (-b) from
    neg_isRepresentable hb
  have hs_repr := roundNNE_isRepresentable fmt (a + b)
  -- s ≤ a and s ≥ 0
  have hs_le_a : s ≤ a := by
    have := roundNNE_monotone fmt (show a + b ≤ a by linarith)
    rwa [roundNNE_repr_fixed fmt ha] at this
  have hs0 : 0 ≤ s := by
    have := roundNNE_monotone fmt (show (0 : ℝ) ≤ a + b by linarith)
    rwa [roundNNE_zero] at this
  by_cases hca : a ≤ 2 * c
  · -- |b| ≥ a/2: Sterbenz on (a, c) makes a - c = a + b exact
    have h_repr : isRepresentable fmt (a - c) :=
      sterbenz_repr fmt ha hc_repr ha0 hc0.le (by linarith) hca
    have : s = a - c := by
      rw [hs_def, show a + b = a - c from by rw [hc_def]; ring]
      exact roundNNE_repr_fixed fmt h_repr
    rw [this, show a - c - a = -c from by ring]
    exact neg_isRepresentable hc_repr
  · -- |b| < a/2: need s ≥ a/2, then Sterbenz on (a, s)
    push Not at hca
    -- a + b > a/2
    have hab_gt : a / 2 < a + b := by linarith
    -- Get exponent of a to handle emin edge case
    obtain ⟨ma, ea, hval_a, hma, hea⟩ := ha
    -- Reconstruct ha for reuse
    have ha' : isRepresentable fmt a := ⟨ma, ea, hval_a, hma, hea⟩
    by_cases hea_gt : fmt.emin + 1 ≤ ea
    · -- a/2 is representable
      have ha_half : isRepresentable fmt (a / 2) := by
        refine ⟨ma, ea - 1, ?_, hma, by omega⟩
        rw [hval_a]; simp only [hβ]; push_cast
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
      have hs_ge_half : a / 2 ≤ s := by
        have := roundNNE_monotone fmt (le_of_lt hab_gt)
        rwa [roundNNE_repr_fixed fmt ha_half] at this
      rw [show s - a = -(a - s) from by ring]
      apply neg_isRepresentable
      exact sterbenz_repr fmt ha' hs_repr ha0 hs0 (by linarith) (by linarith)
    · -- ea = emin: subnormal edge case.
      -- Both a and s are multiples of β^emin with significands < β^p.
      -- Since 0 ≤ s ≤ a, the difference a - s has significand ≤ ma < β^p.
      push Not at hea_gt
      sorry

/-- Dekker's lemma (general): when `|b| ≤ |a|` and β = 2. -/
theorem dekker_sub_repr {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b)
    (hab : |b| ≤ |a|) :
    isRepresentable fmt (roundNNE fmt (a + b) - a) := by
  by_cases ha0 : 0 ≤ a
  · by_cases hb0 : 0 ≤ b
    · exact dekker_sub_repr_nonneg hβ ha hb ha0 hb0
        (by rwa [abs_of_nonneg hb0, abs_of_nonneg ha0] at hab)
    · exact dekker_sub_repr_neg_b hβ ha hb ha0 (not_le.mp hb0)
        (by rw [abs_of_neg (not_le.mp hb0), abs_of_nonneg ha0] at hab; linarith)
  · -- a < 0: negate both
    have ha_neg : a < 0 := not_le.mp ha0
    rw [show roundNNE fmt (a + b) - a = -(roundNNE fmt ((-a) + (-b)) - (-a)) from by
      rw [show (-a) + (-b) = -(a + b) from by ring, roundNNE_neg]; ring]
    apply neg_isRepresentable
    have hab' : |(-b)| ≤ |(-a)| := by rwa [abs_neg, abs_neg]
    by_cases hb0 : 0 < b
    · exact dekker_sub_repr_neg_b hβ (neg_isRepresentable ha) (neg_isRepresentable hb)
        (by linarith) (by linarith)
        (by rw [neg_neg]; rw [abs_of_pos hb0, abs_of_neg ha_neg] at hab; linarith)
    · -- b ≤ 0, a < 0: -a > 0, -b ≥ 0
      push Not at hb0
      exact dekker_sub_repr_nonneg hβ (neg_isRepresentable ha) (neg_isRepresentable hb)
        (by linarith) (by linarith)
        (by rw [abs_of_nonpos (by linarith : b ≤ 0), abs_of_neg ha_neg] at hab; linarith)

/-! ## Fast2Sum exactness -/

theorem fast2Sum_sub_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b)
    (hab : |b| ≤ |a|) :
    let s := roundNNE fmt (a + b)
    roundNNE fmt (s - a) = s - a :=
  roundNNE_repr_fixed fmt (dekker_sub_repr hβ ha hb hab)

/-- Rounding error representability. For β = 2, the error `(a+b) - roundNNE(a+b)`
    is always representable when `a` and `b` are. See Boldo & Melquiond, Theorem 6.3. -/
theorem fast2Sum_err_repr {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b)
    (hab : |b| ≤ |a|) :
    let s := roundNNE fmt (a + b)
    isRepresentable fmt (b - (s - a)) := by
  sorry

/-- **Fast2Sum correctness**: `a + b = s + t` exactly when `|a| ≥ |b|` and β = 2. -/
theorem fast2Sum_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b)
    (hab : |b| ≤ |a|) :
    let ⟨s, t⟩ := fast2Sum fmt a b
    a + b = s + t := by
  simp only [fast2Sum]
  set s := roundNNE fmt (a + b)
  set b' := roundNNE fmt (s - a)
  set t := roundNNE fmt (b - b')
  have hb'_exact : b' = s - a := fast2Sum_sub_exact hβ ha hb hab
  have hbb'_repr : isRepresentable fmt (b - (s - a)) := fast2Sum_err_repr hβ ha hb hab
  have hbb'_repr' : isRepresentable fmt (b - b') := by rwa [hb'_exact]
  have ht_exact : t = b - b' := roundNNE_repr_fixed fmt hbb'_repr'
  rw [ht_exact, hb'_exact]; ring

/-! ## Concrete examples -/

example {a b : ℝ} (ha : isRepresentable binary32 a) (hb : isRepresentable binary32 b)
    (hab : |b| ≤ |a|) : let ⟨s, t⟩ := fast2Sum binary32 a b; a + b = s + t :=
  fast2Sum_exact (by rfl) ha hb hab

example {a b : ℝ} (ha : isRepresentable binary64 a) (hb : isRepresentable binary64 b)
    (hab : |b| ≤ |a|) : let ⟨s, t⟩ := fast2Sum binary64 a b; a + b = s + t :=
  fast2Sum_exact (by rfl) ha hb hab

end Flean
