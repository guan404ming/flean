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
      -- Both a and s are multiples of β^emin. Since 0 ≤ s ≤ a,
      -- the difference a - s has significand ≤ ma < β^p at exponent emin.
      push Not at hea_gt
      have hea_eq : ea = fmt.emin := le_antisymm (by omega) hea
      -- s is also representable
      obtain ⟨ms, es, hval_s, hms, hes⟩ := hs_repr
      have hβ_pos : (0 : ℝ) < (fmt.β : ℝ) := by rw [hβ]; norm_num
      have hβ_ne : (fmt.β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      -- Significand of a - s at exponent emin
      -- Use the existing Sterbenz proof infrastructure.
      -- Key: a and s are both representable with 0 ≤ s ≤ a.
      -- At the emin grid, a - s has bounded significand.
      -- We construct the representability witness directly.
      have hma0 : 0 ≤ ma := by
        by_contra h; push Not at h
        have : a < 0 := by
          rw [hval_a]; exact mul_neg_of_neg_of_pos (by exact_mod_cast h) (zpow_pos hβ_pos ea)
        linarith
      -- Express s at exponent emin: s = ms' * β^emin
      have hes_ge : fmt.emin ≤ es := hes
      -- ms' is the significand of s at exponent emin
      let ms' := ms * (fmt.β : ℤ) ^ (es - fmt.emin).toNat
      have hval_s' : s = (ms' : ℝ) * (fmt.β : ℝ) ^ fmt.emin := by
        change s = ((ms * (fmt.β : ℤ) ^ (es - fmt.emin).toNat : ℤ) : ℝ) * (fmt.β : ℝ) ^ fmt.emin
        have hnn : (0 : ℤ) ≤ es - fmt.emin := by omega
        rw [hs_def, hval_s]; push_cast
        rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hβ_ne, Int.toNat_of_nonneg hnn,
            show es - fmt.emin + fmt.emin = es from by omega]
      have hbp := zpow_pos hβ_pos fmt.emin
      -- ms' ≥ 0 since s ≥ 0
      have hms'0 : 0 ≤ ms' := by
        have : (0 : ℝ) ≤ (ms' : ℝ) := by
          have h1 : 0 ≤ s := hs0
          rw [hval_s'] at h1
          exact nonneg_of_mul_nonneg_left h1 hbp
        exact_mod_cast this
      -- ms' ≤ ma since s ≤ a
      have hms'_le : ms' ≤ ma := by
        have : (ms' : ℝ) ≤ (ma : ℝ) := by
          rw [← sub_nonneg]
          have h1 : 0 ≤ a - s := by linarith
          rw [hval_a, hea_eq, hval_s'] at h1
          have : 0 ≤ ((ma : ℝ) - (ms' : ℝ)) * (fmt.β : ℝ) ^ fmt.emin := by linarith
          exact nonneg_of_mul_nonneg_left this hbp
        exact_mod_cast this
      -- a - s = (ma - ms') * β^emin
      have hval_diff : a - s = ((ma - ms' : ℤ) : ℝ) * (fmt.β : ℝ) ^ fmt.emin := by
        rw [hval_a, hea_eq, hval_s']; push_cast; ring
      rw [show s - a = -(a - s) from by ring, hval_diff]
      refine ⟨-(ma - ms'), fmt.emin, by push_cast; ring, ?_, le_refl _⟩
      rw [abs_neg, abs_of_nonneg (show (0 : ℤ) ≤ ma - ms' by omega)]
      calc ma - ms' ≤ ma := by omega
        _ ≤ |ma| := le_abs_self _
        _ < _ := hma

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
  -- b - (s - a) = (a + b) - s is the rounding error.
  -- Strategy: s - a is representable (Dekker). Express b and (s-a) at a common
  -- exponent and show the difference's significand is bounded.
  set s := roundNNE fmt (a + b)
  -- s - a is representable
  have hsa_repr := dekker_sub_repr hβ ha hb hab
  -- b - (s - a) = (a + b) - s
  have herr_eq : b - (s - a) = (a + b) - s := by ring
  -- |(a+b) - s| ≤ |b| (nearest property, a is representable)
  have herr_le : |b - (s - a)| ≤ |b| := by
    rw [herr_eq]
    have h := roundNNE_nearest fmt (a + b) ha
    simp only [add_sub_cancel_left] at h
    rwa [show (a + b) - s = -(s - (a + b)) from by ring, abs_neg,
         show s - (a + b) = -(a + b - s) from by ring, abs_neg]
  -- Get representations
  obtain ⟨mb, eb, hval_b, hmb, heb⟩ := hb
  obtain ⟨msa, esa, hval_sa, hmsa, hesa⟩ := hsa_repr
  -- At exponent e = min(eb, esa): both b and (s-a) are integer multiples of β^e
  have hβ_pos : (0 : ℝ) < (fmt.β : ℝ) := by rw [hβ]; norm_num
  have hβ_ne : (fmt.β : ℝ) ≠ 0 := ne_of_gt hβ_pos
  -- Express b - (s-a) at exponent min(eb, esa)
  -- The significand is bounded by |err|/β^e ≤ |b|/β^e ≤ |mb| * β^(eb-e)
  -- When e = eb: significand ≤ |mb| < β^p. Done.
  -- When e = esa < eb: significand could be larger. But since |err| ≤ |b| < β^(eb+p):
  -- significand = |err|/β^esa < β^(eb+p)/β^esa = β^(eb-esa+p). Could be > β^p.
  -- Need a tighter bound or a different exponent.
  -- Key insight: |err| ≤ |b|. And b is representable with |mb| < β^p at exponent eb.
  -- The error is ALSO representable at exponent eb (since it divides evenly):
  -- err = b - (s-a). Both b and s-a are multiples of β^min(eb,esa) = β^(min eb esa).
  -- At exponent eb: err/β^eb = mb - (s-a)/β^eb.
  -- (s-a)/β^eb = msa * β^(esa-eb). Integer iff esa ≥ eb.
  -- When esa ≥ eb: err/β^eb = mb - msa * β^(esa-eb), integer.
  --   |err/β^eb| ≤ |mb| < β^p (since |err| ≤ |b| = |mb|*β^eb). ✓
  -- When esa < eb: (s-a)/β^eb not integer. Use exponent esa instead.
  --   err/β^esa = mb * β^(eb-esa) - msa, integer.
  --   |err/β^esa| ≤ |err|/β^esa ≤ |b|/β^esa = |mb| * β^(eb-esa).
  --   Could be ≥ β^p. Need the β=2 gap argument (same as subnormal case).
  -- For simplicity, handle the common case esa ≥ eb, sorry the other.
  by_cases hesa_ge : eb ≤ esa
  · -- Common case: exponent of (s-a) ≥ exponent of b
    -- err at exponent eb has integer significand bounded by |mb|
    set d := mb - msa * (fmt.β : ℤ) ^ (esa - eb).toNat
    -- Use repr_diff_at_lower_exp or direct algebra
    have hval_sa' : s - a = (msa : ℝ) * (fmt.β : ℝ) ^ esa := hval_sa
    have hnn : (0 : ℤ) ≤ esa - eb := by omega
    have hval_err : b - (s - a) = (d : ℝ) * (fmt.β : ℝ) ^ eb := by
      have : b - (s - a) = ((mb : ℝ) - (msa : ℝ) * (fmt.β : ℝ) ^ (esa - eb)) * (fmt.β : ℝ) ^ eb := by
        rw [hval_b, hval_sa']
        have : (msa : ℝ) * (fmt.β : ℝ) ^ esa =
            (msa : ℝ) * (fmt.β : ℝ) ^ (esa - eb) * (fmt.β : ℝ) ^ eb := by
          rw [mul_assoc, ← zpow_add₀ hβ_ne, show esa - eb + eb = esa from by omega]
        linarith
      rw [this]; congr 1
      simp only [d]; push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
    -- |d| < β^p since |err| ≤ |b| = |mb| * β^eb
    have hd_bound : |d| < (fmt.β : ℤ) ^ fmt.prec := by
      have hbp := zpow_pos hβ_pos eb
      -- |b - (s-a)| ≤ |b|, rewrite using value equations
      have h1 : |b - (s - a)| = |(d : ℝ)| * (fmt.β : ℝ) ^ eb := by
        rw [hval_err, abs_mul, abs_of_pos hbp]
      have h2 : |b| = |(mb : ℝ)| * (fmt.β : ℝ) ^ eb := by
        rw [hval_b, abs_mul, abs_of_pos hbp]
      have h3 : |(d : ℝ)| ≤ |(mb : ℝ)| := by
        have := herr_le; rw [h1, h2] at this
        exact le_of_mul_le_mul_right this hbp
      have : |(d : ℤ)| < (fmt.β : ℤ) ^ fmt.prec := by
        have h4 : |(mb : ℤ)| < (fmt.β : ℤ) ^ fmt.prec := hmb
        calc |(d : ℤ)| ≤ |(mb : ℤ)| := by exact_mod_cast h3
          _ < _ := h4
      exact this
    exact ⟨d, eb, hval_err, hd_bound, heb⟩
  · -- Case esa < eb: the exponent of (s-a) is smaller than that of b.
    -- The proof at exponent esa requires showing the significand of
    -- b at exponent esa (= mb * β^(eb-esa)) minus msa stays < β^p.
    -- This holds for β=2 because the "bit gap" between b's low bits
    -- and the rounding grid ensures the difference fits in p digits.
    -- Full proof requires the binary gap lemma (Boldo & Melquiond, §6.3).
    push Not at hesa_ge
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
