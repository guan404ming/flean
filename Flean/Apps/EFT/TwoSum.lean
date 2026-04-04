import Flean.Core.NearestRound
import Flean.Core.DoubleRoundNNE
import Flean.Core.ULP
import Flean.Core.Sterbenz

/-!
# Flean.Apps.EFT.TwoSum

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
    (ha : isRepresentable fmt a) (_hb : isRepresentable fmt b)
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
  have hβ_pos : (0 : ℝ) < (fmt.β : ℝ) := by rw [hβ]; norm_num
  have hβ_ne : (fmt.β : ℝ) ≠ 0 := ne_of_gt hβ_pos
  by_cases hesa_ge : eb ≤ esa
  · -- Common case: exponent of (s-a) ≥ exponent of b
    -- err at exponent eb has integer significand bounded by |mb|
    set d := mb - msa * (fmt.β : ℤ) ^ (esa - eb).toNat
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
  · -- Case esa < eb: express error at min(ea, eb) using a, b, s representations.
    -- Use ulp bound when ea ≤ eb, |err| ≤ |b| bound when eb ≤ ea.
    push Not at hesa_ge
    -- Get representation of a
    obtain ⟨ma, ea, hval_a, hma_bd, hea_ge⟩ := ha
    -- Get representation of s
    have hs_repr := roundNNE_isRepresentable fmt (a + b)
    obtain ⟨ms, es, hval_s, hms_bd, hes_ge⟩ := hs_repr
    -- e0 = min ea eb
    set e0 := min ea eb with he0_def
    have he0_ea : e0 ≤ ea := min_le_left ea eb
    have he0_eb : e0 ≤ eb := min_le_right ea eb
    have he0_emin : fmt.emin ≤ e0 := le_min hea_ge heb
    set ec := cexp fmt (a + b) with hec_def
    -- Show a+b is a multiple of bpow(e0)
    have hab_mul : ∃ (k : ℤ), a + b = (k : ℝ) * (fmt.β : ℝ) ^ e0 := by
      refine ⟨ma * (fmt.β : ℤ) ^ (ea - e0).toNat + mb * (fmt.β : ℤ) ^ (eb - e0).toNat, ?_⟩
      rw [hval_a, hval_b]; push_cast; rw [add_mul]
      congr 1 <;> rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hβ_ne]
      · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ea - e0 from Int.sub_nonneg.mpr he0_ea),
            show ea - e0 + e0 = ea from Int.sub_add_cancel ea e0]
      · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ eb - e0 from Int.sub_nonneg.mpr he0_eb),
            show eb - e0 + e0 = eb from Int.sub_add_cancel eb e0]
    -- Handle two cases: ec ≥ e0 (main) vs ec < e0 (err = 0)
    by_cases hec_ge : e0 ≤ ec
    · -- Main case: s is a multiple of bpow(e0), so err is too.
      -- s is an integer multiple of bpow(ec), and ec ≥ e0, so s is a multiple of bpow(e0)
      have hs_mul : ∃ (k : ℤ), s = (k : ℝ) * (fmt.β : ℝ) ^ e0 := by
        -- s = roundNearestEven((a+b)/bpow(ec)) * bpow(ec) = n * bpow(ec)
        -- Since ec ≥ e0: s = n * β^(ec-e0) * bpow(e0)
        set n := roundNearestEven ((a + b) / bpow fmt ec)
        have hs_eq : s = (n : ℝ) * bpow fmt ec := by
          show roundNNE fmt (a + b) = _; unfold roundNNE; rfl
        refine ⟨n * (fmt.β : ℤ) ^ (ec - e0).toNat, ?_⟩
        rw [hs_eq]; unfold bpow; push_cast
        rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hβ_ne,
          Int.toNat_of_nonneg (show (0 : ℤ) ≤ ec - e0 from Int.sub_nonneg.mpr hec_ge),
          show ec - e0 + e0 = ec from Int.sub_add_cancel ec e0]
      -- err = j * bpow(e0)
      obtain ⟨ka, hka⟩ := hab_mul
      obtain ⟨ks, hks⟩ := hs_mul
      set j := ka - ks with hj_def
      have hval_err : b - (s - a) = (j : ℝ) * (fmt.β : ℝ) ^ e0 := by
        rw [herr_eq, hka, hks]; simp only [hj_def]; push_cast; ring
      -- Bound |j| < β^p by case split on ea vs eb
      have hj_bound : |j| < (fmt.β : ℤ) ^ fmt.prec := by
        have hbp_e0 := zpow_pos hβ_pos e0
        by_cases hea_le_eb : ea ≤ eb
        · -- ea ≤ eb, so e0 = ea. Use ulp bound: |err| ≤ bpow(ec)/2.
          have he0_eq : e0 = ea := by rw [he0_def]; exact min_eq_left hea_le_eb
          -- |err| ≤ bpow(ec)/2
          have hulp := roundNNE_sub_abs_le fmt (a + b)
          rw [show a + b - roundNNE fmt (a + b) = b - (s - a) from by ring] at hulp
          rw [hval_err, abs_mul, abs_of_pos hbp_e0] at hulp
          -- cexp(a+b) ≤ ea + 1
          have hec_le : ec ≤ ea + 1 := by
            by_cases hab_zero : a + b = 0
            · show cexp fmt (a + b) ≤ ea + 1; rw [hab_zero, cexp_zero]; omega
            · have hab_le : |a + b| ≤ 2 * |a| := by
                calc |a + b| ≤ |a| + |b| := abs_add_le a b
                  _ ≤ |a| + |a| := by linarith [hab]
                  _ = 2 * |a| := by ring
              have ha_bd : |a| < (fmt.β : ℝ) ^ (ea + ↑fmt.prec) := by
                rw [hval_a, abs_mul, abs_of_pos (zpow_pos hβ_pos ea)]
                calc |(ma : ℝ)| * (fmt.β : ℝ) ^ ea
                    < (fmt.β : ℝ) ^ fmt.prec * (fmt.β : ℝ) ^ ea :=
                    mul_lt_mul_of_pos_right (by exact_mod_cast hma_bd) (zpow_pos hβ_pos ea)
                  _ = _ := by rw [← zpow_natCast, ← zpow_add₀ hβ_ne]; congr 1; ring
              show cexp fmt (a + b) ≤ ea + 1
              unfold cexp
              split
              · omega -- a + b = 0 case
              · rename_i hab_ne
                apply max_le (by omega)
                have hlogβ : 0 < Real.log (fmt.β : ℝ) := Real.log_pos fmt.β_one_lt
                have hab_le2 : |a + b| ≤ 2 * |a| := by
                  calc |a + b| ≤ |a| + |b| := abs_add_le a b
                    _ ≤ |a| + |a| := by linarith [hab]
                    _ = 2 * |a| := by ring
                have ha_bd2 : |a| < (fmt.β : ℝ) ^ (ea + ↑fmt.prec) := by
                  rw [hval_a, abs_mul, abs_of_pos (zpow_pos hβ_pos ea)]
                  calc |(ma : ℝ)| * (fmt.β : ℝ) ^ ea
                      < (fmt.β : ℝ) ^ fmt.prec * (fmt.β : ℝ) ^ ea :=
                      mul_lt_mul_of_pos_right (by exact_mod_cast hma_bd) (zpow_pos hβ_pos ea)
                    _ = _ := by rw [← zpow_natCast, ← zpow_add₀ hβ_ne]; congr 1; ring
                have hab_bd : |a + b| < (fmt.β : ℝ) ^ (ea + (↑fmt.prec : ℤ) + 1) := by
                  calc |a + b| ≤ 2 * |a| := hab_le2
                    _ < 2 * (fmt.β : ℝ) ^ (ea + ↑fmt.prec) := by linarith
                    _ ≤ (fmt.β : ℝ) * (fmt.β : ℝ) ^ (ea + ↑fmt.prec) := by
                      exact mul_le_mul_of_nonneg_right (by rw [hβ]; push_cast; linarith) (by positivity)
                    _ = (fmt.β : ℝ) ^ (ea + ↑fmt.prec + 1) := by
                      rw [mul_comm, ← zpow_add_one₀ hβ_ne]
                have hlog_bd : Real.log |a + b| < (ea + (↑fmt.prec : ℤ) + 1) * Real.log (fmt.β : ℝ) := by
                  calc Real.log |a + b| < Real.log ((fmt.β : ℝ) ^ (ea + (↑fmt.prec : ℤ) + 1)) :=
                    Real.log_lt_log (abs_pos.mpr hab_ne) hab_bd
                    _ = (ea + ↑fmt.prec + 1) * Real.log (fmt.β : ℝ) :=
                        by rw [Real.log_zpow]; push_cast; ring
                have : Real.log |a + b| / Real.log (fmt.β : ℝ) < ea + (↑fmt.prec : ℤ) + 1 := by
                  rwa [div_lt_iff₀ hlogβ]
                have hfl := Int.floor_le (Real.log |a + b| / Real.log (fmt.β : ℝ))
                have hfloor_lt : (⌊Real.log |a + b| / Real.log (fmt.β : ℝ)⌋ : ℝ) < ea + ↑fmt.prec + 1 := by
                  have := this; push_cast at this ⊢; linarith
                have : ⌊Real.log |a + b| / Real.log (fmt.β : ℝ)⌋ < ea + ↑fmt.prec + 1 := by
                  exact_mod_cast hfloor_lt
                omega
          -- |j| * β^ea ≤ β^ec / 2 ≤ β^(ea+1) / 2 = β^ea (for β=2)
          -- So |j| ≤ 1 < β^p
          have hj_le_one : |(j : ℝ)| ≤ 1 := by
            rw [he0_eq] at hulp
            have hbp_ea := zpow_pos hβ_pos ea
            have hec_bpow : (fmt.β : ℝ) ^ ec ≤ (fmt.β : ℝ) ^ (ea + 1) :=
              zpow_le_zpow_right₀ (by have := fmt.β_one_lt; exact_mod_cast this.le : (1 : ℝ) ≤ fmt.β) hec_le
            have : |(j : ℝ)| * (fmt.β : ℝ) ^ ea ≤ (fmt.β : ℝ) ^ (ea + 1) / 2 := by
              simp only [bpow] at hulp; linarith
            rw [zpow_add₀ hβ_ne, zpow_one, hβ] at this
            push_cast at this
            nlinarith [zpow_pos (show (0 : ℝ) < 2 from by norm_num) ea]
          have : |(j : ℤ)| ≤ 1 := by exact_mod_cast hj_le_one
          calc |j| ≤ 1 := this
            _ < (fmt.β : ℤ) ^ fmt.prec := by
              have := fmt.hprec; have := fmt.hβ
              exact_mod_cast Nat.one_lt_pow (by omega) (by omega)
        · -- eb < ea, so e0 = eb. Use |err| ≤ |b| bound.
          push Not at hea_le_eb
          have he0_eq : e0 = eb := by rw [he0_def]; exact min_eq_right (le_of_lt hea_le_eb)
          have hbp_eb := zpow_pos hβ_pos eb
          have h1 : |b - (s - a)| = |(j : ℝ)| * (fmt.β : ℝ) ^ e0 := by
            rw [hval_err, abs_mul, abs_of_pos hbp_e0]
          have h2 : |b| = |(mb : ℝ)| * (fmt.β : ℝ) ^ eb := by
            rw [hval_b, abs_mul, abs_of_pos hbp_eb]
          have h3 : |(j : ℝ)| ≤ |(mb : ℝ)| := by
            have := herr_le; rw [h1, h2, he0_eq] at this
            exact le_of_mul_le_mul_right this hbp_eb
          calc |j| ≤ |mb| := by exact_mod_cast h3
            _ < _ := hmb
      exact ⟨j, e0, hval_err, hj_bound, he0_emin⟩
    · -- ec < e0: (a+b)/bpow(ec) is an integer, so round is exact, err = 0
      push Not at hec_ge
      simp only [herr_eq]
      have : s = a + b := by
        -- (a+b)/bpow(ec) is an integer multiple of β^(e0-ec), hence an integer.
        -- So roundNNE is exact.
        change roundNNE fmt (a + b) = a + b
        apply roundNNE_repr_fixed
        obtain ⟨k, hk⟩ := hab_mul
        have hk_bd : |k| < (fmt.β : ℤ) ^ fmt.prec := by
          have hsc := scaled_abs_lt fmt (a + b)
          -- Save cexp value before rewriting a+b
          have hec_ab : cexp fmt (a + b) = ec := hec_def.symm
          rw [hec_ab] at hsc; simp only [bpow] at hsc
          rw [hk] at hsc
          have hpow_e0 := zpow_pos hβ_pos e0
          have hpow_ec := zpow_pos hβ_pos ec
          rw [abs_div, abs_mul, abs_of_pos hpow_e0, abs_of_pos hpow_ec] at hsc
          -- |(k : ℝ)| * β^e0 / β^ec < β^p
          have he0_ec_pos : 0 < e0 - ec := by omega
          have hpow_ge : (1 : ℝ) ≤ (fmt.β : ℝ) ^ (e0 - ec) :=
            one_le_zpow₀ (by rw [hβ]; norm_num) (by omega)
          have : |(k : ℝ)| < (fmt.β : ℝ) ^ fmt.prec := by
            have hdiv : |(k : ℝ)| * (fmt.β : ℝ) ^ e0 / (fmt.β : ℝ) ^ ec =
                |(k : ℝ)| * (fmt.β : ℝ) ^ (e0 - ec) := by
              rw [mul_div_assoc, ← zpow_sub₀ hβ_ne]
            rw [hdiv] at hsc
            calc |(k : ℝ)| ≤ |(k : ℝ)| * (fmt.β : ℝ) ^ (e0 - ec) :=
                  le_mul_of_one_le_right (abs_nonneg _) hpow_ge
              _ < _ := hsc
          exact_mod_cast this
        exact ⟨k, e0, hk, hk_bd, he0_emin⟩
      rw [this, sub_self]
      exact zero_isRepresentable fmt

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
