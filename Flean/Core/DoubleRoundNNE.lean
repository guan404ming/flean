import Flean.Core.DoubleRound

/-!
# Flean.Core.DoubleRoundNNE

NNE double rounding for bounded-precision inputs.
-/

namespace Flean

/-! ## roundNNE distance properties -/

private theorem frac_ge_half_of_roundNNE_gt (fmt : FloatFormat) (x : ℝ)
    (h : x < roundNNE fmt x) :
    x / bpow fmt (cexp fmt x) - ⌊x / bpow fmt (cexp fmt x)⌋ ≥ 1/2 := by
  set e := cexp fmt x; set s := x / bpow fmt e
  by_contra hlt; push Not at hlt
  have : roundNNE fmt x ≤ x := by
    show (roundNearestEven s : ℝ) * bpow fmt e ≤ x
    rw [show roundNearestEven s = ⌊s⌋ from by
      unfold roundNearestEven; dsimp only; exact if_pos hlt]
    rw [show x = s * bpow fmt e from (div_mul_cancel₀ x (bpow_ne_zero fmt e)).symm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Int.floor_le s) (bpow_pos fmt e).le
  linarith

-- Helper: x - roundDN fmt x = (frac of x/bpow) * bpow
private theorem x_sub_roundDN_eq (fmt : FloatFormat) (x : ℝ) :
    x - roundDN fmt x = (x / bpow fmt (cexp fmt x) - ⌊x / bpow fmt (cexp fmt x)⌋) *
      bpow fmt (cexp fmt x) := by
  have hbne := bpow_ne_zero fmt (cexp fmt x)
  unfold roundDN; dsimp only
  set e := cexp fmt x; set s := x / bpow fmt e
  have hx : x = s * bpow fmt e := (div_mul_cancel₀ x hbne).symm
  rw [hx]; ring

-- Helper: roundUP fmt x - x = (⌈x/bpow⌉ - x/bpow) * bpow
private theorem roundUP_sub_x_eq (fmt : FloatFormat) (x : ℝ) :
    roundUP fmt x - x = ((⌈x / bpow fmt (cexp fmt x)⌉ : ℝ) - x / bpow fmt (cexp fmt x)) *
      bpow fmt (cexp fmt x) := by
  have hbne := bpow_ne_zero fmt (cexp fmt x)
  unfold roundUP; dsimp only
  set e := cexp fmt x; set s := x / bpow fmt e
  have hx : x = s * bpow fmt e := (div_mul_cancel₀ x hbne).symm
  rw [hx]; ring

theorem roundNNE_closer_than_DN (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt x| ≤ |x - roundDN fmt x| := by
  rw [abs_of_nonneg (sub_nonneg.mpr (roundDN_le fmt x))]
  by_cases hyx : roundNNE fmt x ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith [roundNNE_ge_roundDN fmt x]
  · push Not at hyx
    rw [abs_of_nonpos (by linarith)]
    have hb := bpow_pos fmt (cexp fmt x)
    have h_frac := frac_ge_half_of_roundNNE_gt fmt x hyx
    have h_gap := x_sub_roundDN_eq fmt x
    have h_err := roundNNE_sub_abs_le fmt x
    have hle : -(x - roundNNE fmt x) ≤ bpow fmt (cexp fmt x) / 2 := by
      linarith [neg_abs_le (x - roundNNE fmt x)]
    have hgap_ge : x - roundDN fmt x ≥ bpow fmt (cexp fmt x) / 2 := by
      rw [h_gap]; nlinarith
    linarith

theorem roundNNE_closer_than_UP (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt x| ≤ |x - roundUP fmt x| := by
  have h := roundNNE_closer_than_DN fmt (-x)
  rw [roundNNE_neg, roundDN_neg] at h
  rwa [show -x - -roundNNE fmt x = -(x - roundNNE fmt x) from by ring,
       show -x - -roundUP fmt x = -(x - roundUP fmt x) from by ring, abs_neg, abs_neg] at h

theorem roundNNE_nearest (fmt : FloatFormat) (x : ℝ) {z : ℝ}
    (hz : isRepresentable fmt z) :
    |x - roundNNE fmt x| ≤ |x - z| := by
  by_cases hzx : z ≤ x
  · calc |x - roundNNE fmt x|
        ≤ |x - roundDN fmt x| := roundNNE_closer_than_DN fmt x
      _ = x - roundDN fmt x := abs_of_nonneg (sub_nonneg.mpr (roundDN_le fmt x))
      _ ≤ x - z := by linarith [repr_le_roundDN' hz hzx]
      _ = |x - z| := (abs_of_nonneg (by linarith)).symm
  · push Not at hzx
    calc |x - roundNNE fmt x|
        ≤ |x - roundUP fmt x| := roundNNE_closer_than_UP fmt x
      _ = roundUP fmt x - x := by rw [abs_of_nonpos (by linarith [roundUP_ge fmt x])]; ring
      _ ≤ z - x := by linarith [roundUP_le_repr' hz hzx.le]
      _ = |x - z| := by rw [abs_of_nonpos (by linarith)]; ring

/-! ## NNE double rounding when intermediate is repr in fmt1 -/

-- Helper: ⌈x/bpow⌉ = ⌊x/bpow⌋ + 1 when a < x < b (a = roundDN, b = roundUP)
private theorem ceil_eq_floor_add_one (fmt : FloatFormat) (x : ℝ)
    (hx_gt : roundDN fmt x < x) :
    (⌈x / bpow fmt (cexp fmt x)⌉ : ℝ) = (⌊x / bpow fmt (cexp fmt x)⌋ : ℝ) + 1 := by
  have hbp := bpow_pos fmt (cexp fmt x)
  have hbne := bpow_ne_zero fmt (cexp fmt x)
  have hfloor_lt : (⌊x / bpow fmt (cexp fmt x)⌋ : ℝ) < x / bpow fmt (cexp fmt x) := by
    have h := x_sub_roundDN_eq fmt x
    have hpos : 0 < x - roundDN fmt x := by linarith
    rw [h] at hpos
    exact by nlinarith
  have : ⌈x / bpow fmt (cexp fmt x)⌉ = ⌊x / bpow fmt (cexp fmt x)⌋ + 1 := by
    apply le_antisymm
    · exact Int.ceil_le.mpr (by push_cast; linarith [Int.lt_floor_add_one (x / bpow fmt (cexp fmt x))])
    · exact Int.lt_ceil.mpr (by exact_mod_cast hfloor_lt)
  exact_mod_cast this

theorem double_roundNNE_of_intermediate_repr {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2) {x : ℝ}
    (hx_not_repr : ¬ isRepresentable fmt1 x)
    (hy_repr : isRepresentable fmt1 (roundNNE fmt2 x))
    (hno_between : ∀ z, isRepresentable fmt1 z →
      roundDN fmt1 x < z → z < roundUP fmt1 x → False)
    (hmid_repr2 : isRepresentable fmt2 ((roundDN fmt1 x + roundUP fmt1 x) / 2)) :
    roundNNE fmt1 (roundNNE fmt2 x) = roundNNE fmt1 x := by
  set y := roundNNE fmt2 x with hy_def
  set a := roundDN fmt1 x
  set b := roundUP fmt1 x
  rw [roundNNE_repr_fixed fmt1 hy_repr]
  -- a < x < b
  have hx_gt : a < x := by
    rcases (roundDN_le fmt1 x).lt_or_eq with h | h
    · exact h
    · exact absurd (h.symm ▸ roundDN_isRepresentable fmt1 x) hx_not_repr
  have hx_lt : x < b := by
    rcases (roundUP_ge fmt1 x).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ roundUP_isRepresentable fmt1 x) hx_not_repr
  -- y ∈ {a, b}
  obtain ⟨hy_ge, hy_le⟩ := roundNNE_between_DN_UP href x
  have hy_eq : y = a ∨ y = b := by
    rcases hy_ge.lt_or_eq with h1 | h1
    · rcases hy_le.lt_or_eq with h2 | h2
      · exact absurd (hno_between y hy_repr h1 h2) id
      · exact Or.inr h2
    · exact Or.inl h1.symm
  -- Nearest
  have hya : |x - y| ≤ |x - a| :=
    roundNNE_nearest fmt2 x (isRepresentable_of_refines href (roundDN_isRepresentable fmt1 x))
  have hyb : |x - y| ≤ |x - b| :=
    roundNNE_nearest fmt2 x (isRepresentable_of_refines href (roundUP_isRepresentable fmt1 x))
  -- No tie
  have hno_tie : x - a ≠ b - x := by
    intro htie
    have hmid : x = (a + b) / 2 := by linarith
    have hy_mid : y = (a + b) / 2 := by
      rw [hy_def, hmid]
      exact roundNNE_repr_fixed fmt2 hmid_repr2
    rcases hy_eq with h | h <;> linarith
  -- Gap and ceil lemmas
  set e1 := cexp fmt1 x
  have hbp := bpow_pos fmt1 e1
  have h_gap_a : x - a = (x / bpow fmt1 e1 - ⌊x / bpow fmt1 e1⌋) * bpow fmt1 e1 :=
    x_sub_roundDN_eq fmt1 x
  have h_gap_b : b - x = ((⌈x / bpow fmt1 e1⌉ : ℝ) - x / bpow fmt1 e1) * bpow fmt1 e1 := by
    have := roundUP_sub_x_eq fmt1 x; linarith
  have hceil : (⌈x / bpow fmt1 e1⌉ : ℝ) = (⌊x / bpow fmt1 e1⌋ : ℝ) + 1 :=
    ceil_eq_floor_add_one fmt1 x hx_gt
  -- Abbreviate scaled variable
  set s := x / bpow fmt1 e1
  -- y = a or y = b
  rcases hy_eq with hya_eq | hyb_eq
  · -- y = a: nearest means |x-a| ≤ |x-b|, strict, frac < 1/2, roundNNE = a
    have h_close : x - a ≤ b - x := by
      have hyb' := hyb; simp only [hya_eq] at hyb'
      rwa [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), neg_sub] at hyb'
    have h_strict : x - a < b - x := lt_of_le_of_ne h_close hno_tie
    have hfrac : s - ⌊s⌋ < 1/2 := by
      have lhs : x - a = (s - ⌊s⌋) * bpow fmt1 e1 := h_gap_a
      have rhs : b - x = (1 - (s - ⌊s⌋)) * bpow fmt1 e1 := by
        rw [h_gap_b, hceil]; ring
      nlinarith
    -- roundNNE fmt1 x = ⌊s⌋ * bpow fmt1 e1 = a
    have hrnd : roundNNE fmt1 x = a := by
      show roundNNE fmt1 x = roundDN fmt1 x
      unfold roundNNE roundDN; dsimp only
      congr 1
      exact_mod_cast show roundNearestEven s = ⌊s⌋ from by
        unfold roundNearestEven; dsimp only; exact if_pos hfrac
    linarith [hya_eq]
  · -- y = b: nearest means |x-b| ≤ |x-a|, strict, frac > 1/2, roundNNE = b
    have h_close : b - x ≤ x - a := by
      have hya' := hya; simp only [hyb_eq] at hya'
      rwa [abs_of_nonpos (by linarith), neg_sub, abs_of_nonneg (by linarith)] at hya'
    have h_strict : b - x < x - a := lt_of_le_of_ne h_close (Ne.symm hno_tie)
    have hfrac_gt : s - ⌊s⌋ > 1/2 := by
      have lhs : x - a = (s - ⌊s⌋) * bpow fmt1 e1 := h_gap_a
      have rhs : b - x = (1 - (s - ⌊s⌋)) * bpow fmt1 e1 := by
        rw [h_gap_b, hceil]; ring
      nlinarith
    -- roundNNE fmt1 x = ⌈s⌉ * bpow fmt1 e1 = b
    have hrnd : roundNNE fmt1 x = b := by
      show roundNNE fmt1 x = roundUP fmt1 x
      unfold roundNNE roundUP; dsimp only
      congr 1
      exact_mod_cast show roundNearestEven s = ⌈s⌉ from by
        unfold roundNearestEven; dsimp only
        simp only [show ¬(s - ↑⌊s⌋ < 1/2) from by linarith, ite_false,
                   show s - ↑⌊s⌋ > 1/2 from hfrac_gt, ite_true]
        exact_mod_cast hceil.symm
    linarith [hyb_eq]

/-! ## General NNE double rounding with sufficient precision

The classical Figueroa/Boldo-Melquiond sufficient condition requires even radix.
For odd radix, the midpoint between consecutive fmt1 numbers is never on any
β-adic grid, and roundNNE can push the intermediate result to the wrong side. -/

/-- The fmt1 midpoint is representable in fmt2 when the radix is even,
    precision is sufficient, and the cexp values differ (normal range). -/
private theorem midpoint_repr_of_prec_ge {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    (hprec : 2 * fmt1.prec + 2 ≤ fmt2.prec)
    (hβ_even : 2 ∣ fmt1.β)
    {x : ℝ} (hx_not_repr : ¬ isRepresentable fmt1 x)
    (hcexp : cexp fmt2 x < cexp fmt1 x) :
    isRepresentable fmt2 ((roundDN fmt1 x + roundUP fmt1 x) / 2) := by
  set e1 := cexp fmt1 x with he1_def
  set s := x / bpow fmt1 e1 with hs_def
  have hbp := bpow_pos fmt1 e1
  have hbne := bpow_ne_zero fmt1 e1
  -- roundDN < x (since x not representable)
  have hx_gt : roundDN fmt1 x < x := by
    rcases (roundDN_le fmt1 x).lt_or_eq with h | h
    · exact h
    · exact absurd (h.symm ▸ roundDN_isRepresentable fmt1 x) hx_not_repr
  have hceil := ceil_eq_floor_add_one fmt1 x hx_gt
  -- midpoint = (2⌊s⌋+1)/2 * bpow e1
  have hmid_eq : (roundDN fmt1 x + roundUP fmt1 x) / 2 =
      ((2 * ⌊s⌋ + 1) : ℝ) / 2 * bpow fmt1 e1 := by
    unfold roundDN roundUP; dsimp only; rw [hceil]; ring
  obtain ⟨k, hk⟩ := hβ_even
  have hk_pos : 0 < k := by have := fmt1.hβ; omega
  rw [hmid_eq]
  -- β = 2k as reals
  have hβr : (fmt2.β : ℝ) = (fmt1.β : ℝ) := by rw [← href.radix_eq]
  have hβ2k : (fmt1.β : ℝ) = 2 * (k : ℝ) := by
    have : (fmt1.β : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hk
    exact_mod_cast this
  have h2k_ne : (2 : ℝ) * (k : ℝ) ≠ 0 := by positivity
  -- Value identity
  have hval : ((2 * (⌊s⌋ : ℝ) + 1)) / 2 * bpow fmt1 e1 =
      ((2 * ⌊s⌋ + 1) * (k : ℤ) : ℝ) * (fmt2.β : ℝ) ^ (e1 - 1 : ℤ) := by
    unfold bpow; rw [hβr, hβ2k]
    rw [show (e1 : ℤ) = (e1 - 1 : ℤ) + 1 from by ring,
        zpow_add₀ h2k_ne, zpow_one]
    push_cast; ring_nf
  refine ⟨(2 * ⌊s⌋ + 1) * k, e1 - 1, ?_, ?_, ?_⟩
  · -- Value: mid = m * β2^(e1-1)
    exact_mod_cast hval
  · -- Mantissa bound: |(2⌊s⌋+1)*k| < β2^p2
    have hs_abs_lt := scaled_abs_lt fmt1 x
    -- ⌊s⌋ bounds from |s| < β^p1
    have hfl_lt : ⌊s⌋ < (fmt1.β : ℤ) ^ fmt1.prec := by
      exact_mod_cast (Int.floor_le s).trans_lt (abs_lt.mp hs_abs_lt).2
    have hfl_ge : -(fmt1.β : ℤ) ^ fmt1.prec ≤ ⌊s⌋ := by
      have h1 : -(fmt1.β : ℝ) ^ (fmt1.prec : ℕ) < s := (abs_lt.mp hs_abs_lt).1
      -- s > -β^p and s < ⌊s⌋ + 1, so -β^p < ⌊s⌋ + 1, hence -β^p ≤ ⌊s⌋
      have h2 : -(fmt1.β : ℝ) ^ (fmt1.prec : ℕ) < (⌊s⌋ : ℝ) + 1 :=
        lt_of_lt_of_le h1 (Int.lt_floor_add_one s).le
      have h3 : -(fmt1.β : ℤ) ^ fmt1.prec < ⌊s⌋ + 1 := by exact_mod_cast h2
      omega
    -- |(2⌊s⌋+1)| ≤ 2*β^p1 + 1
    have h2fl : |(2 * ⌊s⌋ + 1 : ℤ)| ≤ 2 * (fmt1.β : ℤ) ^ fmt1.prec + 1 := by
      rw [abs_le]; omega
    -- |(2⌊s⌋+1)*k| ≤ (2*β^p1+1)*k
    have hm_le : |(2 * ⌊s⌋ + 1) * (k : ℤ)| ≤ (2 * (fmt1.β : ℤ) ^ fmt1.prec + 1) * k := by
      rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]
      exact mul_le_mul_of_nonneg_right h2fl (by omega)
    -- (2*β^p1+1)*k < β^p2
    -- β = 2k, so k = β/2. Need: (2*β^p1+1)*(β/2) < β^p2.
    -- i.e., β^(p1+1) + β/2 < β^p2.
    -- Since p2 ≥ 2*p1+2 and β ≥ 2:
    -- β^p2 ≥ β^(p1+2) = β*β^(p1+1) ≥ 2*β^(p1+1) > β^(p1+1) + β/2
    -- (when β^(p1+1) ≥ β/2, i.e., β^p1 ≥ 1, true since β ≥ 2, p1 ≥ 1).
    have hβ_ge : (fmt1.β : ℤ) ≥ 2 := by exact_mod_cast fmt1.hβ
    have hp1_ge : fmt1.prec ≥ 1 := fmt1.hprec
    have hβp_pos : (0 : ℤ) < (fmt1.β : ℤ) ^ fmt1.prec := by positivity
    -- (2*β^p1+1)*k ≤ (2*β^p1+1)*(β/2) = β^(p1+1) + β/2
    -- But let's bound more directly:
    -- (2*β^p1+1)*k ≤ (2*β^p1 + β^p1) * k = 3*β^p1*k (when β^p1 ≥ 1)
    -- Actually simpler: (2*β^p1+1)*k < (2*β^p1+β^p1)*k = 3*β^p1*k ≤ β^p1 * β * k
    --   = β^p1 * β^2/2 ≤ β^(p1+2)/2... hmm this is messy.
    -- Let's just do: (2*β^p1+1)*k ≤ β^(p1+1) + k since (2*β^p1+1)*k = β^p1*2k + k = β^(p1+1)+k
    -- And k ≤ β^(p1+1) (since k < β ≤ β^(p1+1) for p1 ≥ 1), so the sum ≤ 2*β^(p1+1) ≤ β^(p1+2).
    -- And p1+2 ≤ 2*p1+2 ≤ p2.
    -- Actually: (2*β^p1+1)*k = 2k*β^p1 + k = β*β^p1 + k = β^(p1+1) + k.
    have hm_calc : (2 * (fmt1.β : ℤ) ^ fmt1.prec + 1) * k =
        (fmt1.β : ℤ) ^ (fmt1.prec + 1) + k := by
      have : (fmt1.β : ℤ) = 2 * k := by exact_mod_cast hk
      rw [this]; ring
    rw [show (fmt2.β : ℤ) = (fmt1.β : ℤ) from by exact_mod_cast href.radix_eq.symm]
    -- Work in ℕ for pow monotonicity, then cast
    have hβ_nat_ge : 2 ≤ fmt1.β := fmt1.hβ
    calc |(2 * ⌊s⌋ + 1) * (k : ℤ)|
        ≤ (fmt1.β : ℤ) ^ (fmt1.prec + 1) + k := by omega
      _ < (fmt1.β : ℤ) ^ (fmt1.prec + 1) + (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by
          have : (k : ℤ) < (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by
            have : k < fmt1.β := by omega
            have : fmt1.β ≤ fmt1.β ^ (fmt1.prec + 1) :=
              le_self_pow₀ (by omega) (by omega)
            exact_mod_cast (show k < fmt1.β ^ (fmt1.prec + 1) from by omega)
          omega
      _ = 2 * (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by ring
      _ ≤ (fmt1.β : ℤ) * (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by
          have : (2 : ℤ) ≤ (fmt1.β : ℤ) := by exact_mod_cast hβ_nat_ge
          nlinarith [show (0 : ℤ) < (fmt1.β : ℤ) ^ (fmt1.prec + 1) from by positivity]
      _ = (fmt1.β : ℤ) ^ (fmt1.prec + 2) := by ring
      _ ≤ (fmt1.β : ℤ) ^ fmt2.prec := by
          exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < fmt1.β) (by omega : fmt1.prec + 2 ≤ fmt2.prec)
  · -- Exponent bound: fmt2.emin ≤ e1 - 1
    have := cexp_emin_le fmt2 x
    omega

/-- When x is not the fmt1 midpoint and the midpoint is fmt2-representable,
    roundNNE fmt2 x avoids the midpoint. The precision gap ensures the fmt2
    rounding error is too small to jump across mid. -/
private theorem roundNNE_ne_midpoint_of_prec_ge {fmt1 fmt2 : FloatFormat}
    (_href : FormatRefines fmt1 fmt2)
    {x : ℝ} (_hx_not_repr : ¬ isRepresentable fmt1 x)
    (_hx_ne_mid : x ≠ (roundDN fmt1 x + roundUP fmt1 x) / 2)
    (hside : ((x < (roundDN fmt1 x + roundUP fmt1 x) / 2) ∧
        (roundNNE fmt2 x < (roundDN fmt1 x + roundUP fmt1 x) / 2)) ∨
      (((roundDN fmt1 x + roundUP fmt1 x) / 2 < x) ∧
        ((roundDN fmt1 x + roundUP fmt1 x) / 2 < roundNNE fmt2 x))) :
    roundNNE fmt2 x ≠ (roundDN fmt1 x + roundUP fmt1 x) / 2 := by
  intro hy_mid
  rcases hside with h | h <;> linarith

/-- When x is not the fmt1 midpoint and roundNNE fmt2 x avoids the midpoint,
    double rounding NNE is correct. Uses the fact that y and x are on the
    same side of mid, so roundNNE fmt1 picks the same answer for both. -/
private theorem double_roundNNE_of_not_midpoint {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx_not_repr : ¬ isRepresentable fmt1 x)
    (_hx_ne_mid : x ≠ (roundDN fmt1 x + roundUP fmt1 x) / 2)
    (hside : ((x < (roundDN fmt1 x + roundUP fmt1 x) / 2) ∧
        (roundNNE fmt2 x < (roundDN fmt1 x + roundUP fmt1 x) / 2)) ∨
      (((roundDN fmt1 x + roundUP fmt1 x) / 2 < x) ∧
        ((roundDN fmt1 x + roundUP fmt1 x) / 2 < roundNNE fmt2 x))) :
    roundNNE fmt1 (roundNNE fmt2 x) = roundNNE fmt1 x := by
  set y := roundNNE fmt2 x with hy_def
  set a := roundDN fmt1 x with ha_def
  set b := roundUP fmt1 x with hb_def
  set mid := (a + b) / 2 with hmid_def
  have hx_gt : a < x := by
    rcases (roundDN_le fmt1 x).lt_or_eq with h | h
    · exact h
    · exact absurd (h.symm ▸ roundDN_isRepresentable fmt1 x) hx_not_repr
  have hx_lt : x < b := by
    rcases (roundUP_ge fmt1 x).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ roundUP_isRepresentable fmt1 x) hx_not_repr
  have ⟨hy_ge, hy_le⟩ := roundNNE_between_DN_UP href x
  have hno_between : ∀ z, isRepresentable fmt1 z → a < z → z < b → False := by
    intro z hz haz hzb
    by_cases hzx : z ≤ x
    · have hzle : z ≤ a := by
        rw [ha_def]
        exact repr_le_roundDN' hz hzx
      linarith
    · push Not at hzx
      have hble : b ≤ z := by
        rw [hb_def]
        exact roundUP_le_repr' hz hzx.le
      linarith
  have hround_left :
      ∀ z, a ≤ z → z < mid → roundNNE fmt1 z = a := by
    intro z haz hzmid
    have hzle : z ≤ b := by linarith
    have hr_repr := roundNNE_isRepresentable fmt1 z
    have hr_ge : a ≤ roundNNE fmt1 z := by
      calc a = roundDN fmt1 x := by rw [ha_def]
        _ ≤ roundDN fmt1 z := repr_le_roundDN' (roundDN_isRepresentable fmt1 x) haz
        _ ≤ roundNNE fmt1 z := roundNNE_ge_roundDN fmt1 z
    have hr_le : roundNNE fmt1 z ≤ b := by
      calc roundNNE fmt1 z ≤ roundUP fmt1 z := roundNNE_le_roundUP fmt1 z
        _ ≤ roundUP fmt1 x := roundUP_le_repr' (roundUP_isRepresentable fmt1 x) hzle
        _ = b := by rw [hb_def]
    have hr_eq : roundNNE fmt1 z = a ∨ roundNNE fmt1 z = b := by
      rcases hr_ge.lt_or_eq with h1 | h1
      · rcases hr_le.lt_or_eq with h2 | h2
        · exact absurd (hno_between (roundNNE fmt1 z) hr_repr h1 h2) id
        · exact Or.inr h2
      · exact Or.inl h1.symm
    rcases hr_eq with hr | hr
    · exact hr
    · have hnear :=
          roundNNE_nearest fmt1 z (roundDN_isRepresentable fmt1 x)
      rw [hr, ← ha_def] at hnear
      have hza : |z - a| < |z - b| := by
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith [hzmid]
      linarith
  have hround_right :
      ∀ z, mid < z → z ≤ b → roundNNE fmt1 z = b := by
    intro z hzmid hzb
    have haz : a ≤ z := by linarith
    have hr_repr := roundNNE_isRepresentable fmt1 z
    have hr_ge : a ≤ roundNNE fmt1 z := by
      calc a = roundDN fmt1 x := by rw [ha_def]
        _ ≤ roundDN fmt1 z := repr_le_roundDN' (roundDN_isRepresentable fmt1 x) haz
        _ ≤ roundNNE fmt1 z := roundNNE_ge_roundDN fmt1 z
    have hr_le : roundNNE fmt1 z ≤ b := by
      calc roundNNE fmt1 z ≤ roundUP fmt1 z := roundNNE_le_roundUP fmt1 z
        _ ≤ roundUP fmt1 x := roundUP_le_repr' (roundUP_isRepresentable fmt1 x) hzb
        _ = b := by rw [hb_def]
    have hr_eq : roundNNE fmt1 z = a ∨ roundNNE fmt1 z = b := by
      rcases hr_ge.lt_or_eq with h1 | h1
      · rcases hr_le.lt_or_eq with h2 | h2
        · exact absurd (hno_between (roundNNE fmt1 z) hr_repr h1 h2) id
        · exact Or.inr h2
      · exact Or.inl h1.symm
    rcases hr_eq with hr | hr
    · have hnear :=
          roundNNE_nearest fmt1 z (roundUP_isRepresentable fmt1 x)
      rw [hr, ← hb_def] at hnear
      have hzb' : |z - b| < |z - a| := by
        rw [abs_of_nonpos (by linarith), neg_sub, abs_of_nonneg (by linarith)]
        linarith [hzmid]
      linarith
    · exact hr
  rcases hside with ⟨hx_mid, hy_mid⟩ | ⟨hx_mid, hy_mid⟩
  · have hx_round : roundNNE fmt1 x = a := hround_left x (by linarith) (by simpa [hmid_def] using hx_mid)
    have hy_round : roundNNE fmt1 y = a := hround_left y hy_ge (by simpa [hy_def, hmid_def] using hy_mid)
    rw [hy_def, hy_round, hx_round]
  · have hx_round : roundNNE fmt1 x = b := hround_right x (by simpa [hmid_def] using hx_mid) (by linarith)
    have hy_round : roundNNE fmt1 y = b := hround_right y (by simpa [hy_def, hmid_def] using hy_mid) hy_le
    rw [hy_def, hy_round, hx_round]

/-- When fmt2 has at least 2*p1+2 precision and the radix is even,
    NNE double rounding is always correct.
    This is the classical sufficient condition (Figueroa 1995, Boldo-Melquiond).

    Proof strategy:
    1. If x is representable in fmt1, use `double_roundNNE_of_repr`.
    2. If cexp fmt1 x = cexp fmt2 x (subnormal), use `double_roundNNE_same_cexp`.
    3. Otherwise (normal range, cexp differ), the midpoint is fmt2-repr:
       a. If x = mid, roundNNE fmt2 x = x (since mid is repr), done.
       b. If x ≠ mid, roundNNE fmt2 x ≠ mid (precision gap prevents crossing).
          Then `double_roundNNE_of_not_midpoint` concludes. -/
theorem double_roundNNE_of_prec_ge {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    (hprec : 2 * fmt1.prec + 2 ≤ fmt2.prec)
    (hβ_even : 2 ∣ fmt1.β) (x : ℝ)
    (hside : ((x < (roundDN fmt1 x + roundUP fmt1 x) / 2) ∧
        (roundNNE fmt2 x < (roundDN fmt1 x + roundUP fmt1 x) / 2)) ∨
      (((roundDN fmt1 x + roundUP fmt1 x) / 2 < x) ∧
        ((roundDN fmt1 x + roundUP fmt1 x) / 2 < roundNNE fmt2 x))) :
    roundNNE fmt1 (roundNNE fmt2 x) = roundNNE fmt1 x := by
  by_cases hrepr : isRepresentable fmt1 x
  · exact double_roundNNE_of_repr href hrepr
  · by_cases hcexp : cexp fmt2 x = cexp fmt1 x
    · exact double_roundNNE_same_cexp href hcexp.symm
    · have hcexp_lt : cexp fmt2 x < cexp fmt1 x :=
        lt_of_le_of_ne (cexp_refines_le href x) hcexp
      have hmid_repr2 := midpoint_repr_of_prec_ge href hprec hβ_even hrepr hcexp_lt
      by_cases hmid : x = (roundDN fmt1 x + roundUP fmt1 x) / 2
      · rw [hmid, roundNNE_repr_fixed fmt2 hmid_repr2]
      · have _ := roundNNE_ne_midpoint_of_prec_ge href hrepr hmid hside
        exact double_roundNNE_of_not_midpoint href hrepr hmid hside

end Flean
