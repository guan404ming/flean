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

end Flean
