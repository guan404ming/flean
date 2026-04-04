import Flean.Core.DirectedRound

/-!
# Flean.Core.NearestRound

Properties of nearest rounding modes: roundNNE (ties to even) and roundNNA (ties away),
plus ordering relationships between all rounding modes.
-/

namespace Flean

/-! ## roundNNE properties -/

theorem roundNNE_zero (fmt : FloatFormat) : roundNNE fmt 0 = 0 := by
  unfold roundNNE; dsimp only; rw [zero_div]
  show (roundNearestEven 0 : ℝ) * _ = 0
  rw [show roundNearestEven (0 : ℝ) = 0 from by unfold roundNearestEven; simp [Int.floor_zero]]
  simp

theorem roundNNE_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundNNE fmt x) :=
  roundGeneric_isRepresentable zrndNNE.toZrndFn fmt x

theorem roundNNE_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundNNE fmt x = x :=
  roundGeneric_repr_fixed zrndNNE.toZrndFn fmt hx

theorem roundNNE_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundNNE fmt (roundNNE fmt x) = roundNNE fmt x :=
  roundGeneric_idempotent zrndNNE.toZrndFn fmt x

/-! ## roundNNE sandwich: roundDN ≤ roundNNE ≤ roundUP -/

private theorem roundNearestEven_ge_floor (x : ℝ) : ⌊x⌋ ≤ roundNearestEven x := by
  unfold roundNearestEven; dsimp only; split_ifs <;> linarith

private theorem roundNearestEven_le_ceil (x : ℝ) : roundNearestEven x ≤ ⌈x⌉ := by
  have hge := roundNearestEven_ge_floor x
  have habs := roundNearestEven_sub_abs x
  by_cases hint : (x : ℝ) = ⌊x⌋
  · rw [hint, roundNearestEven_intCast, Int.ceil_intCast]
  · have hceil : ⌈x⌉ = ⌊x⌋ + 1 := by
      have : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun h => hint h.symm)
      have h1 := Int.ceil_le.mpr (show x ≤ ↑(⌊x⌋ + 1) from by push_cast; linarith [Int.lt_floor_add_one x])
      have h2 : ⌊x⌋ < ⌈x⌉ := Int.lt_ceil.mpr (by exact_mod_cast this)
      linarith
    have : roundNearestEven x ≤ ⌊x⌋ + 1 := by
      unfold roundNearestEven; dsimp only; split_ifs <;> linarith
    linarith

theorem roundNNE_ge_roundDN (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundNNE fmt x := by
  unfold roundNNE roundDN; dsimp only
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast roundNearestEven_ge_floor _

theorem roundNNE_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundNNE fmt x ≤ roundUP fmt x := by
  unfold roundNNE roundUP; dsimp only
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast roundNearestEven_le_ceil _

/-! ## roundNNE monotonicity -/

theorem roundNNE_monotone (fmt : FloatFormat) : Monotone (roundNNE fmt) :=
  roundGeneric_monotone zrndNNE.toZrndFn fmt

/-! ## roundNNE sign preservation -/

private theorem roundNearestEven_neg (x : ℝ) : roundNearestEven (-x) = -roundNearestEven x := by
  unfold roundNearestEven; dsimp only
  set f := ⌊x⌋; set r := x - (f : ℝ)
  have hr_nn := frac_nonneg x; have hr_lt := frac_lt_one x
  rw [Int.floor_neg]
  by_cases hr0 : r = 0
  · -- x is integer
    have hx_int : x = (f : ℝ) := by linarith
    have hx_eq : x = (f : ℝ) := hx_int
    simp only [hx_eq, Int.ceil_intCast, sub_self, Int.cast_neg]
    split_ifs <;> (try omega) <;> linarith
  · -- x not integer: ⌈x⌉ = f + 1
    have hr_pos : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr0)
    have hceil : ⌈x⌉ = f + 1 := by
      apply le_antisymm
      · exact Int.ceil_le.mpr (by push_cast; linarith)
      · exact Int.lt_ceil.mpr (by linarith)
    rw [hceil]
    have hrn : -x - (↑(-(f + 1)) : ℝ) = 1 - r := by push_cast; linarith
    rw [hrn]
    -- Case split on r vs 1/2
    by_cases h1 : r < 1/2 <;> by_cases h2 : r > 1/2 <;>
      by_cases h3 : (1 : ℝ) - r < 1/2 <;> by_cases h4 : (1 : ℝ) - r > 1/2
    all_goals simp only [h1, h2, h3, h4, ite_true, ite_false]
    -- Close: impossible cases, direct cases, or tie-break
    all_goals first
      | omega
      | (exfalso; linarith)
      | (split_ifs <;> omega)
      | (simp only [BEq.beq, decide_eq_true_eq] at *; split_ifs <;> omega)

theorem roundNNE_neg (fmt : FloatFormat) (x : ℝ) : roundNNE fmt (-x) = -roundNNE fmt x := by
  unfold roundNNE; dsimp only
  rw [cexp_neg, neg_div, roundNearestEven_neg, Int.cast_neg, neg_mul]

/-! ## roundNNE error bound -/

theorem roundNNE_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt x| ≤ bpow fmt (cexp fmt x) / 2 := by
  have := roundGenericNearest_sub_abs_le zrndNNE fmt x; rwa [abs_sub_comm]

theorem roundNNE_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNE fmt x| ≤ machineEpsilon fmt / 2 * |x| := by
  have h1 := roundNNE_sub_abs_le fmt x
  have h2 := bpow_cexp_le_machineEpsilon_mul_abs fmt hx
  linarith

/-! ## roundNNA properties -/

theorem roundNNA_zero (fmt : FloatFormat) : roundNNA fmt 0 = 0 := by
  unfold roundNNA; dsimp only; rw [zero_div]
  show (roundNearestAway 0 : ℝ) * _ = 0
  rw [show roundNearestAway (0 : ℝ) = 0 from by unfold roundNearestAway; simp; norm_num]
  simp

theorem roundNNA_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundNNA fmt x) :=
  roundGeneric_isRepresentable zrndNNA.toZrndFn fmt x

theorem roundNNA_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundNNA fmt x = x :=
  roundGeneric_repr_fixed zrndNNA.toZrndFn fmt hx

theorem roundNNA_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundNNA fmt (roundNNA fmt x) = roundNNA fmt x :=
  roundGeneric_idempotent zrndNNA.toZrndFn fmt x

/-! ## roundNNA error bound -/

theorem roundNNA_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNA fmt x| ≤ bpow fmt (cexp fmt x) / 2 := by
  have := roundGenericNearest_sub_abs_le zrndNNA fmt x; rwa [abs_sub_comm]

theorem roundNNA_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNA fmt x| ≤ machineEpsilon fmt / 2 * |x| := by
  have h1 := roundNNA_sub_abs_le fmt x
  have h2 := bpow_cexp_le_machineEpsilon_mul_abs fmt hx
  linarith

/-! ## roundNNA sign preservation -/

private theorem roundNearestAway_neg (x : ℝ) : roundNearestAway (-x) = -roundNearestAway x := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · by_cases hx0 : x = 0
    · subst hx0; simp; norm_num
    · have hx_pos : x > 0 := lt_of_le_of_ne hx (Ne.symm hx0)
      simp only [hx, show ¬(-x ≥ 0) from by linarith, ite_true, ite_false]
      rw [show -x - 1/2 = -(x + 1/2) from by ring, Int.ceil_neg]
  · push Not at hx
    simp only [show ¬(x ≥ 0) from by linarith, show -x ≥ 0 from by linarith, ite_true, ite_false]
    rw [show -x + 1/2 = -(x - 1/2) from by ring, Int.floor_neg]

theorem roundNNA_neg (fmt : FloatFormat) (x : ℝ) : roundNNA fmt (-x) = -roundNNA fmt x := by
  unfold roundNNA; dsimp only
  rw [cexp_neg, neg_div, roundNearestAway_neg, Int.cast_neg, neg_mul]

/-! ## roundNNA sandwich: roundDN ≤ roundNNA ≤ roundUP -/

private theorem roundNearestAway_ge_floor (x : ℝ) : ⌊x⌋ ≤ roundNearestAway x := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · simp only [hx, ite_true]; exact Int.floor_le_floor (by linarith : x ≤ x + 1/2)
  · simp only [hx, ite_false]
    have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h2 : x - 1/2 ≤ (⌈x - 1/2⌉ : ℝ) := Int.le_ceil _
    have : (⌊x⌋ : ℝ) < (⌈x - 1/2⌉ : ℝ) + 1 := by linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)

private theorem roundNearestAway_le_ceil (x : ℝ) : roundNearestAway x ≤ ⌈x⌉ := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · simp only [hx, ite_true]
    have h1 : (⌊x + 1/2⌋ : ℝ) ≤ x + 1/2 := Int.floor_le _
    have h2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil _
    have : (⌊x + 1/2⌋ : ℝ) < (⌈x⌉ : ℝ) + 1 := by linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
  · simp only [hx, ite_false]; exact Int.ceil_le_ceil (by linarith : x - 1/2 ≤ x)

theorem roundNNA_ge_roundDN (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundNNA fmt x := by
  unfold roundNNA roundDN; dsimp only
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast roundNearestAway_ge_floor _

theorem roundNNA_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundNNA fmt x ≤ roundUP fmt x := by
  unfold roundNNA roundUP; dsimp only
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast roundNearestAway_le_ceil _

/-! ## roundNNA monotonicity -/

theorem roundNNA_monotone (fmt : FloatFormat) : Monotone (roundNNA fmt) :=
  roundGeneric_monotone zrndNNA.toZrndFn fmt

/-! ## RoundingFn instances -/

noncomputable def roundNearestEvenFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundNNE fmt
  rounds_to_repr := roundNNE_isRepresentable fmt
  idempotent := roundNNE_idempotent fmt
  monotone := roundNNE_monotone fmt

noncomputable def roundNearestAwayFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundNNA fmt
  rounds_to_repr := roundNNA_isRepresentable fmt
  idempotent := roundNNA_idempotent fmt
  monotone := roundNNA_monotone fmt

/-! ## Ordering relationships between all rounding modes -/

theorem roundDN_le_roundNNE_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundNNE fmt x ∧ roundNNE fmt x ≤ roundUP fmt x :=
  ⟨roundNNE_ge_roundDN fmt x, roundNNE_le_roundUP fmt x⟩

theorem roundDN_le_roundTZ_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    roundDN fmt x ≤ roundTZ fmt x :=
  (roundDN_eq_roundTZ_nonneg fmt hx).le

theorem roundTZ_le_roundUP_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    roundTZ fmt x ≤ roundUP fmt x := by
  rw [← roundDN_eq_roundTZ_nonneg fmt hx]
  exact le_trans (roundDN_le fmt x) (roundUP_ge fmt x)

theorem roundDN_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundUP fmt x :=
  le_trans (roundDN_le fmt x) (roundUP_ge fmt x)

theorem roundDN_le_roundNNA_le_roundUP (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundNNA fmt x ∧ roundNNA fmt x ≤ roundUP fmt x :=
  ⟨roundNNA_ge_roundDN fmt x, roundNNA_le_roundUP fmt x⟩

end Flean
