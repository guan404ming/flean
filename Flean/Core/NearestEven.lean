import Flean.Core.DirectedRound

/-!
# Flean.Core.NearestEven

Properties of roundNNE (round to nearest, ties to even).
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

/-! ## Sandwich: roundDN ≤ roundNNE ≤ roundUP -/

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

/-! ## Monotonicity -/

theorem roundNNE_monotone (fmt : FloatFormat) : Monotone (roundNNE fmt) :=
  roundGeneric_monotone zrndNNE.toZrndFn fmt

/-! ## Sign preservation -/

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

/-! ## Error bound -/

theorem roundNNE_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt x| ≤ bpow fmt (cexp fmt x) / 2 := by
  have := roundGenericNearest_sub_abs_le zrndNNE fmt x; rwa [abs_sub_comm]

theorem roundNNE_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNE fmt x| ≤ machineEpsilon fmt / 2 * |x| := by
  have h1 := roundNNE_sub_abs_le fmt x
  have h2 := bpow_cexp_le_machineEpsilon_mul_abs fmt hx
  linarith

end Flean
