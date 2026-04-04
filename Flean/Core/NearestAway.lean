import Flean.Core.NearestEven

/-!
# Flean.Core.NearestAway

Properties of roundNNA (round to nearest, ties away from zero).
-/

namespace Flean

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

/-! ## Error bound -/

theorem roundNNA_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNA fmt x| ≤ bpow fmt (cexp fmt x) / 2 := by
  unfold roundNNA; dsimp only; set e := cexp fmt x
  have hb := bpow_pos fmt e
  have hsub := roundNearestAway_sub_abs (x / bpow fmt e)
  have key : |x - (roundNearestAway (x / bpow fmt e) : ℝ) * bpow fmt e|
      = |x / bpow fmt e - (roundNearestAway (x / bpow fmt e) : ℝ)| * bpow fmt e := by
    rw [show |x / bpow fmt e - ↑(roundNearestAway (x / bpow fmt e))| * bpow fmt e
        = |(x / bpow fmt e - ↑(roundNearestAway (x / bpow fmt e))) * bpow fmt e| from by
      rw [abs_mul, abs_of_pos hb]]
    congr 1; rw [sub_mul, div_mul_cancel₀ _ (bpow_ne_zero fmt e)]
  linarith [mul_le_mul_of_nonneg_right hsub hb.le]

theorem roundNNA_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNA fmt x| ≤ machineEpsilon fmt / 2 * |x| := by
  have h1 := roundNNA_sub_abs_le fmt x
  have h2 := bpow_cexp_le_machineEpsilon_mul_abs fmt hx
  linarith

/-! ## Sign preservation -/

private theorem roundNearestAway_neg (x : ℝ) : roundNearestAway (-x) = -roundNearestAway x := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · by_cases hx0 : x = 0
    · subst hx0; simp; norm_num
    · -- x > 0: -x < 0, so LHS uses ceil branch, RHS uses floor branch
      have hx_pos : x > 0 := lt_of_le_of_ne hx (Ne.symm hx0)
      simp only [hx, show ¬(-x ≥ 0) from by linarith, ite_true, ite_false]
      -- ⌈-x - 1/2⌉ = -⌊x + 1/2⌋ (since ⌈-t⌉ = -⌊t⌋)
      rw [show -x - 1/2 = -(x + 1/2) from by ring, Int.ceil_neg]
  · -- x < 0: -x > 0, LHS uses floor branch, RHS uses ceil branch
    push Not at hx
    simp only [show ¬(x ≥ 0) from by linarith, show -x ≥ 0 from by linarith, ite_true, ite_false]
    rw [show -x + 1/2 = -(x - 1/2) from by ring, Int.floor_neg]

theorem roundNNA_neg (fmt : FloatFormat) (x : ℝ) : roundNNA fmt (-x) = -roundNNA fmt x := by
  unfold roundNNA; dsimp only
  rw [cexp_neg, neg_div, roundNearestAway_neg, Int.cast_neg, neg_mul]

/-! ## Sandwich: roundDN ≤ roundNNA ≤ roundUP -/

private theorem roundNearestAway_ge_floor (x : ℝ) : ⌊x⌋ ≤ roundNearestAway x := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · simp only [hx, ite_true]; exact Int.floor_le_floor (by linarith : x ≤ x + 1/2)
  · simp only [hx, ite_false]
    -- ⌊x⌋ ≤ ⌈x - 1/2⌉: both integers, (⌊x⌋ : ℝ) ≤ (⌈x - 1/2⌉ : ℝ) + 1/2
    have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h2 : x - 1/2 ≤ (⌈x - 1/2⌉ : ℝ) := Int.le_ceil _
    -- ⌊x⌋ ≤ ⌈x-1/2⌉ + 1/2 (as reals), both integers, so ⌊x⌋ ≤ ⌈x-1/2⌉
    have : (⌊x⌋ : ℝ) < (⌈x - 1/2⌉ : ℝ) + 1 := by linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)

private theorem roundNearestAway_le_ceil (x : ℝ) : roundNearestAway x ≤ ⌈x⌉ := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · simp only [hx, ite_true]
    -- ⌊x + 1/2⌋ ≤ ⌈x⌉: since x + 1/2 < ⌊x⌋ + 3/2 ≤ ⌈x⌉ + 1 (roughly)
    -- More directly: ⌊x + 1/2⌋ ≤ x + 1/2 and ⌈x⌉ ≥ x, so ⌊x + 1/2⌋ ≤ x + 1/2 < ⌈x⌉ + 1
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

/-! ## Monotonicity -/

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

end Flean
