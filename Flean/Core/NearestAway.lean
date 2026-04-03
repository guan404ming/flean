import Flean.Core.NearestEven

/-!
# Flean.Core.NearestAway

Properties of roundNNA (round to nearest, ties away from zero).
-/

namespace Flean

/-! ## roundNearestAway integer-level properties -/

theorem roundNearestAway_intCast (n : ℤ) : roundNearestAway (n : ℝ) = n := by
  unfold roundNearestAway
  by_cases hn : (n : ℝ) ≥ 0
  · simp only [hn, ite_true]
    have h1 : (n : ℝ) ≤ (n : ℝ) + 1/2 := by linarith
    have h2 : (n : ℝ) + 1/2 < (n : ℝ) + 1 := by linarith
    exact le_antisymm
      (Int.lt_add_one_iff.mp (Int.floor_lt.mpr (by push_cast [Int.cast_add]; linarith)))
      (Int.le_floor.mpr (by linarith))
  · simp only [hn, ite_false]
    exact le_antisymm
      (Int.ceil_le.mpr (by linarith))
      (by have : (n : ℤ) - 1 < ⌈(n : ℝ) - 1/2⌉ := by
            exact_mod_cast lt_of_lt_of_le (by linarith : (n : ℝ) - 1 < (n : ℝ) - 1/2) (Int.le_ceil _)
          omega)

private theorem roundNearestAway_zero : roundNearestAway (0 : ℝ) = 0 := by
  unfold roundNearestAway; simp; norm_num

theorem roundNearestAway_sub_abs (x : ℝ) :
    |x - (roundNearestAway x : ℝ)| ≤ 1/2 := by
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · simp only [hx, ite_true]; set n := ⌊x + 1/2⌋
    have h1 : (n : ℝ) ≤ x + 1/2 := Int.floor_le _
    have h2 : x + 1/2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_le]; constructor <;> linarith
  · push Not at hx; simp only [show ¬(x ≥ 0) from by linarith, ite_false]
    set n := ⌈x - 1/2⌉
    have h1 : x - 1/2 ≤ (n : ℝ) := Int.le_ceil _
    have h2 : (n : ℝ) < x - 1/2 + 1 := Int.ceil_lt_add_one _
    rw [abs_le]; constructor <;> linarith

theorem roundNearestAway_cast_abs_bound (x : ℝ) :
    |(roundNearestAway x : ℝ)| ≤ |x| + 1/2 := by
  have h := roundNearestAway_sub_abs x
  have : |(roundNearestAway x : ℝ)| = |x - (x - (roundNearestAway x : ℝ))| := by ring_nf
  rw [this]; linarith [abs_sub x (x - (roundNearestAway x : ℝ))]

/-! ## roundNNA properties -/

theorem roundNNA_zero (fmt : FloatFormat) : roundNNA fmt 0 = 0 := by
  unfold roundNNA; dsimp only; rw [zero_div, roundNearestAway_zero]; simp

theorem roundNNA_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundNNA fmt x) := by
  unfold roundNNA; dsimp only; set e := cexp fmt x
  set n := roundNearestAway (x / bpow fmt e)
  have hscaled := scaled_abs_lt fmt x
  have hbound := roundNearestAway_cast_abs_bound (x / bpow fmt e)
  have hn_le : |n| ≤ (fmt.β : ℤ) ^ fmt.prec := by
    have h1 : |(n : ℝ)| < (fmt.β : ℝ) ^ fmt.prec + 1/2 := by linarith
    have h2 : |(n : ℝ)| < ((fmt.β : ℤ) ^ fmt.prec + 1 : ℤ) := by push_cast; linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast h2)
  by_cases hn_lt : |n| < (fmt.β : ℤ) ^ fmt.prec
  · exact ⟨n, e, rfl, hn_lt, cexp_emin_le fmt x⟩
  · have hn_eq : |n| = (fmt.β : ℤ) ^ fmt.prec := le_antisymm hn_le (not_lt.mp hn_lt)
    have hp := fmt.hprec; have hβ := fmt.hβ
    cases abs_eq (by positivity : (0 : ℤ) ≤ (fmt.β : ℤ) ^ fmt.prec) |>.mp hn_eq with
    | inl hn_pos =>
      refine ⟨(fmt.β : ℤ) ^ (fmt.prec - 1), e + 1, ?_, ?_, by linarith [cexp_emin_le fmt x]⟩
      · rw [hn_pos]; unfold bpow; push_cast [zpow_natCast]
        conv_lhs => rw [show fmt.prec = (fmt.prec - 1) + 1 from by omega, pow_succ]
        rw [zpow_add₀ (FloatFormat.β_ne_zero fmt), zpow_one]; ring
      · rw [abs_of_nonneg (by positivity)]
        exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)
    | inr hn_neg =>
      refine ⟨-((fmt.β : ℤ) ^ (fmt.prec - 1)), e + 1, ?_, ?_,
              by linarith [cexp_emin_le fmt x]⟩
      · rw [hn_neg]; unfold bpow; push_cast [zpow_natCast]
        conv_lhs => rw [show fmt.prec = (fmt.prec - 1) + 1 from by omega, pow_succ]
        rw [zpow_add₀ (FloatFormat.β_ne_zero fmt), zpow_one]; ring
      · rw [abs_neg, abs_of_nonneg (by positivity)]
        exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)

theorem roundNNA_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundNNA fmt x = x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval, roundNNA_zero]
  · rw [hval]; unfold roundNNA; dsimp only
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e)
    have hce_le : ce ≤ e := cexp_le_of_repr fmt hm_ne hm he
    have ⟨k, hk⟩ : ∃ (k : ℤ), (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (k : ℝ) :=
      ⟨m * (fmt.β : ℤ) ^ (e - ce).toNat, by
        unfold bpow; push_cast; rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
        congr 2; exact (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hk, roundNearestAway_intCast, ← hk, div_mul_cancel₀ _ (bpow_ne_zero fmt ce)]

theorem roundNNA_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundNNA fmt (roundNNA fmt x) = roundNNA fmt x :=
  roundNNA_repr_fixed fmt (roundNNA_isRepresentable fmt x)

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

private theorem roundNearestAway_monotone : Monotone (roundNearestAway : ℝ → ℤ) := by
  intro x y hxy
  unfold roundNearestAway
  by_cases hx : x ≥ 0
  · have hy : y ≥ 0 := le_trans hx hxy
    simp only [hx, hy, ite_true]
    exact Int.floor_le_floor (by linarith)
  · push Not at hx
    by_cases hy : y ≥ 0
    · simp only [show ¬(x ≥ 0) from by linarith, hy, ite_true, ite_false]
      -- ⌈x - 1/2⌉ ≤ 0 ≤ ⌊y + 1/2⌋
      have h1 : ⌈x - 1/2⌉ ≤ 0 := Int.ceil_le.mpr (by exact_mod_cast show x - 1/2 ≤ (0 : ℝ) from by linarith)
      have h2 : 0 ≤ ⌊y + 1/2⌋ := Int.le_floor.mpr (by exact_mod_cast show (0 : ℝ) ≤ y + 1/2 from by linarith)
      linarith
    · push Not at hy
      simp only [show ¬(x ≥ 0) from by linarith, show ¬(y ≥ 0) from by linarith, ite_false]
      exact Int.ceil_le_ceil (by linarith)

private theorem roundNNA_monotone_same_cexp (fmt : FloatFormat) {x y : ℝ}
    (hxy : x ≤ y) (hce : cexp fmt x = cexp fmt y) :
    roundNNA fmt x ≤ roundNNA fmt y := by
  unfold roundNNA; dsimp only; rw [hce]
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast roundNearestAway_monotone (div_le_div_of_nonneg_right hxy (bpow_pos fmt _).le)

theorem roundNNA_monotone (fmt : FloatFormat) : Monotone (roundNNA fmt) := by
  intro x y hxy
  by_cases hce : cexp fmt x = cexp fmt y
  · exact roundNNA_monotone_same_cexp fmt hxy hce
  · calc roundNNA fmt x ≤ roundUP fmt x := roundNNA_le_roundUP fmt x
      _ ≤ roundDN fmt y := roundUP_le_roundDN_of_cexp_ne fmt hxy hce
      _ ≤ roundNNA fmt y := roundNNA_ge_roundDN fmt y

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
