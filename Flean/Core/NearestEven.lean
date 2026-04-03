import Flean.Core.DirectedRound

/-!
# Flean.Core.NearestEven

Properties of roundNNE (round to nearest, ties to even).
-/

namespace Flean

/-! ## roundNearestEven integer-level properties -/

private theorem frac_nonneg (x : ℝ) : 0 ≤ x - ⌊x⌋ :=
  sub_nonneg.mpr (Int.floor_le x)

private theorem frac_lt_one (x : ℝ) : x - ⌊x⌋ < 1 := by
  linarith [Int.lt_floor_add_one x]

theorem roundNearestEven_intCast (n : ℤ) : roundNearestEven (n : ℝ) = n := by
  unfold roundNearestEven; dsimp only; simp [Int.floor_intCast, sub_self]

/-- roundNearestEven is within 1/2 of its input. -/
theorem roundNearestEven_sub_abs (x : ℝ) :
    |x - (roundNearestEven x : ℝ)| ≤ 1/2 := by
  unfold roundNearestEven; dsimp only
  set f := ⌊x⌋; set r := x - (f : ℝ)
  have hr_nn := frac_nonneg x
  have hr_lt := frac_lt_one x
  show |x - ↑(if r < 1/2 then f else if r > 1/2 then f + 1 else
    if f % 2 == 0 then f else f + 1)| ≤ 1/2
  by_cases h1 : r < 1/2
  · simp only [h1, ite_true]; show |r| ≤ 1/2
    rw [abs_of_nonneg hr_nn]; linarith
  · by_cases h2 : r > 1/2
    · simp only [h1, h2, ite_true, ite_false]; push_cast
      rw [show x - ((f : ℝ) + 1) = r - 1 from by simp [r]; ring]
      rw [abs_of_nonpos (by linarith)]; linarith
    · have hr_eq : r = 1/2 := le_antisymm (by linarith) (by linarith)
      simp only [h1, h2, ite_false]
      split_ifs
      · rw [abs_of_nonneg hr_nn]; linarith
      · push_cast; rw [show x - ((f : ℝ) + 1) = r - 1 from by simp [r]; ring, hr_eq]; norm_num

theorem roundNearestEven_cast_abs_bound (x : ℝ) :
    |(roundNearestEven x : ℝ)| ≤ |x| + 1/2 := by
  have h := roundNearestEven_sub_abs x
  have : |(roundNearestEven x : ℝ)| = |(x - (x - (roundNearestEven x : ℝ)))| := by ring_nf
  rw [this]
  linarith [abs_sub x (x - (roundNearestEven x : ℝ))]

/-! ## roundNNE properties -/

private theorem roundNearestEven_zero : roundNearestEven (0 : ℝ) = 0 := by
  unfold roundNearestEven; simp [Int.floor_zero]

theorem roundNNE_zero (fmt : FloatFormat) : roundNNE fmt 0 = 0 := by
  unfold roundNNE; dsimp only; rw [zero_div, roundNearestEven_zero]; simp

theorem roundNNE_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundNNE fmt x) := by
  unfold roundNNE; dsimp only; set e := cexp fmt x
  set n := roundNearestEven (x / bpow fmt e)
  have hscaled := scaled_abs_lt fmt x
  have hbound := roundNearestEven_cast_abs_bound (x / bpow fmt e)
  -- |n| < β^p + 1/2, so as integer |n| ≤ β^p
  have hn_le : |n| ≤ (fmt.β : ℤ) ^ fmt.prec := by
    have h1 : |(n : ℝ)| < (fmt.β : ℝ) ^ fmt.prec + 1/2 := by linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast show |(n : ℝ)| < ↑((fmt.β : ℤ) ^ fmt.prec + 1) from by push_cast; linarith)
  by_cases hn_lt : |n| < (fmt.β : ℤ) ^ fmt.prec
  · exact ⟨n, e, rfl, hn_lt, cexp_emin_le fmt x⟩
  · -- |n| = β^p, need renormalization
    have hn_eq : |n| = (fmt.β : ℤ) ^ fmt.prec := le_antisymm hn_le (not_lt.mp hn_lt)
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

theorem roundNNE_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundNNE fmt x = x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval, roundNNE_zero]
  · rw [hval]; unfold roundNNE; dsimp only
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e)
    have hce_le : ce ≤ e := cexp_le_of_repr fmt hm_ne hm he
    have ⟨k, hk⟩ : ∃ (k : ℤ), (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (k : ℝ) :=
      ⟨m * (fmt.β : ℤ) ^ (e - ce).toNat, by
        unfold bpow; push_cast; rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
        congr 2; exact (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hk, roundNearestEven_intCast, ← hk, div_mul_cancel₀ _ (bpow_ne_zero fmt ce)]

theorem roundNNE_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundNNE fmt (roundNNE fmt x) = roundNNE fmt x :=
  roundNNE_repr_fixed fmt (roundNNE_isRepresentable fmt x)

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

/-! ## Integer-level monotonicity -/

private theorem roundNearestEven_monotone : Monotone (roundNearestEven : ℝ → ℤ) := by
  intro x y hxy
  have hge_x := roundNearestEven_ge_floor x
  have hle_x := roundNearestEven_le_ceil x
  have hge_y := roundNearestEven_ge_floor y
  have hle_y := roundNearestEven_le_ceil y
  have habs_x := roundNearestEven_sub_abs x
  have habs_y := roundNearestEven_sub_abs y
  -- roundNearestEven x ∈ {⌊x⌋, ⌈x⌉} and same for y
  -- Key: ⌈x⌉ ≤ ⌊y⌋ + 1 (since x ≤ y implies ⌈x⌉ ≤ ⌈y⌉ ≤ ⌊y⌋ + 1)
  -- So roundNearestEven x ≤ ⌈x⌉ ≤ ⌈y⌉ and roundNearestEven y ≥ ⌊y⌋ ≥ ⌊x⌋
  -- We need: roundNearestEven x ≤ roundNearestEven y
  -- Case: ⌊x⌋ < ⌊y⌋. Then roundNearestEven x ≤ ⌈x⌉ ≤ ⌊x⌋ + 1 ≤ ⌊y⌋ ≤ roundNearestEven y
  -- Case: ⌊x⌋ = ⌊y⌋. Then rx ≤ ry, same floor, direct.
  by_cases hf : ⌊x⌋ = ⌊y⌋
  · -- Same floor: x and y have same floor, so rx ≤ ry
    unfold roundNearestEven; dsimp only; rw [← hf]
    set f := ⌊x⌋; set rx := x - f; set ry := y - f
    have hrxy : rx ≤ ry := by simp [rx, ry]; linarith
    by_cases h1 : rx < 1/2 <;> by_cases h2 : ry < 1/2 <;>
      by_cases h3 : rx > 1/2 <;> by_cases h4 : ry > 1/2
    all_goals simp only [h1, h2, h3, h4, ite_true, ite_false]
    all_goals first | linarith | (split_ifs <;> linarith)
  · -- Different floors: ⌊x⌋ < ⌊y⌋, so ⌊x⌋ + 1 ≤ ⌊y⌋
    have hf_lt : ⌊x⌋ + 1 ≤ ⌊y⌋ := Int.add_one_le_of_lt (lt_of_le_of_ne (Int.floor_le_floor hxy) hf)
    -- roundNearestEven x ≤ ⌊x⌋ + 1 (since it's ⌊x⌋ or ⌊x⌋+1)
    have hle1 : roundNearestEven x ≤ ⌊x⌋ + 1 := by
      unfold roundNearestEven; dsimp only; split_ifs <;> linarith
    linarith

/-! ## Monotonicity -/

private theorem roundNNE_monotone_same_cexp (fmt : FloatFormat) {x y : ℝ}
    (hxy : x ≤ y) (hce : cexp fmt x = cexp fmt y) :
    roundNNE fmt x ≤ roundNNE fmt y := by
  unfold roundNNE; dsimp only; rw [hce]
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast roundNearestEven_monotone (div_le_div_of_nonneg_right hxy (bpow_pos fmt _).le)

theorem roundNNE_monotone (fmt : FloatFormat) : Monotone (roundNNE fmt) := by
  intro x y hxy
  by_cases hce : cexp fmt x = cexp fmt y
  · exact roundNNE_monotone_same_cexp fmt hxy hce
  · calc roundNNE fmt x ≤ roundUP fmt x := roundNNE_le_roundUP fmt x
      _ ≤ roundDN fmt y := roundUP_le_roundDN_of_cexp_ne fmt hxy hce
      _ ≤ roundNNE fmt y := roundNNE_ge_roundDN fmt y

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
      · exact Int.lt_ceil.mpr (by push_cast; linarith)
    rw [hceil]
    have hrn : -x - (↑(-(f + 1)) : ℝ) = 1 - r := by push_cast; linarith
    rw [hrn]
    -- Case split on r vs 1/2
    by_cases h1 : r < 1/2 <;> by_cases h2 : r > 1/2 <;>
      by_cases h3 : (1 : ℝ) - r < 1/2 <;> by_cases h4 : (1 : ℝ) - r > 1/2
    all_goals simp only [h1, h2, h3, h4, ite_true, ite_false]
    -- Close: impossible cases, direct cases, or tie-break
    all_goals first
      | (push_cast; omega)
      | (exfalso; linarith)
      | (split_ifs <;> push_cast <;> omega)
      | (simp only [BEq.beq, decide_eq_true_eq] at *; split_ifs <;> omega)

theorem roundNNE_neg (fmt : FloatFormat) (x : ℝ) : roundNNE fmt (-x) = -roundNNE fmt x := by
  unfold roundNNE; dsimp only
  rw [cexp_neg, neg_div, roundNearestEven_neg, Int.cast_neg, neg_mul]

/-! ## Error bound -/

theorem roundNNE_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt x| ≤ bpow fmt (cexp fmt x) / 2 := by
  unfold roundNNE; dsimp only; set e := cexp fmt x
  have hb := bpow_pos fmt e
  have hsub := roundNearestEven_sub_abs (x / bpow fmt e)
  have key : |x - (roundNearestEven (x / bpow fmt e) : ℝ) * bpow fmt e|
      = |x / bpow fmt e - (roundNearestEven (x / bpow fmt e) : ℝ)| * bpow fmt e := by
    rw [show |x / bpow fmt e - ↑(roundNearestEven (x / bpow fmt e))| * bpow fmt e
        = |(x / bpow fmt e - ↑(roundNearestEven (x / bpow fmt e))) * bpow fmt e| from by
      rw [abs_mul, abs_of_pos hb]]
    congr 1; rw [sub_mul, div_mul_cancel₀ _ (bpow_ne_zero fmt e)]
  linarith [mul_le_mul_of_nonneg_right hsub hb.le]

theorem roundNNE_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNE fmt x| ≤ machineEpsilon fmt / 2 * |x| := by
  have h1 := roundNNE_sub_abs_le fmt x
  have h2 := bpow_cexp_le_machineEpsilon_mul_abs fmt hx
  linarith

end Flean
