import Flean.Core.Rounding
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Flean.Core.RoundProps

Concrete rounding functions and proofs of their properties.
-/

namespace Flean

/-! ## Helper lemmas about the radix β -/

theorem FloatFormat.β_pos (fmt : FloatFormat) : (0 : ℝ) < (fmt.β : ℝ) := by
  have h := fmt.hβ; exact Nat.cast_pos.mpr (by omega)

theorem FloatFormat.β_ne_zero (fmt : FloatFormat) : (fmt.β : ℝ) ≠ 0 :=
  ne_of_gt fmt.β_pos

theorem FloatFormat.β_one_lt (fmt : FloatFormat) : (1 : ℝ) < (fmt.β : ℝ) := by
  have : 1 < fmt.β := by have := fmt.hβ; omega
  exact_mod_cast this

/-! ## Representability lemmas -/

theorem zero_isRepresentable (fmt : FloatFormat) : isRepresentable fmt 0 := by
  refine ⟨0, fmt.emin, by simp, ?_, le_refl _⟩
  simp; exact_mod_cast pow_pos (show 0 < fmt.β from by have := fmt.hβ; omega) fmt.prec

theorem neg_isRepresentable {fmt : FloatFormat} {x : ℝ}
    (hx : isRepresentable fmt x) : isRepresentable fmt (-x) := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  exact ⟨-m, e, by rw [hval]; push_cast; ring, by rwa [abs_neg], he⟩

/-! ## Power of β -/

noncomputable def bpow (fmt : FloatFormat) (e : ℤ) : ℝ :=
  (fmt.β : ℝ) ^ e

theorem bpow_pos (fmt : FloatFormat) (e : ℤ) : 0 < bpow fmt e :=
  zpow_pos fmt.β_pos e

theorem bpow_ne_zero (fmt : FloatFormat) (e : ℤ) : bpow fmt e ≠ 0 :=
  ne_of_gt (bpow_pos fmt e)

/-! ## Truncation toward zero -/

noncomputable def ztrunc (x : ℝ) : ℤ :=
  if x ≥ 0 then ⌊x⌋ else ⌈x⌉

theorem ztrunc_zero : ztrunc 0 = 0 := by
  simp [ztrunc, Int.floor_zero]

theorem ztrunc_cast_abs_le (y : ℝ) : |(ztrunc y : ℝ)| ≤ |y| := by
  unfold ztrunc
  split_ifs with hy
  · have hf_nn : (0 : ℤ) ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy
    rw [abs_of_nonneg (by exact_mod_cast hf_nn : (0 : ℝ) ≤ (⌊y⌋ : ℝ)),
        abs_of_nonneg hy]
    exact Int.floor_le y
  · have hy' : y < 0 := lt_of_not_ge hy
    have hc_np : ⌈y⌉ ≤ 0 := Int.ceil_le.mpr (by exact_mod_cast le_of_lt hy')
    rw [abs_of_nonpos (by exact_mod_cast hc_np : (⌈y⌉ : ℝ) ≤ (0 : ℝ)),
        abs_of_neg hy']
    linarith [Int.le_ceil y]

/-- ztrunc of an integer is itself. -/
theorem ztrunc_intCast (n : ℤ) : ztrunc (n : ℝ) = n := by
  unfold ztrunc
  split_ifs with h
  · exact Int.floor_intCast n
  · exact Int.ceil_intCast n

/-! ## Canonical exponent -/

noncomputable def cexp (fmt : FloatFormat) (x : ℝ) : ℤ :=
  if x = 0 then fmt.emin
  else max fmt.emin (⌊Real.log |x| / Real.log (fmt.β : ℝ)⌋ - (fmt.prec : ℤ) + 1)

theorem cexp_zero (fmt : FloatFormat) : cexp fmt 0 = fmt.emin := by
  simp [cexp]

theorem cexp_emin_le (fmt : FloatFormat) (x : ℝ) : fmt.emin ≤ cexp fmt x := by
  unfold cexp; split
  · exact le_refl _
  · exact le_max_left _ _

/-! ## Round toward zero -/

noncomputable def roundTZ (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e

theorem roundTZ_zero (fmt : FloatFormat) : roundTZ fmt 0 = 0 := by
  simp [roundTZ, cexp_zero, ztrunc_zero, bpow]

/-! ## Key scaling lemma -/

theorem scaled_abs_lt (fmt : FloatFormat) (x : ℝ) :
    |x / bpow fmt (cexp fmt x)| < (fmt.β : ℝ) ^ fmt.prec := by
  by_cases hx : x = 0
  · subst hx; simp [bpow, cexp_zero]; exact pow_pos fmt.β_pos _
  · have hx_pos : 0 < |x| := abs_pos.mpr hx
    have hlogβ : 0 < Real.log (fmt.β : ℝ) := Real.log_pos fmt.β_one_lt
    set e := cexp fmt x with he_def
    -- e ≥ ⌊log_β |x|⌋ - p + 1
    have he_max : e = max fmt.emin (⌊Real.log |x| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) := by
      simp [cexp, hx, he_def]
    have he_ge : ⌊Real.log |x| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1 ≤ e := by
      rw [he_max]; exact le_max_right _ _
    -- log_β |x| < e + p
    have hlogbx_lt : Real.log |x| / Real.log ↑fmt.β < (e : ℝ) + (fmt.prec : ℝ) := by
      have h1 := Int.lt_floor_add_one (Real.log |x| / Real.log ↑fmt.β)
      have h2 : (⌊Real.log |x| / Real.log ↑fmt.β⌋ : ℝ) + 1 ≤ (e : ℝ) + (fmt.prec : ℝ) := by
        exact_mod_cast show ⌊Real.log |x| / Real.log ↑fmt.β⌋ + 1 ≤ e + ↑fmt.prec from by omega
      linarith
    -- log |x| < (e+p) * log β
    have h_log : Real.log |x| < ((e : ℝ) + (fmt.prec : ℝ)) * Real.log ↑fmt.β := by
      have := hlogbx_lt
      rwa [div_lt_iff₀ hlogβ] at this
    -- Therefore |x| < β^(e+p)
    have hβep_pos : (0 : ℝ) < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) :=
      zpow_pos fmt.β_pos _
    have hx_lt : |x| < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
      have hβep_log : Real.log ((fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec)) =
          ((e : ℝ) + ↑fmt.prec) * Real.log ↑fmt.β := by
        rw [Real.log_zpow]; push_cast; ring
      have h_log' : Real.log |x| < Real.log ((fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec)) := by
        rw [hβep_log]; exact h_log
      calc |x| = Real.exp (Real.log |x|) := (Real.exp_log hx_pos).symm
        _ < Real.exp (Real.log ((fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec))) :=
            Real.exp_strictMono h_log'
        _ = (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := Real.exp_log hβep_pos
    -- |x / β^e| = |x| / β^e < β^(e+p) / β^e = β^p
    rw [abs_div, abs_of_pos (bpow_pos fmt e)]
    rw [div_lt_iff₀ (bpow_pos fmt e)]
    calc (fmt.β : ℝ) ^ fmt.prec * bpow fmt e
        = (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
          unfold bpow
          rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]
          congr 1; omega
      _ > |x| := hx_lt

/-! ## Properties of roundTZ -/

theorem roundTZ_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundTZ fmt x) := by
  unfold roundTZ
  refine ⟨ztrunc (x / bpow fmt (cexp fmt x)), cexp fmt x, rfl, ?_, cexp_emin_le fmt x⟩
  have h := lt_of_le_of_lt (ztrunc_cast_abs_le _) (scaled_abs_lt fmt x)
  exact_mod_cast h

theorem roundTZ_le_abs (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x| ≤ |x| := by
  unfold roundTZ
  set e := cexp fmt x
  calc |(ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e|
      = |(ztrunc (x / bpow fmt e) : ℝ)| * |bpow fmt e| := abs_mul _ _
    _ = |(ztrunc (x / bpow fmt e) : ℝ)| * bpow fmt e := by
        rw [abs_of_pos (bpow_pos fmt e)]
    _ ≤ |x / bpow fmt e| * bpow fmt e :=
        mul_le_mul_of_nonneg_right (ztrunc_cast_abs_le _) (le_of_lt (bpow_pos fmt e))
    _ = |x| / bpow fmt e * bpow fmt e := by
        rw [abs_div, abs_of_pos (bpow_pos fmt e)]
    _ = |x| := div_mul_cancel₀ |x| (bpow_ne_zero fmt e)

/-- The canonical exponent is bounded by any valid exponent of a representation. -/
theorem cexp_le_of_repr (fmt : FloatFormat) {m : ℤ} {e : ℤ}
    (hm_ne : m ≠ 0) (hm : |m| < (fmt.β ^ fmt.prec : ℤ)) (he : fmt.emin ≤ e) :
    cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e) ≤ e := by
  have hx_ne : (m : ℝ) * (fmt.β : ℝ) ^ e ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hm_ne) (zpow_ne_zero _ fmt.β_ne_zero)
  unfold cexp; rw [if_neg hx_ne]
  -- Goal: max emin (⌊log|m*β^e| / logβ⌋ - p + 1) ≤ e
  refine max_le he ?_
  have hlogβ : 0 < Real.log (fmt.β : ℝ) := Real.log_pos fmt.β_one_lt
  have hx_pos : 0 < |(m : ℝ) * (fmt.β : ℝ) ^ e| := abs_pos.mpr hx_ne
  -- |m * β^e| < β^(e+p)
  have hx_lt : |(m : ℝ) * (fmt.β : ℝ) ^ e| < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
    rw [abs_mul, abs_of_pos (zpow_pos fmt.β_pos e)]
    calc |(m : ℝ)| * (fmt.β : ℝ) ^ e
        < (fmt.β : ℝ) ^ (fmt.prec : ℤ) * (fmt.β : ℝ) ^ e := by
          exact mul_lt_mul_of_pos_right (by exact_mod_cast hm) (zpow_pos fmt.β_pos e)
      _ = (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
          rw [mul_comm, ← zpow_add₀ fmt.β_ne_zero]
  -- log|x| / logβ < e + p
  have h_logb : Real.log |(m : ℝ) * (fmt.β : ℝ) ^ e| / Real.log ↑fmt.β <
      (e : ℝ) + (fmt.prec : ℝ) := by
    rw [div_lt_iff₀ hlogβ]
    calc Real.log |(m : ℝ) * (fmt.β : ℝ) ^ e|
        < Real.log ((fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec)) := Real.log_lt_log hx_pos hx_lt
      _ = ((e : ℝ) + ↑fmt.prec) * Real.log ↑fmt.β := by rw [Real.log_zpow]; push_cast; ring
  -- ⌊log|x| / logβ⌋ < e + p, so ⌊...⌋ - p + 1 ≤ e
  have : ⌊Real.log |(m : ℝ) * (fmt.β : ℝ) ^ e| / Real.log ↑fmt.β⌋ < e + ↑fmt.prec :=
    Int.floor_lt.mpr (by exact_mod_cast h_logb)
  omega

/-- Representable numbers are fixed points of roundTZ. -/
theorem roundTZ_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundTZ fmt x = x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval]; exact roundTZ_zero fmt
  · rw [hval]; unfold roundTZ; dsimp only
    have hce_le : cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e) ≤ e :=
      cexp_le_of_repr fmt hm_ne hm he
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e) with hce_def
    -- The division yields an integer
    have ⟨n, hn⟩ : ∃ (n : ℤ),
        (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (n : ℝ) := by
      refine ⟨m * ↑(fmt.β ^ (e - ce).toNat), ?_⟩
      unfold bpow; push_cast
      rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
      congr 2
      exact (Int.toNat_of_nonneg (by omega)).symm
    conv_lhs => rw [show (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (n : ℝ) from hn]
    rw [ztrunc_intCast]
    rw [show (n : ℝ) = (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce from hn.symm]
    exact div_mul_cancel₀ _ (bpow_ne_zero fmt ce)

theorem roundTZ_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundTZ fmt (roundTZ fmt x) = roundTZ fmt x :=
  roundTZ_repr_fixed fmt (roundTZ_isRepresentable fmt x)

/-- ztrunc preserves sign: non-negative input gives non-negative output. -/
theorem ztrunc_nonneg {y : ℝ} (hy : 0 ≤ y) : (0 : ℤ) ≤ ztrunc y := by
  unfold ztrunc; rw [if_pos hy]; exact Int.floor_nonneg.mpr hy

/-- ztrunc preserves sign: non-positive input gives non-positive output. -/
theorem ztrunc_nonpos {y : ℝ} (hy : y ≤ 0) : ztrunc y ≤ 0 := by
  unfold ztrunc
  by_cases h : y ≥ 0
  · have : y = 0 := le_antisymm hy h
    rw [if_pos h, this]; simp
  · rw [if_neg h]; exact Int.ceil_le.mpr (by exact_mod_cast hy)

/-- roundTZ preserves non-negativity. -/
theorem roundTZ_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ roundTZ fmt x := by
  unfold roundTZ; dsimp only
  exact mul_nonneg (by exact_mod_cast ztrunc_nonneg (div_nonneg hx (le_of_lt (bpow_pos fmt _))))
    (le_of_lt (bpow_pos fmt _))

/-- roundTZ preserves non-positivity. -/
theorem roundTZ_nonpos (fmt : FloatFormat) {x : ℝ} (hx : x ≤ 0) :
    roundTZ fmt x ≤ 0 := by
  unfold roundTZ; dsimp only
  exact mul_nonpos_of_nonpos_of_nonneg
    (by exact_mod_cast ztrunc_nonpos (div_nonpos_of_nonpos_of_nonneg hx (le_of_lt (bpow_pos fmt _))))
    (le_of_lt (bpow_pos fmt _))

/-- Truncation error is less than one unit. -/
theorem ztrunc_sub_lt_one (y : ℝ) : |(ztrunc y : ℝ) - y| < 1 := by
  unfold ztrunc
  split_ifs with hy
  · rw [abs_of_nonpos (by linarith [Int.floor_le y])]
    linarith [Int.lt_floor_add_one y]
  · rw [abs_of_nonneg (by linarith [Int.le_ceil y])]
    linarith [Int.ceil_lt_add_one y]

/-- Absolute error: |roundTZ(x) - x| < β^(cexp x). -/
theorem roundTZ_error_abs (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x - x| < bpow fmt (cexp fmt x) := by
  unfold roundTZ; dsimp only
  set e := cexp fmt x
  have he := bpow_pos fmt e
  have h1 : (ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e - x =
      ((ztrunc (x / bpow fmt e) : ℝ) - x / bpow fmt e) * bpow fmt e := by
    rw [sub_mul, div_mul_cancel₀ x (bpow_ne_zero fmt e)]
  rw [h1, abs_mul, abs_of_pos he]
  calc |(ztrunc (x / bpow fmt e) : ℝ) - x / bpow fmt e| * bpow fmt e
      < 1 * bpow fmt e := mul_lt_mul_of_pos_right (ztrunc_sub_lt_one _) he
    _ = bpow fmt e := one_mul _

theorem roundTZ_monotone (fmt : FloatFormat) : Monotone (roundTZ fmt) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · -- 0 ≤ x ≤ y: both non-negative
    have hy : 0 ≤ y := le_trans hx hxy
    have hrx := roundTZ_nonneg fmt hx
    have hle := (roundTZ_le_abs fmt x)
    rw [abs_of_nonneg hx] at hle
    -- roundTZ(x) is representable and 0 ≤ roundTZ(x) ≤ x ≤ y
    -- roundTZ(y) is the largest representable ≤ y, so roundTZ(x) ≤ roundTZ(y)
    sorry
  · by_cases hy : y ≤ 0
    · -- x ≤ y ≤ 0: use negation symmetry
      sorry
    · -- x < 0 < y: roundTZ(x) ≤ 0 ≤ roundTZ(y)
      exact le_trans (roundTZ_nonpos fmt (le_of_not_ge hx))
        (roundTZ_nonneg fmt (not_le.mp hy).le)

/-- Relative error for normal-range values.
    |roundTZ(x) - x| ≤ ε * |x| when |x| ≥ β^(emin + p - 1). -/
theorem roundTZ_error (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundTZ fmt x - x| ≤ machineEpsilon fmt * |x| := by
  have hx_ne : x ≠ 0 := by
    intro h; subst h; simp at hx
    exact not_le.mpr (zpow_pos fmt.β_pos _) hx
  -- |roundTZ(x) - x| < β^(cexp x) ≤ ε * |x|
  have h1 := roundTZ_error_abs fmt x
  -- Key: cexp(x) = ⌊log_β|x|⌋ - p + 1 (not clamped to emin)
  -- So β^(cexp x) ≤ β^(log_β|x| - p + 1) = |x| * β^(1-p) = ε * |x|
  sorry

noncomputable def roundTowardZeroFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundTZ fmt
  rounds_to_repr := roundTZ_isRepresentable fmt
  idempotent := roundTZ_idempotent fmt
  monotone := roundTZ_monotone fmt

end Flean
