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

theorem roundTZ_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundTZ fmt (roundTZ fmt x) = roundTZ fmt x := by
  sorry

theorem roundTZ_monotone (fmt : FloatFormat) : Monotone (roundTZ fmt) := by
  sorry

theorem roundTZ_error (fmt : FloatFormat) {x : ℝ} (hx : x ≠ 0) :
    |roundTZ fmt x - x| ≤ machineEpsilon fmt * |x| := by
  sorry

noncomputable def roundTowardZeroFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundTZ fmt
  rounds_to_repr := roundTZ_isRepresentable fmt
  idempotent := roundTZ_idempotent fmt
  monotone := roundTZ_monotone fmt

end Flean
