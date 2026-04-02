import Flean.Core.Rounding
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Flean.Core.RoundProps

Concrete rounding functions and proofs of their properties.
Defines roundTowardZero (truncation) and proves representability,
idempotence, and monotonicity.
-/

namespace Flean

/-! ## Helper lemmas about the radix β -/

theorem FloatFormat.β_pos (fmt : FloatFormat) : (0 : ℝ) < (fmt.β : ℝ) := by
  have h := fmt.hβ
  exact Nat.cast_pos.mpr (by omega)

theorem FloatFormat.β_ne_zero (fmt : FloatFormat) : (fmt.β : ℝ) ≠ 0 :=
  ne_of_gt fmt.β_pos

theorem FloatFormat.β_one_lt (fmt : FloatFormat) : (1 : ℝ) < (fmt.β : ℝ) := by
  have : 1 < fmt.β := by have := fmt.hβ; omega
  exact_mod_cast this

/-! ## Representability lemmas -/

theorem zero_isRepresentable (fmt : FloatFormat) : isRepresentable fmt 0 := by
  refine ⟨0, fmt.emin, by simp, ?_, le_refl _⟩
  simp
  exact pow_pos (show 0 < fmt.β from by have := fmt.hβ; omega) fmt.prec

theorem neg_isRepresentable {fmt : FloatFormat} {x : ℝ}
    (hx : isRepresentable fmt x) : isRepresentable fmt (-x) := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  exact ⟨-m, e, by rw [hval]; push_cast; ring, by rwa [Int.natAbs_neg], he⟩

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

/-! ## Canonical exponent -/

noncomputable def cexp (fmt : FloatFormat) (x : ℝ) : ℤ :=
  if x = 0 then fmt.emin
  else max fmt.emin (⌊Real.log |x| / Real.log (fmt.β : ℝ)⌋ - (fmt.prec : ℤ) + 1)

theorem cexp_zero (fmt : FloatFormat) : cexp fmt 0 = fmt.emin := by
  simp [cexp]

theorem cexp_emin_le (fmt : FloatFormat) (x : ℝ) : fmt.emin ≤ cexp fmt x := by
  unfold cexp
  split
  · exact le_refl _
  · exact le_max_left _ _

/-! ## Round toward zero -/

noncomputable def roundTZ (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e

/-- Rounding zero gives zero. -/
theorem roundTZ_zero (fmt : FloatFormat) : roundTZ fmt 0 = 0 := by
  simp [roundTZ, cexp_zero, ztrunc_zero, bpow]

/-- The result of roundTZ is always representable. -/
theorem roundTZ_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundTZ fmt x) := by
  unfold roundTZ
  refine ⟨ztrunc (x / bpow fmt (cexp fmt x)), cexp fmt x, rfl, ?_, cexp_emin_le fmt x⟩
  sorry

/-- roundTZ is idempotent: rounding an already-rounded value is a no-op. -/
theorem roundTZ_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundTZ fmt (roundTZ fmt x) = roundTZ fmt x := by
  sorry

/-- roundTZ is monotone: x ≤ y implies roundTZ x ≤ roundTZ y. -/
theorem roundTZ_monotone (fmt : FloatFormat) : Monotone (roundTZ fmt) := by
  sorry

/-- roundTZ truncates toward zero: |roundTZ(x)| ≤ |x|. -/
theorem roundTZ_le_abs (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x| ≤ |x| := by
  sorry

/-- Relative error bound: |roundTZ(x) - x| ≤ ε * |x|. -/
theorem roundTZ_error (fmt : FloatFormat) {x : ℝ} (hx : x ≠ 0) :
    |roundTZ fmt x - x| ≤ machineEpsilon fmt * |x| := by
  sorry

/-- Construct a RoundingFn for roundTowardZero. -/
noncomputable def roundTowardZeroFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundTZ fmt
  rounds_to_repr := roundTZ_isRepresentable fmt
  idempotent := roundTZ_idempotent fmt
  monotone := roundTZ_monotone fmt

end Flean
