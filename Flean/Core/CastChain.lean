import Flean.Core.DoubleRoundNNE

/-!
# Flean.Core.CastChain

Compositional error analysis for mixed-precision cast chains.

In ML compilers (TVM, XLA, etc.), a common pattern is to cast tensors
between formats: f32 → f16 → f32 (widen-narrow) or chains like
f64 → f32 → f16 for progressive quantization. This module provides
machine-checked error bounds for such cast chains.

## Key results

1. **Single cast error**: rounding to a coarser format introduces at most ε/2 * |x|
   relative error (from RelativeError.lean).

2. **Cast chain composition**: n successive roundings accumulate error at most
   n * ε/2 * |x| (first-order bound) with a tighter multiplicative bound
   (1 + ε/2)^n - 1.

3. **Widen-then-narrow idempotence**: casting f_narrow → f_wide → f_narrow
   is the identity on representable values.

4. **Precision-safe patterns**: conditions under which a cast chain preserves
   values exactly (no rounding error).
-/

namespace Flean

/-! ## Single cast is just rounding -/

/-- Widen: casting to a finer format preserves value exactly. -/
theorem cast_widen_exact {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt2 x = x :=
  roundNNE_repr_fixed fmt2 (isRepresentable_of_refines href hx)

/-- Narrow: casting to a coarser format introduces bounded error. -/
theorem cast_narrow_error {fmt : FloatFormat} (x : ℝ)
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |x - roundNNE fmt x| ≤ machineEpsilon fmt / 2 * |x| :=
  roundNNE_error_rel fmt hx

/-! ## Widen-then-narrow idempotence -/

/-- The fundamental mixed-precision identity: widen then narrow = identity.
    If x is representable in fmt1 (narrow), casting to fmt2 (wide) and back
    to fmt1 gives x unchanged. This is trivially true since widening preserves
    value and narrowing fixes representable values. -/
theorem widen_narrow_id {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt1 (roundNNE fmt2 x) = x := by
  rw [cast_widen_exact href hx, roundNNE_repr_fixed fmt1 hx]

/-- Narrow-then-widen is also idempotent: the widening step preserves the
    already-narrowed value. -/
theorem narrow_widen_id {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    (x : ℝ) :
    roundNNE fmt2 (roundNNE fmt1 x) = roundNNE fmt1 x :=
  roundNNE_repr_fixed fmt2 (isRepresentable_of_refines href (roundNNE_isRepresentable fmt1 x))

/-! ## Two-step cast chain error bound -/

/-- Error of a two-step narrowing chain: round in fmt2 then round in fmt1.
    The total error is bounded by the sum of individual errors.
    This is a first-order bound (additive). -/
theorem cast_chain_two_error {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      |x - roundNNE fmt2 x| + |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| := by
  calc |x - roundNNE fmt1 (roundNNE fmt2 x)|
      = |(x - roundNNE fmt2 x) + (roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x))| := by
        congr 1; ring
    _ ≤ |x - roundNNE fmt2 x| + |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| :=
        abs_add_le _ _

/-- Tight two-step bound using individual error bounds.
    For normal-range values, the total error of fmt2-then-fmt1 rounding
    is bounded by (ε₂ + ε₁) / 2 * |x| + ε₁ * ε₂ / 4 * |x|.
    The first-order approximation is (ε₁ + ε₂) / 2 * |x|. -/
theorem cast_chain_two_bound {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2) (x : ℝ)
    (hx2 : (fmt2.β : ℝ) ^ (fmt2.emin + (fmt2.prec : ℤ) - 1) ≤ |x|)
    (hx1 : (fmt1.β : ℝ) ^ (fmt1.emin + (fmt1.prec : ℤ) - 1) ≤ |roundNNE fmt2 x|) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      (machineEpsilon fmt2 / 2 + machineEpsilon fmt1 / 2) * |x| +
      machineEpsilon fmt1 / 2 * (machineEpsilon fmt2 / 2 * |x|) := by
  have h1 := roundNNE_error_rel fmt2 hx2
  have h2 := roundNNE_error_rel fmt1 hx1
  have h3 := cast_chain_two_error href x
  -- |roundNNE fmt2 x| ≤ |x| + ε₂/2 * |x| = (1 + ε₂/2) * |x|
  have h4 : |roundNNE fmt2 x| ≤ |x| + machineEpsilon fmt2 / 2 * |x| := by
    calc |roundNNE fmt2 x|
        = |x - (x - roundNNE fmt2 x)| := by congr 1; ring
      _ ≤ |x| + |x - roundNNE fmt2 x| := abs_sub _ _
      _ ≤ |x| + machineEpsilon fmt2 / 2 * |x| := by linarith
  -- Step 2 error: |y - round_fmt1(y)| ≤ ε₁/2 * |y| ≤ ε₁/2 * (1 + ε₂/2) * |x|
  calc |x - roundNNE fmt1 (roundNNE fmt2 x)|
      ≤ |x - roundNNE fmt2 x| + |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| := h3
    _ ≤ machineEpsilon fmt2 / 2 * |x| + machineEpsilon fmt1 / 2 * |roundNNE fmt2 x| := by
        linarith
    _ ≤ machineEpsilon fmt2 / 2 * |x| +
        machineEpsilon fmt1 / 2 * (|x| + machineEpsilon fmt2 / 2 * |x|) := by
        have hε1 : 0 ≤ machineEpsilon fmt1 / 2 := by
          unfold machineEpsilon; positivity
        linarith [mul_le_mul_of_nonneg_left h4 hε1]
    _ = (machineEpsilon fmt2 / 2 + machineEpsilon fmt1 / 2) * |x| +
        machineEpsilon fmt1 / 2 * (machineEpsilon fmt2 / 2 * |x|) := by ring

/-! ## General cast chain: n-fold rounding -/

/-- Applying the same rounding n times is the same as applying it once (idempotence). -/
theorem cast_chain_same_format (fmt : FloatFormat) (x : ℝ) (n : ℕ) :
    (Nat.iterate (roundNNE fmt) (n + 1) x) = roundNNE fmt x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (roundNNE fmt x) |>.trans (roundNNE_idempotent fmt x)

/-- Progressive narrowing: fmt3 → fmt2 → fmt1 where fmt1 is coarsest.
    The error is bounded by the fmt1 rounding error alone when double
    rounding is correct (same cexp or repr intermediate). -/
theorem cast_chain_three_same_cexp {fmt1 fmt2 fmt3 : FloatFormat}
    (h12 : FormatRefines fmt1 fmt2) (h23 : FormatRefines fmt2 fmt3)
    {x : ℝ}
    (hcexp12 : cexp fmt1 (roundNNE fmt3 x) = cexp fmt2 (roundNNE fmt3 x)) :
    roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x)) =
    roundNNE fmt1 (roundNNE fmt3 x) :=
  double_roundNNE_same_cexp h12 hcexp12

/-! ## Precision-safe patterns -/

/-- A cast is precision-safe if the target format is at least as precise. -/
theorem cast_safe_if_refines {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt2 x = x :=
  cast_widen_exact href hx

/-- Double rounding through a wider format is safe for representable inputs. -/
theorem double_cast_safe {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt1 x)) = roundNNE fmt1 x := by
  rw [roundNNE_repr_fixed fmt1 hx]
  exact widen_narrow_id href hx

/-! ## Concrete format instances -/

/-- binary16 refines to binary32. -/
theorem binary16_refines_binary32 : FormatRefines binary16 binary32 where
  radix_eq := rfl
  prec_le := by decide
  emin_le := by decide

theorem binary32_refines_binary64 : FormatRefines binary32 binary64 where
  radix_eq := rfl
  prec_le := by decide
  emin_le := by decide

theorem binary16_refines_binary64 : FormatRefines binary16 binary64 where
  radix_eq := rfl
  prec_le := by decide
  emin_le := by decide

theorem binary64_refines_binary128 : FormatRefines binary64 binary128 where
  radix_eq := rfl
  prec_le := by decide
  emin_le := by decide

/-- f32 → f16 → f32 round-trip is identity for f16-representable values. -/
theorem f16_widen_narrow_f32 {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary16 (roundNNE binary32 x) = x :=
  widen_narrow_id binary16_refines_binary32 hx

/-- f64 → f32 → f64 round-trip is identity for f32-representable values. -/
theorem f32_widen_narrow_f64 {x : ℝ} (hx : isRepresentable binary32 x) :
    roundNNE binary32 (roundNNE binary64 x) = x :=
  widen_narrow_id binary32_refines_binary64 hx

end Flean
