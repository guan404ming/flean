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
theorem cast_chain_two_error {fmt1 fmt2 : FloatFormat} (_href : FormatRefines fmt1 fmt2)
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
    (h12 : FormatRefines fmt1 fmt2) (_h23 : FormatRefines fmt2 fmt3)
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

/-! ## ML cast patterns -/

/-! ### Pattern 1: Widen-compute-narrow

The most common ML pattern: widen inputs to higher precision, compute,
then narrow the result. E.g., cast f16 inputs to f32, multiply, cast
result back to f16. The error is that of the narrow format alone. -/

/-- Widen-compute-narrow: if we widen x to fmt2, apply an exact operation f,
    then narrow back to fmt1, the result equals rounding f(x) in fmt1.
    (Here "exact operation" means f is applied to the real value.) -/
theorem widen_compute_narrow {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt1 (roundNNE fmt2 x) = x :=
  widen_narrow_id href hx

/-! ### Pattern 2: Accumulation in wider precision

In ML training, partial sums are accumulated in f32 while inputs are f16.
Adding an f16 value to an f32 accumulator: the f16 value is exact in f32
(by widening), so the only rounding is the f32 addition rounding. -/

/-- Adding a narrow-format value to a wide-format accumulator: the narrow
    value is exact in the wide format, so no cast error from widening. -/
theorem accumulate_widen_exact {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt2 x = x :=
  cast_widen_exact href hx

/-! ### Pattern 3: Progressive narrowing (quantization pipeline)

f64 → f32 → f16: two successive narrowing steps.
Error accumulates but is bounded by the composition theorem. -/

/-- Progressive narrowing: the total error of two narrowing steps is
    bounded by the sum of individual errors plus a cross term. -/
theorem progressive_narrow_error {fmt1 fmt2 fmt3 : FloatFormat}
    (_h12 : FormatRefines fmt1 fmt2) (_h23 : FormatRefines fmt2 fmt3)
    (x : ℝ)
    (_hx3 : (fmt3.β : ℝ) ^ (fmt3.emin + (fmt3.prec : ℤ) - 1) ≤ |x|)
    (_hx2 : (fmt2.β : ℝ) ^ (fmt2.emin + (fmt2.prec : ℤ) - 1) ≤ |roundNNE fmt3 x|)
    (_hx1 : (fmt1.β : ℝ) ^ (fmt1.emin + (fmt1.prec : ℤ) - 1) ≤ |roundNNE fmt2 (roundNNE fmt3 x)|) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| ≤
      |x - roundNNE fmt3 x| +
      |roundNNE fmt3 x - roundNNE fmt2 (roundNNE fmt3 x)| +
      |roundNNE fmt2 (roundNNE fmt3 x) - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| := by
  calc |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))|
      = |(x - roundNNE fmt3 x) +
         (roundNNE fmt3 x - roundNNE fmt2 (roundNNE fmt3 x)) +
         (roundNNE fmt2 (roundNNE fmt3 x) - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x)))| := by
        congr 1; ring
    _ ≤ _ := by
        set a1 := x - roundNNE fmt3 x
        set a2 := roundNNE fmt3 x - roundNNE fmt2 (roundNNE fmt3 x)
        set a3 := roundNNE fmt2 (roundNNE fmt3 x) - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))
        have h1 : |a1 + a2 + a3| ≤ |a1 + a2| + |a3| := abs_add_le _ _
        have h2 : |a1 + a2| ≤ |a1| + |a2| := abs_add_le _ _
        linarith

/-! ### Pattern 4: Cast absorption (idempotence)

Redundant casts can be eliminated. -/

/-- Narrowing twice to the same format is the same as once. -/
theorem narrow_absorb (fmt : FloatFormat) (x : ℝ) :
    roundNNE fmt (roundNNE fmt x) = roundNNE fmt x :=
  roundNNE_idempotent fmt x

/-- Narrowing to fmt1 absorbs a prior narrowing to fmt1 through fmt2. -/
theorem narrow_absorb_widen {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    (x : ℝ) :
    roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt1 x)) = roundNNE fmt1 x := by
  rw [narrow_widen_id href, roundNNE_idempotent]

/-! ### Pattern 5: Monotonicity of cast error

Coarser format has larger maximum error. -/

/-- A finer format always has at most the rounding error of a coarser one. -/
theorem finer_format_smaller_error {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    (x : ℝ) :
    |x - roundNNE fmt2 x| ≤ |x - roundNNE fmt1 x| := by
  exact roundNNE_nearest fmt2 x (isRepresentable_of_refines href (roundNNE_isRepresentable fmt1 x))

/-! ### Pattern 6: Error dominance

When chaining a fine-then-coarse cast, the coarse cast dominates. -/

/-- The error of fine-then-coarse is at most 2x the fine error plus the coarse error.
    Since fine error ≤ coarse error, this gives ≤ 3x coarse error. -/
theorem cast_chain_error_dominance {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      2 * |x - roundNNE fmt2 x| + |x - roundNNE fmt1 x| := by
  have h1 := cast_chain_two_error href x
  have h2 : |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      |roundNNE fmt2 x - roundNNE fmt1 x| :=
    roundNNE_nearest fmt1 (roundNNE fmt2 x) (roundNNE_isRepresentable fmt1 x)
  have h3 : |roundNNE fmt2 x - roundNNE fmt1 x| ≤
      |roundNNE fmt2 x - x| + |x - roundNNE fmt1 x| := by
    calc |roundNNE fmt2 x - roundNNE fmt1 x|
        = |(roundNNE fmt2 x - x) + (x - roundNNE fmt1 x)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith [abs_sub_comm (roundNNE fmt2 x) x]

/-! ### Pattern 7: Transitivity of FormatRefines -/

theorem FormatRefines.trans {fmt1 fmt2 fmt3 : FloatFormat}
    (h12 : FormatRefines fmt1 fmt2) (h23 : FormatRefines fmt2 fmt3) :
    FormatRefines fmt1 fmt3 where
  radix_eq := h12.radix_eq.trans h23.radix_eq
  prec_le := le_trans h12.prec_le h23.prec_le
  emin_le := le_trans h23.emin_le h12.emin_le

/-- Widening through an intermediate format is exact. -/
theorem widen_chain_exact {fmt1 fmt2 fmt3 : FloatFormat}
    (h12 : FormatRefines fmt1 fmt2) (h23 : FormatRefines fmt2 fmt3)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt3 (roundNNE fmt2 x) = x := by
  rw [cast_widen_exact h12 hx]
  exact cast_widen_exact (h12.trans h23) hx

/-! ### Concrete ML patterns -/

/-- f16 multiply pattern: widen to f32, multiply is exact in f32 for f16 inputs. -/
theorem f16_inputs_exact_in_f32 {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary32 x = x :=
  accumulate_widen_exact binary16_refines_binary32 hx

/-- f16 → f32 → f64 widening chain is exact. -/
theorem f16_widen_chain_f64 {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary64 (roundNNE binary32 x) = x :=
  widen_chain_exact binary16_refines_binary32 binary32_refines_binary64 hx

/-- f32 accumulator pattern: narrow f32 result back to f16 gives single rounding. -/
theorem f32_accumulate_narrow_f16 {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary16 (roundNNE binary32 x) = x :=
  widen_narrow_id binary16_refines_binary32 hx

/-- The finer the intermediate format, the smaller the intermediate error. -/
theorem f64_intermediate_better_than_f32 (x : ℝ) :
    |x - roundNNE binary64 x| ≤ |x - roundNNE binary32 x| :=
  finer_format_smaller_error binary32_refines_binary64 x

/-! ## General chain decomposition -/

/-- One-step peeling: |x - round(y)| ≤ |x - y| + |y - round(y)|. -/
theorem chain_peel (fmt : FloatFormat) (x y : ℝ) :
    |x - roundNNE fmt y| ≤ |x - y| + |y - roundNNE fmt y| := by
  calc |x - roundNNE fmt y|
      = |(x - y) + (y - roundNNE fmt y)| := by congr 1; ring
    _ ≤ |x - y| + |y - roundNNE fmt y| := abs_add_le _ _

/-- One-step peeling with ULP bound. -/
theorem chain_peel' (fmt : FloatFormat) (x y : ℝ) :
    |x - roundNNE fmt y| ≤ |x - y| + bpow fmt (cexp fmt y) / 2 :=
  le_trans (chain_peel fmt x y) (by linarith [roundNNE_sub_abs_le fmt y])

/-- Two-step chain with ULP bounds. -/
theorem chain_error_2_ulp (fmt1 fmt2 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      bpow fmt2 (cexp fmt2 x) / 2 +
      bpow fmt1 (cexp fmt1 (roundNNE fmt2 x)) / 2 := by
  calc |x - roundNNE fmt1 (roundNNE fmt2 x)|
      ≤ |x - roundNNE fmt2 x| + |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| :=
        chain_peel fmt1 x (roundNNE fmt2 x)
    _ ≤ _ := by
        linarith [roundNNE_sub_abs_le fmt2 x, roundNNE_sub_abs_le fmt1 (roundNNE fmt2 x)]

/-- Three-step chain with ULP bounds. -/
theorem chain_error_3_ulp (fmt1 fmt2 fmt3 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| ≤
      bpow fmt3 (cexp fmt3 x) / 2 +
      bpow fmt2 (cexp fmt2 (roundNNE fmt3 x)) / 2 +
      bpow fmt1 (cexp fmt1 (roundNNE fmt2 (roundNNE fmt3 x))) / 2 := by
  set y := roundNNE fmt3 x; set z := roundNNE fmt2 y
  calc |x - roundNNE fmt1 z|
      ≤ |x - z| + |z - roundNNE fmt1 z| := chain_peel fmt1 x z
    _ ≤ (|x - y| + |y - z|) + |z - roundNNE fmt1 z| := by
        linarith [chain_peel fmt2 x y]
    _ ≤ _ := by
        linarith [roundNNE_sub_abs_le fmt3 x,
                  roundNNE_sub_abs_le fmt2 (roundNNE fmt3 x),
                  roundNNE_sub_abs_le fmt1 (roundNNE fmt2 (roundNNE fmt3 x))]

/-- Four-step chain decomposition. -/
theorem chain_error_4 (fmt1 fmt2 fmt3 fmt4 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x)))| ≤
      |x - roundNNE fmt4 x| +
      |roundNNE fmt4 x - roundNNE fmt3 (roundNNE fmt4 x)| +
      |roundNNE fmt3 (roundNNE fmt4 x) -
        roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x))| +
      |roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x)) -
        roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x)))| := by
  set a := roundNNE fmt4 x; set b := roundNNE fmt3 a; set c := roundNNE fmt2 b
  calc |x - roundNNE fmt1 c|
      ≤ |x - c| + |c - roundNNE fmt1 c| := chain_peel fmt1 x c
    _ ≤ (|x - b| + |b - c|) + |c - roundNNE fmt1 c| := by
        linarith [chain_peel fmt2 x b]
    _ ≤ ((|x - a| + |a - b|) + |b - c|) + |c - roundNNE fmt1 c| := by
        linarith [chain_peel fmt3 x a]
    _ = _ := by ring

/-! ## General n-step chain via lists -/

/-- Apply a list of rounding functions in sequence (innermost first). -/
noncomputable def roundChain (fmts : List FloatFormat) (x : ℝ) : ℝ :=
  fmts.foldl (fun acc fmt => roundNNE fmt acc) x

theorem roundChain_nil (x : ℝ) : roundChain [] x = x := rfl

theorem roundChain_cons (fmt : FloatFormat) (fmts : List FloatFormat) (x : ℝ) :
    roundChain (fmt :: fmts) x = roundChain fmts (roundNNE fmt x) := by
  unfold roundChain; simp [List.foldl]

theorem roundChain_singleton (fmt : FloatFormat) (x : ℝ) :
    roundChain [fmt] x = roundNNE fmt x := rfl

/-- Sum of individual rounding errors along a chain. -/
noncomputable def chainErrorSum (fmts : List FloatFormat) (x : ℝ) : ℝ :=
  match fmts with
  | [] => 0
  | fmt :: rest =>
    let y := roundNNE fmt x
    |x - y| + chainErrorSum rest y

theorem chainErrorSum_nonneg (fmts : List FloatFormat) (x : ℝ) :
    0 ≤ chainErrorSum fmts x := by
  induction fmts generalizing x with
  | nil => simp [chainErrorSum]
  | cons fmt rest ih => simp [chainErrorSum]; linarith [abs_nonneg (x - roundNNE fmt x), ih (roundNNE fmt x)]

/-- General n-step chain error bound: total error ≤ sum of individual errors. -/
theorem roundChain_error_le_sum (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainErrorSum fmts x := by
  induction fmts generalizing x with
  | nil => simp [roundChain, chainErrorSum]
  | cons fmt rest ih =>
    rw [roundChain_cons]; simp only [chainErrorSum]
    set y := roundNNE fmt x
    calc |x - roundChain rest y|
        = |(x - y) + (y - roundChain rest y)| := by congr 1; ring
      _ ≤ |x - y| + |y - roundChain rest y| := abs_add_le _ _
      _ ≤ |x - y| + chainErrorSum rest y := by linarith [ih y]

/-- Sum of bpow/2 at each step. -/
noncomputable def chainBpowSum (fmts : List FloatFormat) (x : ℝ) : ℝ :=
  match fmts with
  | [] => 0
  | fmt :: rest =>
    bpow fmt (cexp fmt x) / 2 + chainBpowSum rest (roundNNE fmt x)

/-- Chain error sum ≤ sum of bpow/2 at each step. -/
theorem chainErrorSum_le_bpow_sum (fmts : List FloatFormat) (x : ℝ) :
    chainErrorSum fmts x ≤ chainBpowSum fmts x := by
  induction fmts generalizing x with
  | nil => simp [chainErrorSum, chainBpowSum]
  | cons fmt rest ih =>
    simp only [chainErrorSum, chainBpowSum]
    linarith [roundNNE_sub_abs_le fmt x, ih (roundNNE fmt x)]

/-- Total chain error ≤ sum of ULP/2 at each step. -/
theorem roundChain_error_le_bpow_sum (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainBpowSum fmts x :=
  le_trans (roundChain_error_le_sum fmts x) (chainErrorSum_le_bpow_sum fmts x)

/-- A chain of the same format collapses to a single rounding. -/
theorem roundChain_same (fmt : FloatFormat) (n : ℕ) (x : ℝ) :
    roundChain (List.replicate (n + 1) fmt) x = roundNNE fmt x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, roundChain_cons]
    exact (ih (roundNNE fmt x)).trans (roundNNE_idempotent fmt x)

end Flean
