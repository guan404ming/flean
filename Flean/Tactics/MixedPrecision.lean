import Flean.Core.CastChain
import Flean.Arith.Conversions
import Lean
import Mathlib.Tactic.NormNum

/-!
# Flean.Tactics.MixedPrecision

Custom Lean 4 tactics for ML compiler mixed-precision analysis.

## Tactics

- `flean_cast_safe`: Prove that a cast chain preserves values exactly
  (widen-narrow idempotence, widening exactness, etc.)
- `flean_cast_bound`: Derive error bounds for cast chains by composing
  rounding error lemmas.
- `flean_quant_bound`: Derive error bounds for quantization schemes
  (progressive narrowing pipelines).

## Strategy

Each tactic works by:
1. Pattern-matching the goal to identify cast chain structure
2. Selecting the appropriate lemma (widen_narrow_id, cast_chain_two_bound, etc.)
3. Applying it with `norm_num` to discharge numeric side conditions
-/

namespace Flean

open Lean Meta Elab Tactic

/-! ## flean_cast_safe: prove cast chains are exact -/

/-- `flean_cast_safe` proves goals of the form:
    - `roundNNE fmt1 (roundNNE fmt2 x) = x` (widen-narrow)
    - `roundNNE fmt2 x = x` (widening)
    - `roundNNE fmt (roundNNE fmt x) = roundNNE fmt x` (idempotence)
    - `roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt1 x)) = roundNNE fmt1 x` (narrow-widen-narrow)
    by trying relevant CastChain lemmas with `norm_num` for format conditions. -/
syntax (name := fleanCastSafe) "flean_cast_safe" : tactic

@[tactic fleanCastSafe]
def evalFleanCastSafe : Tactic := fun _ => do
  -- Try each cast-safety lemma in order of specificity
  let tactics ← `(tactic|
    first
    -- Idempotence: roundNNE fmt (roundNNE fmt x) = roundNNE fmt x
    | exact roundNNE_idempotent _ _
    -- Widen-narrow: roundNNE fmt1 (roundNNE fmt2 x) = x
    | (apply widen_narrow_id; constructor <;> (first | rfl | decide))
    -- Widening exact: roundNNE fmt2 x = x
    | (apply cast_widen_exact; constructor <;> (first | rfl | decide))
    -- Narrow-widen-narrow absorption
    | (apply narrow_absorb_widen; constructor <;> (first | rfl | decide))
    -- Same-format n-fold collapse
    | exact cast_chain_same_format _ _ _
    -- Widen chain exact: roundNNE fmt3 (roundNNE fmt2 x) = x
    | (apply widen_chain_exact <;> (constructor <;> (first | rfl | decide)))
    -- Double cast safe
    | (apply double_cast_safe; constructor <;> (first | rfl | decide))
    -- Narrow then widen = narrow
    | (apply narrow_widen_id; constructor <;> (first | rfl | decide))
    -- Repr fixed point
    | exact roundNNE_repr_fixed _ ‹_›
    -- Fallback: try simp with cast chain lemmas
    | (simp only [roundNNE_idempotent, narrow_widen_id, cast_widen_exact, widen_narrow_id])
  )
  evalTactic tactics

/-! ## flean_cast_bound: derive error bounds for cast chains -/

/-- `flean_cast_bound` proves goals of the form:
    - `|x - roundNNE fmt x| ≤ ...` (single cast)
    - `|x - roundNNE fmt1 (roundNNE fmt2 x)| ≤ ...` (two-step chain)
    - error dominance bounds
    by applying error bound lemmas and using `linarith`/`norm_num`. -/
syntax (name := fleanCastBound) "flean_cast_bound" : tactic

@[tactic fleanCastBound]
def evalFleanCastBound : Tactic := fun _ => do
  let tactics ← `(tactic|
    first
    -- Single cast NNE error: |x - roundNNE fmt x| ≤ bpow/2
    | exact roundNNE_sub_abs_le _ _
    -- Single cast NNE relative error
    | exact roundNNE_error_rel _ ‹_›
    -- Finer format has smaller error
    | (apply finer_format_smaller_error; constructor <;> (first | rfl | decide))
    -- Two-step chain triangle inequality
    | (apply cast_chain_two_error; constructor <;> (first | rfl | decide))
    -- Two-step chain tight bound
    | (apply cast_chain_two_bound <;> first | (constructor <;> (first | rfl | decide)) | assumption)
    -- Error dominance: |x - round1(round2(x))| ≤ 2*|x-round2(x)| + |x-round1(x)|
    | (apply cast_chain_error_dominance; constructor <;> (first | rfl | decide))
    -- Progressive narrowing (3-step)
    | apply progressive_narrow_error <;> first | (constructor <;> (first | rfl | decide)) | assumption
    -- roundNNE_nearest: |x - roundNNE x| ≤ |x - z| for repr z
    | exact roundNNE_nearest _ _ ‹_›
    -- Fallback: try linarith with available error bounds
    | (linarith [roundNNE_sub_abs_le _ _, roundDN_le _ _, roundUP_ge _ _])
  )
  evalTactic tactics

/-! ## flean_quant_bound: quantization scheme error bounds -/

/-- `flean_quant_bound` proves goals about quantization error bounds.
    Handles patterns like:
    - f32 → f16 quantization error
    - f32 → f16 → f32 dequantization round-trip error
    - Progressive quantization f64 → f32 → f16 -/
syntax (name := fleanQuantBound) "flean_quant_bound" : tactic

@[tactic fleanQuantBound]
def evalFleanQuantBound : Tactic := fun _ => do
  let tactics ← `(tactic|
    first
    -- Quantize then dequantize is identity for representable values
    | (apply widen_narrow_id; constructor <;> (first | rfl | decide))
    -- Quantization error = single rounding error
    | exact roundNNE_sub_abs_le _ _
    -- Quantization relative error
    | exact roundNNE_error_rel _ ‹_›
    -- Progressive quantization error
    | apply progressive_narrow_error <;> first | (constructor <;> (first | rfl | decide)) | assumption
    -- Two-step quantization bound
    | (apply cast_chain_two_bound <;> first | (constructor <;> (first | rfl | decide)) | assumption)
    -- Accumulation in wider format is exact
    | (apply accumulate_widen_exact; constructor <;> (first | rfl | decide))
    -- Fallback: try the cast bound tactic
    | flean_cast_bound
    -- Last resort: try the cast safe tactic (for identity cases)
    | flean_cast_safe
  )
  evalTactic tactics

/-! ## Convenience lemma: machine epsilon values for concrete formats -/

theorem machineEpsilon_binary16 : machineEpsilon binary16 = (2 : ℝ) ^ (-10 : ℤ) := by
  unfold machineEpsilon binary16; norm_num

theorem machineEpsilon_binary32 : machineEpsilon binary32 = (2 : ℝ) ^ (-23 : ℤ) := by
  unfold machineEpsilon binary32; norm_num

theorem machineEpsilon_binary64 : machineEpsilon binary64 = (2 : ℝ) ^ (-52 : ℤ) := by
  unfold machineEpsilon binary64; norm_num

/-! ## Demo: tactics in action -/

-- Demo 1: idempotence
example (x : ℝ) :
    roundNNE binary32 (roundNNE binary32 x) = roundNNE binary32 x := by
  flean_cast_safe

-- Demo 2: widen-narrow with explicit FormatRefines
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary16 (roundNNE binary32 x) = x := by
  exact widen_narrow_id binary16_refines_binary32 hx

-- Demo 3: widening exactness
example {x : ℝ} (hx : isRepresentable binary32 x) :
    roundNNE binary64 x = x := by
  exact cast_widen_exact binary32_refines_binary64 hx

-- Demo 4: narrow-widen absorption
example (x : ℝ) :
    roundNNE binary16 (roundNNE binary32 (roundNNE binary16 x)) = roundNNE binary16 x := by
  exact narrow_absorb_widen binary16_refines_binary32 x

-- Demo 5: finer format has smaller error
example (x : ℝ) :
    |x - roundNNE binary64 x| ≤ |x - roundNNE binary32 x| := by
  exact finer_format_smaller_error binary32_refines_binary64 x

-- Demo 6: single rounding error bound
example (x : ℝ) :
    |x - roundNNE binary32 x| ≤ bpow binary32 (cexp binary32 x) / 2 := by
  flean_cast_bound

-- Demo 7: accumulation exactness
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary32 x = x := by
  exact accumulate_widen_exact binary16_refines_binary32 hx

end Flean
