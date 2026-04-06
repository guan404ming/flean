import Flean.Core.CastChain
import Flean.Tactics.MixedPrecision
import Mathlib.Tactic.NormNum

/-!
# Flean.Tactics.NumericBounds

Concrete numeric error bounds for IEEE 754 cast chains.

Discharges symbolic bounds to concrete numbers like
"f32 → f16 relative error ≤ 2^(-10)" using machineEpsilon values
and norm_num.
-/

namespace Flean

/-! ## Machine epsilon as concrete rationals -/

theorem machineEpsilon_binary16_val : machineEpsilon binary16 = (1 : ℝ) / 1024 := by
  rw [machineEpsilon_binary16]; norm_num

theorem machineEpsilon_bfloat16_val : machineEpsilon bfloat16 = (1 : ℝ) / 128 := by
  rw [machineEpsilon_bfloat16]; norm_num

theorem machineEpsilon_binary32_val : machineEpsilon binary32 = (1 : ℝ) / 8388608 := by
  rw [machineEpsilon_binary32]; norm_num

theorem machineEpsilon_binary64_val : machineEpsilon binary64 = (1 : ℝ) / 4503599627370496 := by
  rw [machineEpsilon_binary64]; norm_num

/-! ## Single cast relative error with concrete numbers -/

/-- f16 rounding: relative error ≤ ε/2 = 1/2048 ≈ 4.88e-4. -/
theorem f16_relative_error (x : ℝ)
    (hx : (2 : ℝ) ^ ((-14 : ℤ) + (11 : ℤ) - 1) ≤ |x|) :
    |x - roundNNE binary16 x| ≤ (1 : ℝ) / 2048 * |x| := by
  have h := roundNNE_error_rel binary16 hx
  rw [machineEpsilon_binary16_val] at h; linarith

/-- f32 rounding: relative error ≤ ε/2 = 1/16777216 ≈ 5.96e-8. -/
theorem f32_relative_error (x : ℝ)
    (hx : (2 : ℝ) ^ ((-126 : ℤ) + (24 : ℤ) - 1) ≤ |x|) :
    |x - roundNNE binary32 x| ≤ (1 : ℝ) / 16777216 * |x| := by
  have h := roundNNE_error_rel binary32 hx
  rw [machineEpsilon_binary32_val] at h; linarith

/-- bfloat16 rounding: relative error ≤ ε/2 = 1/256 ≈ 3.91e-3. -/
theorem bf16_relative_error (x : ℝ)
    (hx : (2 : ℝ) ^ ((-126 : ℤ) + (8 : ℤ) - 1) ≤ |x|) :
    |x - roundNNE bfloat16 x| ≤ (1 : ℝ) / 256 * |x| := by
  have h := roundNNE_error_rel bfloat16 hx
  rw [machineEpsilon_bfloat16_val] at h; linarith

/-- f64 rounding: relative error ≤ ε/2 = 1/9007199254740992 ≈ 1.11e-16. -/
theorem f64_relative_error (x : ℝ)
    (hx : (2 : ℝ) ^ ((-1022 : ℤ) + (53 : ℤ) - 1) ≤ |x|) :
    |x - roundNNE binary64 x| ≤ (1 : ℝ) / 9007199254740992 * |x| := by
  have h := roundNNE_error_rel binary64 hx
  rw [machineEpsilon_binary64_val] at h; linarith

/-! ## Two-step cast chain with concrete relative error -/

/-- f32 → f16 cast chain: relative error bound with concrete numbers.
    ≤ (ε₃₂ + ε₁₆)/2 + ε₁₆ε₃₂/4 ≈ 4.89e-4 * |x|. -/
theorem f32_to_f16_chain_error (x : ℝ)
    (hx32 : (2 : ℝ) ^ ((-126 : ℤ) + (24 : ℤ) - 1) ≤ |x|)
    (hx16 : (2 : ℝ) ^ ((-14 : ℤ) + (11 : ℤ) - 1) ≤ |roundNNE binary32 x|) :
    |x - roundNNE binary16 (roundNNE binary32 x)| ≤
      ((1 : ℝ) / 8388608 / 2 + (1 : ℝ) / 1024 / 2) * |x| +
      (1 : ℝ) / 1024 / 2 * ((1 : ℝ) / 8388608 / 2 * |x|) := by
  have h := cast_chain_two_bound binary16_refines_binary32 x
    (by show (binary32.β : ℝ) ^ _ ≤ _; convert hx32 using 2)
    (by show (binary16.β : ℝ) ^ _ ≤ _; convert hx16 using 2)
  rw [machineEpsilon_binary32_val, machineEpsilon_binary16_val] at h
  linarith

/-! ## Tactic: flean_numeric_bound -/

open Lean Meta Elab Tactic

/-- `flean_numeric_bound` tries to discharge a goal about rounding error
    by substituting concrete machineEpsilon values and using norm_num/linarith. -/
syntax (name := fleanNumericBound) "flean_numeric_bound" : tactic

@[tactic fleanNumericBound]
def evalFleanNumericBound : Tactic := fun _ => do
  let tactics ← `(tactic|
    first
    -- Try rewriting machineEpsilon to concrete values, then linarith
    | (simp only [machineEpsilon_binary16_val, machineEpsilon_bfloat16_val,
                  machineEpsilon_binary32_val, machineEpsilon_binary64_val,
                  machineEpsilon_binary16, machineEpsilon_bfloat16,
                  machineEpsilon_binary32, machineEpsilon_binary64] at *;
       linarith)
    -- Try with norm_num after rewriting
    | (simp only [machineEpsilon_binary16_val, machineEpsilon_bfloat16_val,
                  machineEpsilon_binary32_val, machineEpsilon_binary64_val] at *;
       norm_num at *; linarith)
    -- Direct application of concrete error theorems
    | exact f16_relative_error _ ‹_›
    | exact bf16_relative_error _ ‹_›
    | exact f32_relative_error _ ‹_›
    | exact f64_relative_error _ ‹_›
    -- Combine with chain bound
    | (have := cast_chain_two_bound _ _ ‹_› ‹_›;
       simp only [machineEpsilon_binary16_val, machineEpsilon_bfloat16_val,
                  machineEpsilon_binary32_val, machineEpsilon_binary64_val] at *;
       linarith)
  )
  evalTactic tactics

/-! ## Demos with concrete numbers -/

-- f16 relative error ≤ 1/2048 ≈ 4.88e-4
example (x : ℝ) (hx : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) ≤ |x|) :
    |x - roundNNE binary16 x| ≤ 1 / 2048 * |x| := by
  exact f16_relative_error x hx

-- f32 relative error ≤ 1/16777216 ≈ 5.96e-8
example (x : ℝ) (hx : (2 : ℝ) ^ ((-126 : ℤ) + 24 - 1) ≤ |x|) :
    |x - roundNNE binary32 x| ≤ 1 / 16777216 * |x| := by
  exact f32_relative_error x hx

-- bf16 relative error ≤ 1/256 ≈ 3.91e-3
example (x : ℝ) (hx : (2 : ℝ) ^ ((-126 : ℤ) + 8 - 1) ≤ |x|) :
    |x - roundNNE bfloat16 x| ≤ 1 / 256 * |x| := by
  exact bf16_relative_error x hx

-- f64 relative error ≤ 1/9007199254740992 ≈ 1.11e-16
example (x : ℝ) (hx : (2 : ℝ) ^ ((-1022 : ℤ) + 53 - 1) ≤ |x|) :
    |x - roundNNE binary64 x| ≤ 1 / 9007199254740992 * |x| := by
  exact f64_relative_error x hx

end Flean
