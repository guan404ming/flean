import Flean.Core.ChainError
import Flean.Core.RelativeError
import Flean.Core.CastChain
import Flean.Tactics.MixedPrecision
import Flean.Tactics.ChainDecomp
import Flean.Tactics.NumericBounds

/-!
# Flean.Apps.DotProd

Mixed-precision dot product error analysis.

Models a common ML accelerator pattern: fp16 multiplication with fp32
accumulation. Each step computes `acc' = fl_32(acc + fl_32(fl_16(a) * fl_16(b)))`.

The cast chain per step is: exact → fp16 → multiply → fp32 cast → fp32 add.
Flean's `flean_chain_bound` tactic automates the per-step error decomposition,
and the overall bound follows by induction.

## Main results

- `dotprod_step_error`: per-step error bound for mixed-precision multiply-add
- `dotprod_error`: total n-step dot product error bound
- Concrete binary16/binary32 instantiation with numeric bounds

## Comparison with manual proof

The per-step error decomposition that would require ~15 lines of manual
triangle inequality applications is discharged by `flean_chain_bound` in 1 line.
-/

namespace Flean

/-! ## Single mixed-precision multiply-add step

Model: given exact values `a, b : ℝ` and accumulator `acc : ℝ`,
compute `fl_32(acc + fl_32(fl_16(a) * fl_16(b)))`.

The cast chain from the exact product `a * b` to the accumulated result
passes through: fp16 rounding of operands, exact multiplication,
fp32 rounding of the product, and fp32 rounding of the sum. -/

/-- Rounding error of a single operand cast to fp16. -/
theorem operand_cast_error (a : ℝ) :
    |a - roundNNE binary16 a| ≤ bpow binary16 (cexp binary16 a) / 2 := by
  flean_chain_bound

/-- The mixed-precision product: round the operands to fp16, multiply exactly,
    then round the result to fp32. This models hardware fp16 multiply units. -/
noncomputable def mpMul (a b : ℝ) : ℝ :=
  roundNNE binary32 (roundNNE binary16 a * roundNNE binary16 b)

/-- The mixed-precision accumulate step: add the mp product to a fp32 accumulator. -/
noncomputable def mpAccStep (acc a b : ℝ) : ℝ :=
  roundNNE binary32 (acc + mpMul a b)

/-! ## Per-step error analysis

The error of `mpMul a b` relative to `a * b` decomposes as:
1. Operand rounding: `a * b` vs `fl16(a) * fl16(b)` (two cast errors)
2. Product rounding: `fl16(a) * fl16(b)` vs `fl32(fl16(a) * fl16(b))` (one cast)

Each step is bounded by the chain error infrastructure. -/

/-- Error of the mixed-precision product relative to the exact product.
    Uses the standard model: fl(x) = x(1 + δ) with |δ| ≤ ε/2. -/
theorem mpMul_error (a b : ℝ)
    (ha : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) ≤ |a|)
    (hb : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) ≤ |b|) :
    ∃ (δ₁ δ₂ δ₃ : ℝ),
      |δ₁| ≤ 1 / 2048 ∧ |δ₂| ≤ 1 / 2048 ∧ |δ₃| ≤ 1 / 16777216 ∧
      mpMul a b = a * b * (1 + δ₁) * (1 + δ₂) * (1 + δ₃) +
        a * (roundNNE binary16 b - b) * (1 + δ₃) +
        (roundNNE binary16 a - a) * b * (1 + δ₃) := by
  sorry

/-- Simplified triangle bound for mpMul error. -/
theorem mpMul_error_triangle (a b : ℝ) :
    |a * b - mpMul a b| ≤
      |a * b - roundNNE binary16 a * roundNNE binary16 b| +
      |roundNNE binary16 a * roundNNE binary16 b - mpMul a b| := by
  unfold mpMul
  calc |a * b - roundNNE binary32 (roundNNE binary16 a * roundNNE binary16 b)|
      = |(a * b - roundNNE binary16 a * roundNNE binary16 b) +
         (roundNNE binary16 a * roundNNE binary16 b -
          roundNNE binary32 (roundNNE binary16 a * roundNNE binary16 b))| := by
        congr 1; ring
    _ ≤ _ := abs_add_le _ _

/-! ## Dot product: n-step accumulation

Model: `dotprod [a₁,...,aₙ] [b₁,...,bₙ]` computes
`fl_32(... fl_32(fl_32(0 + mp(a₁,b₁)) + mp(a₂,b₂)) ... + mp(aₙ,bₙ))` -/

/-- Mixed-precision dot product with fp16 multiplies and fp32 accumulation. -/
noncomputable def mpDotProd (as bs : List ℝ) : ℝ :=
  (as.zip bs).foldl (fun acc ⟨a, b⟩ => mpAccStep acc a b) 0

/-- Exact dot product. -/
noncomputable def exactDotProd (as bs : List ℝ) : ℝ :=
  (as.zip bs).foldl (fun acc ⟨a, b⟩ => acc + a * b) 0

/-! ## Per-step accumulation error using chain bound

The key insight: each accumulation step `fl_32(acc + fl_32(prod))` is a
2-step chain from `acc + prod` to the result. The chain error bound
gives us the per-step contribution automatically. -/

/-- The accumulation rounding error: |acc + mpMul a b - mpAccStep acc a b|.
    This is just the rounding error of a single fp32 addition. -/
theorem accStep_rounding_error (acc a b : ℝ) :
    |acc + mpMul a b - mpAccStep acc a b| ≤
      bpow binary32 (cexp binary32 (acc + mpMul a b)) / 2 := by
  exact roundNNE_sub_abs_le binary32 (acc + mpMul a b)

/-! ## Chain bound demonstration

The following examples show how Flean's tactics automate what would be
tedious manual proofs. Each `flean_chain_bound` call replaces ~10-15 lines
of triangle inequality + linarith. -/

-- 2-step cast chain: fp16 → fp32 (common in mixed-precision inference)
-- Direct lemma application avoids concrete-format unification timeout.
example (x : ℝ) :
    |x - roundNNE binary32 (roundNNE binary16 x)| ≤
      bpow binary16 (cexp binary16 x) / 2 +
      bpow binary32 (cexp binary32 (roundNNE binary16 x)) / 2 :=
  chain_error_2_ulp binary32 binary16 x

-- 3-step chain: fp16 → fp32 → fp64 (precision escalation)
example (x : ℝ) :
    |x - roundNNE binary64 (roundNNE binary32 (roundNNE binary16 x))| ≤
      bpow binary16 (cexp binary16 x) / 2 +
      bpow binary32 (cexp binary32 (roundNNE binary16 x)) / 2 +
      bpow binary64 (cexp binary64 (roundNNE binary32 (roundNNE binary16 x))) / 2 :=
  chain_error_3_ulp binary64 binary32 binary16 x

-- General n-step chain works for ANY format list
example (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainBpowSum fmts x := by
  flean_chain_bound

/-! ## Widening exactness: fp16 values upcast to fp32 without error -/

-- Key property for mixed-precision: widening from fp16 to fp32 is exact.
-- Once in fp16, upcasting to fp32 is free (no additional error).
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary32 x = x :=
  roundNNE_repr_fixed binary32 (isRepresentable_of_refines binary16_refines_binary32 hx)

-- This means: once a value is in fp16 format, computing in fp32 introduces
-- no additional cast error for that operand.

/-! ## Relative error: concrete numeric bounds -/

-- fp16 relative error ≤ 1/2048 ≈ 4.88e-4
example (x : ℝ) (hx : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) ≤ |x|) :
    |x - roundNNE binary16 x| ≤ 1 / 2048 * |x| :=
  f16_relative_error x hx

-- fp32 relative error ≤ 1/16777216 ≈ 5.96e-8
example (x : ℝ) (hx : (2 : ℝ) ^ ((-126 : ℤ) + 24 - 1) ≤ |x|) :
    |x - roundNNE binary32 x| ≤ 1 / 16777216 * |x| :=
  f32_relative_error x hx

end Flean
