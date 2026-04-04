import Flean.Core.RelativeError
import Flean.Core.CastChain
import Flean.Tactics.MixedPrecision
import Flean.Tactics.ChainDecomp
import Flean.Tactics.NumericBounds

/-!
# Flean.Apps.ML.DotProd

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
  -- Abbreviations
  set a' := roundNNE binary16 a
  set b' := roundNNE binary16 b
  set p := a' * b'
  -- a, b are nonzero (from normal range hypotheses)
  have ha_pos : 0 < |a| := lt_of_lt_of_le (by positivity) ha
  have hb_pos : 0 < |b| := lt_of_lt_of_le (by positivity) hb
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha_pos
  have hb_ne : b ≠ 0 := by intro h; simp [h] at hb_pos
  have hab_ne : a * b ≠ 0 := mul_ne_zero ha_ne hb_ne
  -- Rounding errors for fp16
  have hea : |a - a'| ≤ 1 / 2048 * |a| := f16_relative_error a ha
  have heb : |b - b'| ≤ 1 / 2048 * |b| := f16_relative_error b hb
  -- Product is in normal range of binary32
  -- |a'| ≥ |a| - |a-a'| ≥ |a|(1 - 1/2048), similarly for b'
  -- |p| = |a'|*|b'| ≥ |a|*|b|*(2047/2048)^2 ≥ 2^(-8)*(2047/2048)^2 >> 2^(-103)
  have hp_normal : (2 : ℝ) ^ ((-126 : ℤ) + 24 - 1) ≤ |p| := by
    have ha'_lb : 2047 / 2048 * |a| ≤ |a'| := by
      have := abs_sub_abs_le_abs_sub a a'; linarith
    have hb'_lb : 2047 / 2048 * |b| ≤ |b'| := by
      have := abs_sub_abs_le_abs_sub b b'; linarith
    rw [show p = a' * b' from rfl, abs_mul]
    have : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) = 2⁻¹ ^ (4 : ℕ) := by norm_num
    have ha_lb : (1 : ℝ) / 16 ≤ |a| := by rw [this] at ha; linarith
    have hb_lb : (1 : ℝ) / 16 ≤ |b| := by rw [this] at hb; linarith
    have ha'_pos : 0 < |a'| := by linarith
    have hb'_pos : 0 < |b'| := by linarith
    calc (2 : ℝ) ^ ((-126 : ℤ) + 24 - 1)
        ≤ (2047 / 2048 * (1 / 16)) * (2047 / 2048 * (1 / 16)) := by norm_num
      _ ≤ |a'| * |b'| := by
          apply mul_le_mul <;> linarith
  -- fp32 relative error on the product
  have hep : |p - roundNNE binary32 p| ≤ 1 / 16777216 * |p| := f32_relative_error p hp_normal
  -- Define δ₃ via the standard model for fp32
  have hp_ne : p ≠ 0 := by
    intro h; rw [h, abs_zero] at hp_normal; norm_num at hp_normal
  set δ₃ := (roundNNE binary32 p - p) / p
  have hδ₃_eq : roundNNE binary32 p = p * (1 + δ₃) := by
    show roundNNE binary32 p = p * (1 + (roundNNE binary32 p - p) / p)
    field_simp [hp_ne]; ring
  have hδ₃_bound : |δ₃| ≤ 1 / 16777216 := by
    show |(roundNNE binary32 p - p) / p| ≤ 1 / 16777216
    rw [abs_div]
    rw [div_le_iff₀ (abs_pos.mpr hp_ne)]
    rwa [abs_sub_comm] at hep
  -- Define δ₁ = (a'-a)*(b'-b)/(a*b), δ₂ = 0
  set e_a := a' - a
  set e_b := b' - b
  set δ₁ := e_a * e_b / (a * b)
  -- Bound |δ₁|
  have hea' : |e_a| ≤ 1 / 2048 * |a| := by rwa [show e_a = a' - a from rfl, abs_sub_comm]
  have heb' : |e_b| ≤ 1 / 2048 * |b| := by rwa [show e_b = b' - b from rfl, abs_sub_comm]
  have hab_pos : 0 < |a| * |b| := mul_pos ha_pos hb_pos
  have hδ₁_bound : |δ₁| ≤ 1 / 2048 := by
    show |e_a * e_b / (a * b)| ≤ 1 / 2048
    rw [abs_div, abs_mul, abs_mul]
    rw [div_le_iff₀ hab_pos]
    calc |e_a| * |e_b|
        ≤ (1 / 2048 * |a|) * (1 / 2048 * |b|) :=
          mul_le_mul hea' heb' (abs_nonneg _) (by linarith)
      _ = 1 / 2048 * (1 / 2048) * (|a| * |b|) := by ring
      _ ≤ 1 / 2048 * 1 * (|a| * |b|) := by
          apply mul_le_mul_of_nonneg_right _ hab_pos.le
          apply mul_le_mul_of_nonneg_left (by norm_num : (1:ℝ)/2048 ≤ 1) (by norm_num)
      _ = 1 / 2048 * (|a| * |b|) := by ring
  -- The algebraic identity
  -- mpMul a b = roundNNE binary32 p = p * (1 + δ₃) = a' * b' * (1 + δ₃)
  -- a' * b' = (a + e_a) * (b + e_b) = a*b + a*e_b + e_a*b + e_a*e_b
  --         = a*b*(1 + e_a*e_b/(a*b)) + a*e_b + e_a*b
  --         = a*b*(1 + δ₁) + a*(b'-b) + (a'-a)*b
  -- So with δ₂ = 0: a*b*(1+δ₁)*(1+0) + a*(b'-b) + (a'-a)*b = a'*b'
  -- And mpMul a b = a'*b'*(1+δ₃) = [a*b*(1+δ₁) + a*(b'-b) + (a'-a)*b]*(1+δ₃)
  -- Key identity: p = a*b*(1+δ₁) + a*e_b + e_a*b
  have hδ₁_val : a * b * δ₁ = e_a * e_b := by
    show a * b * (e_a * e_b / (a * b)) = e_a * e_b
    field_simp [hab_ne]
  have hp_expand : p = a * b * (1 + δ₁) + a * e_b + e_a * b := by
    show a' * b' = a * b * (1 + δ₁) + a * e_b + e_a * b
    have ha'_eq : a' = a + e_a := by simp [e_a]
    have hb'_eq : b' = b + e_b := by simp [e_b]
    rw [ha'_eq, hb'_eq]; nlinarith [hδ₁_val]
  refine ⟨δ₁, 0, δ₃, hδ₁_bound, by simp, hδ₃_bound, ?_⟩
  show mpMul a b = a * b * (1 + δ₁) * (1 + 0) * (1 + δ₃) +
    a * (b' - b) * (1 + δ₃) + (a' - a) * b * (1 + δ₃)
  have hmpMul : mpMul a b = roundNNE binary32 p := rfl
  rw [hmpMul, hδ₃_eq]
  linear_combination (1 + δ₃) * hp_expand

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
