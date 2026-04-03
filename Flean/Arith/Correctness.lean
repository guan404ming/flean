import Flean.Bridge
import Flean.Arith.Operations

/-!
# Flean.Arith.Correctness

IEEE 754 arithmetic correctness specifications.

The IEEE 754 standard requires that each arithmetic operation computes
the exact mathematical result and then rounds it to the target format.
This module states and proves properties that connect bit-level operations
to the real-valued rounding model.

## Approach

Full verification of `roundAndPack` (bit manipulation, GRS logic, overflow/underflow)
is a substantial effort. We take a layered approach:

1. **Specification layer**: State what IEEE 754 requires as `Prop`.
2. **Bridge properties**: Prove that representable values are fixed points of rounding.
3. **Special value correctness**: Prove special-case handling (NaN, Inf, zero) is correct.

This provides a framework for incremental verification of the bit-level implementations.
-/

namespace Flean

/-! ## IEEE 754 correctness specification

The fundamental IEEE 754 contract: for an operation ⊕ with mathematical counterpart op,
  (a ⊕ b).toReal = round(op(a.toReal, b.toReal))
for finite inputs where the result doesn't overflow. -/

/-- The IEEE 754 correctness property for a binary operation. -/
def IsCorrectBinOp {spec : BinarySpec} (op : ℝ → ℝ → ℝ)
    (impl : FloatBits spec → FloatBits spec → RoundingMode → OpResult (FloatBits spec))
    (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    let r := impl a b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = round spec.toFormat mode (op a.toReal b.toReal)

/-- The IEEE 754 correctness property for a unary operation. -/
def IsCorrectUnaryOp {spec : BinarySpec} (op : ℝ → ℝ)
    (impl : FloatBits spec → RoundingMode → OpResult (FloatBits spec))
    (mode : RoundingMode) : Prop :=
  ∀ (a : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    let r := impl a mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = round spec.toFormat mode (op a.toReal)

/-! ## Key structural property: roundAndPack specification

Rather than fully verifying roundAndPack, we state what it must satisfy. -/

/-- Specification: roundAndPack produces a representable result. -/
def RoundAndPackSpec (spec : BinarySpec) : Prop :=
  ∀ (mode : RoundingMode) (isNeg : Bool) (rawExp : Int) (rawSig : Nat),
    let r := @roundAndPack spec mode isNeg rawExp rawSig
    r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
    r.value.classify = .zero ∨ r.value.classify = .infinite

/-- The exact-input case: when GRS bits are zero, roundAndPack preserves the value. -/
theorem roundAndPack_exact_preserves {spec : BinarySpec} (mode : RoundingMode) (isNeg : Bool)
    (rawExp : Int) (rawSig : Nat)
    (hexp_pos : 1 ≤ rawExp) (hexp_max : rawExp < 2 ^ spec.expWidth - 1)
    (hsig : rawSig < 2 ^ (spec.sigWidth + 1)) :
    (roundAndPack mode isNeg rawExp rawSig).value =
      FloatBits.fromFields
        (if isNeg then BitVec.ofNat 1 1 else BitVec.ofNat 1 0)
        (BitVec.ofNat spec.expWidth rawExp.toNat)
        (BitVec.ofNat spec.sigWidth (rawSig % 2 ^ spec.sigWidth)) :=
  roundAndPack_normal_exact mode isNeg rawExp rawSig hexp_pos hexp_max hsig

/-! ## Multiplication correctness (partial)

For multiplication, the exact product m1 * m2 has at most 2p bits.
This means the intermediate result before rounding is exact. -/

/-- The exact product of two (sigWidth+1)-bit significands fits in 2*(sigWidth+1) bits. -/
theorem mul_significand_bound {spec : BinarySpec} (m1 m2 : Nat)
    (h1 : m1 < 2 ^ (spec.sigWidth + 1)) (h2 : m2 < 2 ^ (spec.sigWidth + 1)) :
    m1 * m2 < 2 ^ (2 * (spec.sigWidth + 1)) := by
  calc m1 * m2 < 2 ^ (spec.sigWidth + 1) * 2 ^ (spec.sigWidth + 1) :=
        Nat.mul_lt_mul_of_lt_of_lt h1 h2
    _ = 2 ^ (2 * (spec.sigWidth + 1)) := by rw [← Nat.pow_add]; ring_nf

/-! ## Rounding-then-cast equivalence

A key IEEE 754 property: computing in a wider format then rounding to
the target format gives the same result as computing directly. -/

/-- If a result is representable in fmt1, rounding in fmt1 is a no-op. -/
theorem round_repr_id (fmt : FloatFormat) (mode : RoundingMode) {x : ℝ}
    (hx : isRepresentable fmt x) :
    round fmt mode x = x := by
  unfold round
  cases mode with
  | roundTowardZero => exact roundTZ_repr_fixed fmt hx
  | roundTowardPositive => exact roundUP_repr_fixed fmt hx
  | roundTowardNegative => exact roundDN_repr_fixed fmt hx
  | roundNearestTiesToEven => exact roundNNE_repr_fixed fmt hx
  | roundNearestTiesAway => exact roundNNA_repr_fixed fmt hx

/-- Rounding a representable value in any mode gives back the value. -/
theorem toReal_round_id {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal)
    (mode : RoundingMode) :
    round spec.toFormat mode f.toReal = f.toReal :=
  round_repr_id spec.toFormat mode (f.toReal_isRepresentable hfin)

end Flean
