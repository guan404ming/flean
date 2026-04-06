import Flean.Bridge
import Flean.Core.ULP
import Flean.Arith.Spec
import Flean.Arith.Operations
import Flean.Arith.Sqrt
import Flean.Arith.FMA
import Flean.Arith.Conversions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Flean.Arith.Correctness

IEEE 754 arithmetic correctness: specification-level and bit-level.

## Architecture

Following Flocq's approach, we separate two concerns:

1. **Specification-level correctness**:
   Each operation is `round(exact_result)`. This is trivially correct
   by construction and gives us error bounds, monotonicity, etc. for free.

2. **Bit-level equivalence**:
   The `FloatBits` implementations (`mul`, `add`, etc.) compute the same
   result as the spec-level operations. This requires verifying `roundAndPack`.

-/

namespace Flean

/-! ## Section 1: Specification-level operations

These define the IEEE 754 semantics as `round(exact_result)` on ℝ.
Correctness is immediate. Error bounds follow from rounding properties. -/

/-! ### Correctness (trivial by definition) -/

theorem mulSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    mulSpec fmt mode a b = round fmt mode (a * b) := rfl

theorem addSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    addSpec fmt mode a b = round fmt mode (a + b) := rfl

theorem divSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    divSpec fmt mode a b = round fmt mode (a / b) := rfl

theorem sqrtSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a : ℝ) :
    sqrtSpec fmt mode a = round fmt mode (Real.sqrt a) := rfl

theorem fmaSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b c : ℝ) :
    fmaSpec fmt mode a b c = round fmt mode (a * b + c) := rfl

theorem castSpec_correct (srcFmt dstFmt : FloatFormat) (mode : RoundingMode) (x : ℝ) :
    castSpec srcFmt dstFmt mode x = round dstFmt mode x := rfl

theorem roundedFlagsSpec_correct (fmt : FloatFormat) (exact rounded : ℝ) :
    roundedFlagsSpec fmt exact rounded =
      { inexact := inexactFlag exact rounded
        overflow := overflowFlag fmt exact
        underflow := underflowFlag fmt exact rounded } := by
  simp [roundedFlagsSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]

theorem addFlagsSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    addFlagsSpec fmt mode a b = roundedFlagsSpec fmt (a + b) (addSpec fmt mode a b) := rfl

theorem mulFlagsSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    mulFlagsSpec fmt mode a b = roundedFlagsSpec fmt (a * b) (mulSpec fmt mode a b) := rfl

theorem divFlagsSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    divFlagsSpec fmt mode a b = roundedFlagsSpec fmt (a / b) (divSpec fmt mode a b) := rfl

theorem sqrtFlagsSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a : ℝ) :
    sqrtFlagsSpec fmt mode a = roundedFlagsSpec fmt (Real.sqrt a) (sqrtSpec fmt mode a) := rfl

theorem fmaFlagsSpec_correct (fmt : FloatFormat) (mode : RoundingMode) (a b c : ℝ) :
    fmaFlagsSpec fmt mode a b c = roundedFlagsSpec fmt (a * b + c) (fmaSpec fmt mode a b c) := rfl

theorem castFlagsSpec_correct (srcFmt dstFmt : FloatFormat) (mode : RoundingMode) (x : ℝ) :
    castFlagsSpec srcFmt dstFmt mode x = roundedFlagsSpec dstFmt x (castSpec srcFmt dstFmt mode x) := rfl

/-! ### Representability -/

theorem mulSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    isRepresentable fmt (mulSpec fmt mode a b) := by
  unfold mulSpec round
  cases mode <;> first
    | exact roundTZ_isRepresentable fmt _
    | exact roundDN_isRepresentable fmt _
    | exact roundUP_isRepresentable fmt _
    | exact roundNNE_isRepresentable fmt _
    | exact roundNNA_isRepresentable fmt _

theorem addSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    isRepresentable fmt (addSpec fmt mode a b) := by
  unfold addSpec round
  cases mode <;> first
    | exact roundTZ_isRepresentable fmt _
    | exact roundDN_isRepresentable fmt _
    | exact roundUP_isRepresentable fmt _
    | exact roundNNE_isRepresentable fmt _
    | exact roundNNA_isRepresentable fmt _

theorem divSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    isRepresentable fmt (divSpec fmt mode a b) := by
  unfold divSpec round
  cases mode <;> first
    | exact roundTZ_isRepresentable fmt _
    | exact roundDN_isRepresentable fmt _
    | exact roundUP_isRepresentable fmt _
    | exact roundNNE_isRepresentable fmt _
    | exact roundNNA_isRepresentable fmt _

theorem sqrtSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a : ℝ) :
    isRepresentable fmt (sqrtSpec fmt mode a) := by
  unfold sqrtSpec round
  cases mode <;> first
    | exact roundTZ_isRepresentable fmt _
    | exact roundDN_isRepresentable fmt _
    | exact roundUP_isRepresentable fmt _
    | exact roundNNE_isRepresentable fmt _
    | exact roundNNA_isRepresentable fmt _

theorem fmaSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b c : ℝ) :
    isRepresentable fmt (fmaSpec fmt mode a b c) := by
  unfold fmaSpec round
  cases mode <;> first
    | exact roundTZ_isRepresentable fmt _
    | exact roundDN_isRepresentable fmt _
    | exact roundUP_isRepresentable fmt _
    | exact roundNNE_isRepresentable fmt _
    | exact roundNNA_isRepresentable fmt _

/-! ### Rounding utilities -/

/-- If a result is representable, rounding in any mode is a no-op. -/
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

theorem round_zero (fmt : FloatFormat) (mode : RoundingMode) :
    round fmt mode 0 = 0 := by
  unfold round
  cases mode with
  | roundTowardZero => exact roundTZ_zero fmt
  | roundTowardPositive => exact roundUP_zero fmt
  | roundTowardNegative => exact roundDN_zero fmt
  | roundNearestTiesToEven => exact roundNNE_zero fmt
  | roundNearestTiesAway => exact roundNNA_zero fmt

/-- Rounding a FloatBits.toReal in any mode gives back the value. -/
theorem toReal_round_id {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal)
    (mode : RoundingMode) :
    round spec.toFormat mode f.toReal = f.toReal :=
  round_repr_id spec.toFormat mode (f.toReal_isRepresentable hfin)

/-! ### Idempotence: applying the same operation to a representable input -/

theorem mulSpec_repr_fixed (fmt : FloatFormat) (mode : RoundingMode) {a b : ℝ}
    (h : isRepresentable fmt (a * b)) :
    mulSpec fmt mode a b = a * b :=
  round_repr_id fmt mode h

theorem addSpec_repr_fixed (fmt : FloatFormat) (mode : RoundingMode) {a b : ℝ}
    (h : isRepresentable fmt (a + b)) :
    addSpec fmt mode a b = a + b :=
  round_repr_id fmt mode h

/-! ### Error bounds (inherited from rounding) -/

theorem mulSpec_error_le_ulp_TZ (fmt : FloatFormat) (a b : ℝ) :
    |mulSpec fmt .roundTowardZero a b - a * b| < ulp fmt (a * b) := by
  unfold mulSpec round; exact roundTZ_error_lt_ulp fmt _

theorem addSpec_error_le_ulp_TZ (fmt : FloatFormat) (a b : ℝ) :
    |addSpec fmt .roundTowardZero a b - (a + b)| < ulp fmt (a + b) := by
  unfold addSpec round; exact roundTZ_error_lt_ulp fmt _

theorem mulSpec_error_le_half_ulp_NNE (fmt : FloatFormat) (a b : ℝ) :
    |a * b - mulSpec fmt .roundNearestTiesToEven a b| ≤ ulp fmt (a * b) / 2 := by
  unfold mulSpec round; exact roundNNE_error_le_half_ulp fmt _

theorem addSpec_error_le_half_ulp_NNE (fmt : FloatFormat) (a b : ℝ) :
    |a + b - addSpec fmt .roundNearestTiesToEven a b| ≤ ulp fmt (a + b) / 2 := by
  unfold addSpec round; exact roundNNE_error_le_half_ulp fmt _

/-! ## Section 3: Structural lemmas -/

/-- The exact product of two (sigWidth+1)-bit significands fits in 2*(sigWidth+1) bits. -/
theorem mul_significand_bound {spec : BinarySpec} (m1 m2 : Nat)
    (h1 : m1 < 2 ^ (spec.sigWidth + 1)) (h2 : m2 < 2 ^ (spec.sigWidth + 1)) :
    m1 * m2 < 2 ^ (2 * (spec.sigWidth + 1)) := by
  calc m1 * m2 < 2 ^ (spec.sigWidth + 1) * 2 ^ (spec.sigWidth + 1) :=
        Nat.mul_lt_mul_of_lt_of_lt h1 h2
    _ = 2 ^ (2 * (spec.sigWidth + 1)) := by rw [← Nat.pow_add]; ring_nf

/-! ## Section 4: Special value correctness (unconditional) -/

/-- Multiplication: special returns none for finite non-zero inputs. -/
theorem mulSpecial_none_of_finite {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal)
    (hb : b.classify = .normal ∨ b.classify = .subnormal) :
    a.mulSpecial b = none := by
  unfold FloatBits.mulSpecial
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- Addition: special returns none for finite inputs. -/
theorem addSpecial_none_of_finite {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero)
    (hb : b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) :
    a.addSpecial b = none := by
  unfold FloatBits.addSpecial
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> simp [ha, hb]

/-- Division: special returns none for finite non-zero inputs. -/
theorem divSpecial_none_of_finite {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal)
    (hb : b.classify = .normal ∨ b.classify = .subnormal) :
    a.divSpecial b = none := by
  unfold FloatBits.divSpecial
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

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

/-! ## Section 5: Bit-level equivalence (specifications)

These state that the `FloatBits` implementations match the spec-level
operations at the value level. The primary arithmetic path now discharges
these equivalences directly against the spec-backed implementations. -/

/-- Bit-level multiplication matches spec-level multiplication. -/
def MulBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    let r := a.mul b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
      r.value.classify = .zero) →
    r.value.toReal = mulSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level addition matches spec-level addition. -/
def AddBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    let r := a.add b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
      r.value.classify = .zero) →
    r.value.toReal = addSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level cast matches destination-format rounding on reals. -/
def CastBitEquiv (srcSpec dstSpec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a : FloatBits srcSpec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    let r := a.cast (dstSpec := dstSpec) mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
      r.value.classify = .zero) →
    r.value.toReal = castSpec srcSpec.toFormat dstSpec.toFormat mode a.toReal

/-- Bit-level division matches spec-level division. -/
def DivBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    b.toReal ≠ 0 →
    let r := a.div b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
      r.value.classify = .zero) →
    r.value.toReal = divSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level square root matches spec-level square root. -/
def SqrtBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    ¬a.isNeg →
    let r := a.sqrt mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
      r.value.classify = .zero) →
    r.value.toReal = sqrtSpec spec.toFormat mode a.toReal

/-- Bit-level FMA matches spec-level FMA. -/
def FmaBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b c : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (c.classify = .normal ∨ c.classify = .subnormal ∨ c.classify = .zero) →
    let r := a.fma b c mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal ∨
      r.value.classify = .zero) →
    r.value.toReal = fmaSpec spec.toFormat mode a.toReal b.toReal c.toReal

/-- Bit-level addition flags match the spec-level flag definition. -/
def AddBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    (a.add b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level multiplication flags match the spec-level flag definition. -/
def MulBitFlagEquivFinite (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (a.mul b mode).flags = mulFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level multiplication flags match the spec-level flag definition (full finite coverage). -/
def MulBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    (a.mul b mode).flags = mulFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level division flags match the spec-level flag definition. -/
def DivBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    b.toReal ≠ 0 →
    (a.div b mode).flags = divFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level square-root flags match the spec-level flag definition. -/
def SqrtBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    ¬a.isNeg →
    (a.sqrt mode).flags = sqrtFlagsSpec spec.toFormat mode a.toReal

/-- Bit-level FMA flags match the spec-level flag definition. -/
def FmaBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b c : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (c.classify = .normal ∨ c.classify = .subnormal ∨ c.classify = .zero) →
    (a.fma b c mode).flags = fmaFlagsSpec spec.toFormat mode a.toReal b.toReal c.toReal

/-- Bit-level cast flags match the spec-level flag definition. -/
def CastBitFlagEquiv (srcSpec dstSpec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a : FloatBits srcSpec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (a.cast (dstSpec := dstSpec) mode).flags =
      castFlagsSpec srcSpec.toFormat dstSpec.toFormat mode a.toReal

private theorem ofRealOrInfSigned_toReal_of_finite {spec : BinarySpec} {x : ℝ} (negZero : Bool)
    (hfin : (FloatBits.ofRealOrInfSigned spec x negZero).classify = .normal ∨
      (FloatBits.ofRealOrInfSigned spec x negZero).classify = .subnormal ∨
      (FloatBits.ofRealOrInfSigned spec x negZero).classify = .zero) :
    (FloatBits.ofRealOrInfSigned spec x negZero).toReal = x := by
  by_cases hx : isBitRepresentable spec x
  · exact FloatBits.ofRealOrInfSigned_toReal_of_isBitRepresentable (spec := spec) negZero hx
  · have hinf := FloatBits.ofRealOrInfSigned_classify_of_not_isBitRepresentable
      (spec := spec) (x := x) negZero hx
    have : False := by
      rcases hfin with h | h | h
      · have : FloatClass.normal = FloatClass.infinite := h.symm.trans hinf
        cases this
      · have : FloatClass.subnormal = FloatClass.infinite := h.symm.trans hinf
        cases this
      · have : FloatClass.zero = FloatClass.infinite := h.symm.trans hinf
        cases this
    exact False.elim this

theorem castBitEquiv (srcSpec dstSpec : BinarySpec) (mode : RoundingMode) :
    CastBitEquiv srcSpec dstSpec mode := by
  intro a ha
  have hnot_nan : a.classify ≠ .nan := by
    rcases ha with h | h | h <;> simp [h]
  have hnot_inf : a.classify ≠ .infinite := by
    rcases ha with h | h | h <;> simp [h]
  dsimp [CastBitEquiv]
  unfold FloatBits.cast
  cases hclass : a.classify with
  | nan => cases (hnot_nan hclass)
  | infinite => cases (hnot_inf hclass)
  | zero =>
      let y := castSpec srcSpec.toFormat dstSpec.toFormat mode a.toReal
      intro hout
      simpa [y] using
        (ofRealOrInfSigned_toReal_of_finite (spec := dstSpec) (x := y) a.isNeg hout)
  | normal =>
      let y := castSpec srcSpec.toFormat dstSpec.toFormat mode a.toReal
      intro hout
      simpa [y] using
        (ofRealOrInfSigned_toReal_of_finite (spec := dstSpec) (x := y) a.isNeg hout)
  | subnormal =>
      let y := castSpec srcSpec.toFormat dstSpec.toFormat mode a.toReal
      intro hout
      simpa [y] using
        (ofRealOrInfSigned_toReal_of_finite (spec := dstSpec) (x := y) a.isNeg hout)

theorem castBitFlagEquiv (srcSpec dstSpec : BinarySpec) (mode : RoundingMode) :
    CastBitFlagEquiv srcSpec dstSpec mode := by
  intro a ha
  have hnot_nan : a.classify ≠ .nan := by
    rcases ha with h | h | h <;> simp [h]
  have hnot_inf : a.classify ≠ .infinite := by
    rcases ha with h | h | h <;> simp [h]
  unfold FloatBits.cast
  cases hclass : a.classify with
  | nan => cases (hnot_nan hclass)
  | infinite => cases (hnot_inf hclass)
  | zero =>
      simp [castFlagsSpec, roundedFlagsSpec, castSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]
  | normal =>
      simp [castFlagsSpec, roundedFlagsSpec, castSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]
  | subnormal =>
      simp [castFlagsSpec, roundedFlagsSpec, castSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]

theorem addBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    AddBitEquiv spec mode := by
  intro a b ha hb
  have hnone := addSpecial_none_of_finite a b ha hb
  dsimp [AddBitEquiv]
  unfold FloatBits.add
  rw [hnone]
  let y := addSpec spec.toFormat mode a.toReal b.toReal
  intro hout
  simpa [y] using
    (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) (addZeroSign a b mode) hout)

theorem addBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    AddBitFlagEquiv spec mode := by
  intro a b ha hb
  have hnone := addSpecial_none_of_finite a b ha hb
  unfold FloatBits.add
  rw [hnone]
  simp [addFlagsSpec, roundedFlagsSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]

theorem mulBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    MulBitEquiv spec mode := by
  intro a b ha hb
  dsimp [MulBitEquiv]
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · have hnone := mulSpecial_none_of_finite a b (Or.inl ha) (Or.inl hb)
    unfold FloatBits.mul
    rw [hnone]
    let y := mulSpec spec.toFormat mode a.toReal b.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) (mulZeroSign a b) hout)
  · have hnone := mulSpecial_none_of_finite a b (Or.inl ha) (Or.inr hb)
    unfold FloatBits.mul
    rw [hnone]
    let y := mulSpec spec.toFormat mode a.toReal b.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) (mulZeroSign a b) hout)
  · intro _
    unfold FloatBits.mul mulSpec
    have hb0 : b.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hb]
    by_cases hsgn : mulZeroSign a b
    · simp [FloatBits.mulSpecial, ha, hb, hb0, hsgn, round_zero, FloatBits.negZero_toReal]
    · simp [FloatBits.mulSpecial, ha, hb, hb0, hsgn, round_zero, FloatBits.posZero_toReal]
  · have hnone := mulSpecial_none_of_finite a b (Or.inr ha) (Or.inl hb)
    unfold FloatBits.mul
    rw [hnone]
    let y := mulSpec spec.toFormat mode a.toReal b.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) (mulZeroSign a b) hout)
  · have hnone := mulSpecial_none_of_finite a b (Or.inr ha) (Or.inr hb)
    unfold FloatBits.mul
    rw [hnone]
    let y := mulSpec spec.toFormat mode a.toReal b.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) (mulZeroSign a b) hout)
  · intro _
    unfold FloatBits.mul mulSpec
    have hb0 : b.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hb]
    by_cases hsgn : mulZeroSign a b
    · simp [FloatBits.mulSpecial, ha, hb, hb0, hsgn, round_zero, FloatBits.negZero_toReal]
    · simp [FloatBits.mulSpecial, ha, hb, hb0, hsgn, round_zero, FloatBits.posZero_toReal]
  · intro _
    unfold FloatBits.mul mulSpec
    have ha0 : a.toReal = 0 := by
      unfold FloatBits.toReal
      rw [ha]
    by_cases hsgn : mulZeroSign a b
    · simp [FloatBits.mulSpecial, ha, hb, ha0, hsgn, round_zero, FloatBits.negZero_toReal]
    · simp [FloatBits.mulSpecial, ha, hb, ha0, hsgn, round_zero, FloatBits.posZero_toReal]
  · intro _
    unfold FloatBits.mul mulSpec
    have ha0 : a.toReal = 0 := by
      unfold FloatBits.toReal
      rw [ha]
    by_cases hsgn : mulZeroSign a b
    · simp [FloatBits.mulSpecial, ha, hb, ha0, hsgn, round_zero, FloatBits.negZero_toReal]
    · simp [FloatBits.mulSpecial, ha, hb, ha0, hsgn, round_zero, FloatBits.posZero_toReal]
  · intro _
    unfold FloatBits.mul mulSpec
    have ha0 : a.toReal = 0 := by
      unfold FloatBits.toReal
      rw [ha]
    have hb0 : b.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hb]
    by_cases hsgn : mulZeroSign a b
    · simp [FloatBits.mulSpecial, ha, hb, ha0, hb0, hsgn, round_zero, FloatBits.negZero_toReal]
    · simp [FloatBits.mulSpecial, ha, hb, ha0, hb0, hsgn, round_zero, FloatBits.posZero_toReal]

theorem mulBitFlagEquivFinite (spec : BinarySpec) (mode : RoundingMode) :
    MulBitFlagEquivFinite spec mode := by
  intro a b ha hb
  have hnone := mulSpecial_none_of_finite a b ha hb
  unfold FloatBits.mul
  rw [hnone]
  simp [mulFlagsSpec, roundedFlagsSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]

theorem divBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    DivBitEquiv spec mode := by
  intro a b ha hb hb_ne
  have hnone := divSpecial_none_of_finite a b ha hb
  dsimp [DivBitEquiv]
  unfold FloatBits.div
  rw [hnone]
  let y := divSpec spec.toFormat mode a.toReal b.toReal
  intro hout
  simpa [y] using
    (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) (mulZeroSign a b) hout)

theorem divBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    DivBitFlagEquiv spec mode := by
  intro a b ha hb hb_ne
  have hnone := divSpecial_none_of_finite a b ha hb
  unfold FloatBits.div
  rw [hnone]
  simp [divFlagsSpec, roundedFlagsSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]

theorem sqrtBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    SqrtBitEquiv spec mode := by
  intro a ha hnonneg
  dsimp [SqrtBitEquiv]
  unfold FloatBits.sqrt
  rcases ha with h | h
  · simp [h, hnonneg]
    let y := sqrtSpec spec.toFormat mode a.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) false hout)
  · simp [h, hnonneg]
    let y := sqrtSpec spec.toFormat mode a.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite (spec := spec) (x := y) false hout)

theorem sqrtBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    SqrtBitFlagEquiv spec mode := by
  intro a ha hnonneg
  rcases ha with h | h
  · unfold FloatBits.sqrt
    simp [h, hnonneg, sqrtFlagsSpec, roundedFlagsSpec, sqrtSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]
  · unfold FloatBits.sqrt
    simp [h, hnonneg, sqrtFlagsSpec, roundedFlagsSpec, sqrtSpec, inexactFlag, overflowFlag, underflowFlag, eq_comm]

theorem fmaBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    FmaBitEquiv spec mode := by
  intro a b c ha hb hc
  dsimp [FmaBitEquiv]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc | hc
  all_goals
    unfold FloatBits.fma
    simp [ha, hb, hc]
    let y := fmaSpec spec.toFormat mode a.toReal b.toReal c.toReal
    intro hout
    simpa [y] using
      (ofRealOrInfSigned_toReal_of_finite
        (spec := spec) (x := y) (fmaZeroSign a.isNeg b.isNeg c.isNeg mode) hout)

theorem fmaBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    FmaBitFlagEquiv spec mode := by
  intro a b c ha hb hc
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc | hc
  all_goals
    unfold FloatBits.fma
    simp [ha, hb, hc, fmaFlagsSpec, roundedFlagsSpec, fmaSpec,
      inexactFlag, overflowFlag, underflowFlag, eq_comm]

end Flean
