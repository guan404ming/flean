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

private theorem round_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (x : ℝ) :
    isRepresentable fmt (round fmt mode x) := by
  unfold round
  cases mode <;> first
    | exact roundTZ_isRepresentable fmt _
    | exact roundDN_isRepresentable fmt _
    | exact roundUP_isRepresentable fmt _
    | exact roundNNE_isRepresentable fmt _
    | exact roundNNA_isRepresentable fmt _

theorem mulSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    isRepresentable fmt (mulSpec fmt mode a b) := by
  simpa [mulSpec] using round_isRepresentable fmt mode (a * b)

theorem addSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    isRepresentable fmt (addSpec fmt mode a b) := by
  simpa [addSpec] using round_isRepresentable fmt mode (a + b)

theorem divSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    isRepresentable fmt (divSpec fmt mode a b) := by
  simpa [divSpec] using round_isRepresentable fmt mode (a / b)

theorem sqrtSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a : ℝ) :
    isRepresentable fmt (sqrtSpec fmt mode a) := by
  simpa [sqrtSpec] using round_isRepresentable fmt mode (Real.sqrt a)

theorem fmaSpec_isRepresentable (fmt : FloatFormat) (mode : RoundingMode) (a b c : ℝ) :
    isRepresentable fmt (fmaSpec fmt mode a b c) := by
  simpa [fmaSpec] using round_isRepresentable fmt mode (a * b + c)

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
  exact round_repr_id fmt mode (zero_isRepresentable fmt)

/-- Rounding a FloatBits.toReal in any mode gives back the value. -/
theorem toReal_round_id {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal)
    (mode : RoundingMode) :
    round spec.toFormat mode f.toReal = f.toReal :=
  round_repr_id spec.toFormat mode (f.toReal_isRepresentable hfin)

theorem toReal_isRepresentable_of_finiteOrZero {spec : BinarySpec} (f : FloatBits spec)
    (hfin :
      f.classify = .normal ∨ f.classify = .subnormal ∨ f.classify = .zero) :
    isRepresentable spec.toFormat f.toReal := by
  rcases hfin with hnorm | hsub | hzero
  · exact f.toReal_isRepresentable (Or.inl hnorm)
  · exact f.toReal_isRepresentable (Or.inr hsub)
  · unfold FloatBits.toReal
    rw [hzero]
    exact zero_isRepresentable spec.toFormat

/-! ### Idempotence: applying the same operation to a representable input -/

theorem mulSpec_repr_fixed (fmt : FloatFormat) (mode : RoundingMode) {a b : ℝ}
    (h : isRepresentable fmt (a * b)) :
    mulSpec fmt mode a b = a * b :=
  round_repr_id fmt mode h

theorem addSpec_repr_fixed (fmt : FloatFormat) (mode : RoundingMode) {a b : ℝ}
    (h : isRepresentable fmt (a + b)) :
    addSpec fmt mode a b = a + b :=
  round_repr_id fmt mode h

theorem divSpec_repr_fixed (fmt : FloatFormat) (mode : RoundingMode) {a b : ℝ}
    (h : isRepresentable fmt (a / b)) :
    divSpec fmt mode a b = a / b :=
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

/-- `roundAndPack` preserves exact normalized payloads in-range. -/
theorem roundAndPack_exact_preserves {spec : BinarySpec} (mode : RoundingMode) (isNeg : Bool)
    (rawExp : Int) (rawSig : Nat)
    (hexp_pos : 1 ≤ rawExp)
    (hexp_max : rawExp < 2 ^ spec.expWidth - 1)
    (hsig_hi : rawSig < 2 ^ (spec.sigWidth + 1)) :
    (roundAndPack (spec := spec) mode isNeg rawExp rawSig).value =
      FloatBits.fromFields
        (if isNeg then BitVec.ofNat 1 1 else BitVec.ofNat 1 0)
        (BitVec.ofNat spec.expWidth rawExp.toNat)
        (BitVec.ofNat spec.sigWidth (rawSig % 2 ^ spec.sigWidth)) :=
  roundAndPack_normal_exact mode isNeg rawExp rawSig hexp_pos hexp_max hsig_hi

/-! ## Section 5: Bit-level equivalence (specifications)

These predicates capture spec-level equivalence goals. For the rewired
bit-kernel arithmetic path, we currently discharge executable kernel-flow
characterizations below and keep these predicates available as explicit
assumptions for clients that still need spec-level refinements. -/

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
    (a.div b mode).flags = divFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Full IEEE-style add value spec (special path + finite kernel path), expressed on `IEEEValue`. -/
noncomputable def addIEEEValueSpec (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec) : IEEEValue :=
  match a.addSpecial b with
  | some res => res.value.toIEEEValue
  | none =>
      match a.classify, b.classify with
      | .zero, .zero =>
          (if addZeroSign a b mode then FloatBits.negZero spec else FloatBits.posZero spec).toIEEEValue
      | .zero, _ => b.toIEEEValue
      | _, .zero => a.toIEEEValue
      | _, _ =>
          let (x, y) := if FloatBits.finiteMagGE a b then (a, b) else (b, a)
          if x.isNeg == y.isNeg then
            (x.addFiniteSameSign y mode).value.toIEEEValue
          else
            (x.addFiniteOppositeSign y mode).value.toIEEEValue

/-- Full IEEE-style add flags spec (special path + finite kernel path). -/
noncomputable def addIEEEFlagsSpec (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec) : ExceptionFlags :=
  match a.addSpecial b with
  | some res => res.flags
  | none =>
      match a.classify, b.classify with
      | .zero, .zero => {}
      | .zero, _ => {}
      | _, .zero => {}
      | _, _ =>
          let (x, y) := if FloatBits.finiteMagGE a b then (a, b) else (b, a)
          if x.isNeg == y.isNeg then
            (x.addFiniteSameSign y mode).flags
          else
            (x.addFiniteOppositeSign y mode).flags

/-- Full IEEE-style mul value spec (special path + finite kernel path), expressed on `IEEEValue`. -/
noncomputable def mulIEEEValueSpec (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec) : IEEEValue :=
  match a.mulSpecial b with
  | some res => res.value.toIEEEValue
  | none => (a.mulFinite b mode).value.toIEEEValue

/-- Full IEEE-style mul flags spec (special path + finite kernel path). -/
noncomputable def mulIEEEFlagsSpec (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec) : ExceptionFlags :=
  match a.mulSpecial b with
  | some res => res.flags
  | none => (a.mulFinite b mode).flags

/-- Full IEEE-style div value spec (special path + finite kernel path), expressed on `IEEEValue`. -/
noncomputable def divIEEEValueSpec (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec) : IEEEValue :=
  match a.divSpecial b with
  | some res => res.value.toIEEEValue
  | none => (a.divFinite b mode).value.toIEEEValue

/-- Full IEEE-style div flags spec (special path + finite kernel path). -/
noncomputable def divIEEEFlagsSpec (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec) : ExceptionFlags :=
  match a.divSpecial b with
  | some res => res.flags
  | none => (a.divFinite b mode).flags

/-- Add operation matches the full IEEE-style value decomposition spec. -/
theorem addIEEEValueEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.add b mode).value.toIEEEValue = addIEEEValueSpec spec mode a b := by
  intro a b
  cases hsp : a.addSpecial b with
  | some res =>
      simp [FloatBits.add, addIEEEValueSpec, hsp]
  | none =>
      cases ha : a.classify <;> cases hb : b.classify <;>
        simp [FloatBits.add, addIEEEValueSpec, hsp, ha, hb] <;> aesop

/-- Add operation flags match the full IEEE-style flags decomposition spec. -/
theorem addIEEEFlagsEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.add b mode).flags = addIEEEFlagsSpec spec mode a b := by
  intro a b
  cases hsp : a.addSpecial b with
  | some res =>
      simp [FloatBits.add, addIEEEFlagsSpec, hsp]
  | none =>
      cases ha : a.classify <;> cases hb : b.classify <;>
        simp [FloatBits.add, addIEEEFlagsSpec, hsp, ha, hb] <;> aesop

/-- Mul operation matches the full IEEE-style value decomposition spec. -/
theorem mulIEEEValueEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.mul b mode).value.toIEEEValue = mulIEEEValueSpec spec mode a b := by
  intro a b
  unfold mulIEEEValueSpec FloatBits.mul
  cases hsp : a.mulSpecial b with
  | some res =>
      simp
  | none =>
      simp

/-- Mul operation flags match the full IEEE-style flags decomposition spec. -/
theorem mulIEEEFlagsEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.mul b mode).flags = mulIEEEFlagsSpec spec mode a b := by
  intro a b
  unfold mulIEEEFlagsSpec FloatBits.mul
  cases hsp : a.mulSpecial b with
  | some res =>
      simp
  | none =>
      simp

/-- Div operation matches the full IEEE-style value decomposition spec. -/
theorem divIEEEValueEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.div b mode).value.toIEEEValue = divIEEEValueSpec spec mode a b := by
  intro a b
  unfold divIEEEValueSpec FloatBits.div
  cases hsp : a.divSpecial b with
  | some res =>
      simp
  | none =>
      simp

/-- Div operation flags match the full IEEE-style flags decomposition spec. -/
theorem divIEEEFlagsEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.div b mode).flags = divIEEEFlagsSpec spec mode a b := by
  intro a b
  unfold divIEEEFlagsSpec FloatBits.div
  cases hsp : a.divSpecial b with
  | some res =>
      simp
  | none =>
      simp

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

/-- Finite-path kernel result selected by `FloatBits.add` once specials are ruled out. -/
noncomputable def addFiniteKernelResult {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode) : OpResult (FloatBits spec) :=
  match a.classify, b.classify with
  | .zero, .zero =>
      { value := if addZeroSign a b mode then FloatBits.negZero spec else FloatBits.posZero spec }
  | .zero, _ => { value := b }
  | _, .zero => { value := a }
  | _, _ =>
      let (x, y) := if FloatBits.finiteMagGE a b then (a, b) else (b, a)
      if x.isNeg == y.isNeg then
        x.addFiniteSameSign y mode
      else
        x.addFiniteOppositeSign y mode

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
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
      (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
      a.add b mode = addFiniteKernelResult a b mode := by
  intro a b ha hb
  have hnone := addSpecial_none_of_finite a b ha hb
  unfold FloatBits.add
  rw [hnone]
  rfl

theorem addBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
      (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
      (a.add b mode).flags = (addFiniteKernelResult a b mode).flags := by
  intro a b ha hb
  simpa using congrArg (fun r => r.flags) (addBitEquiv spec mode a b ha hb)

/-- Add-kernel real-value obligation needed to lift to `AddBitEquiv`. -/
def AddFiniteKernelToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    ((addFiniteKernelResult a b mode).value.classify = .normal ∨
      (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
      (addFiniteKernelResult a b mode).value.classify = .zero) →
    (addFiniteKernelResult a b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

theorem addBitEquiv_of_addFiniteKernelToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelToSpec spec mode) :
    AddBitEquiv spec mode := by
  intro a b ha hb
  dsimp [AddBitEquiv]
  intro hout
  have himpl := addBitEquiv spec mode a b ha hb
  have hout' :
      ((addFiniteKernelResult a b mode).value.classify = .normal ∨
        (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
        (addFiniteKernelResult a b mode).value.classify = .zero) := by
    simpa [himpl] using hout
  calc
    (a.add b mode).value.toReal = (addFiniteKernelResult a b mode).value.toReal := by
      simp [himpl]
    _ = addSpec spec.toFormat mode a.toReal b.toReal := hkernel a b ha hb hout'

/-- Add-kernel flag obligation needed to lift to `AddBitFlagEquiv`. -/
def AddFiniteKernelFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Remaining non-zero/non-zero value obligation for `addFiniteKernelResult`. -/
def AddFiniteKernelFiniteFiniteToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((addFiniteKernelResult a b mode).value.classify = .normal ∨
      (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
      (addFiniteKernelResult a b mode).value.classify = .zero) →
    (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal

/-- Remaining non-zero/non-zero flag obligation for `addFiniteKernelResult`. -/
def AddFiniteKernelFiniteFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered same-sign value obligation for finite/non-zero addition kernel. -/
def AddFiniteSameSignToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    ((a.addFiniteSameSign b mode).value.classify = .normal ∨
      (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
      (a.addFiniteSameSign b mode).value.classify = .zero) →
    (a.addFiniteSameSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign value obligation for finite/non-zero addition kernel. -/
def AddFiniteOppositeSignToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .zero) →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered same-sign flag obligation for finite/non-zero addition kernel. -/
def AddFiniteSameSignFlagsToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.addFiniteSameSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign flag obligation for finite/non-zero addition kernel. -/
def AddFiniteOppositeSignFlagsToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.addFiniteOppositeSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered same-sign value obligation guarded by sign-equality. -/
def AddFiniteSameSignToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = true →
    ((a.addFiniteSameSign b mode).value.classify = .normal ∨
      (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
      (a.addFiniteSameSign b mode).value.classify = .zero) →
    (a.addFiniteSameSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign value obligation guarded by sign-inequality. -/
def AddFiniteOppositeSignToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .zero) →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign value obligation restricted to cancellation (`zero`) outputs. -/
def AddFiniteOppositeSignZeroToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign value obligation restricted to non-zero (normal/subnormal) outputs. -/
def AddFiniteOppositeSignNonzeroToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign cancellation (`zero`) obligation. -/
def AddFiniteOppositeSignZeroToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign non-zero (normal/subnormal) obligation. -/
def AddFiniteOppositeSignNonzeroToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded same-sign exactness obligation (`toReal` equals real addition). -/
def AddFiniteSameSignExactOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = true →
    ((a.addFiniteSameSign b mode).value.classify = .normal ∨
      (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
      (a.addFiniteSameSign b mode).value.classify = .zero) →
    (a.addFiniteSameSign b mode).value.toReal = a.toReal + b.toReal

/-- Guarded same-sign representability obligation for the exact-sum target. -/
def AddFiniteSameSignRepresentableOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = true →
    ((a.addFiniteSameSign b mode).value.classify = .normal ∨
      (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
      (a.addFiniteSameSign b mode).value.classify = .zero) →
    isRepresentable spec.toFormat (a.toReal + b.toReal)

/-- Guarded opposite-sign zero-branch exactness obligation. -/
def AddFiniteOppositeSignZeroExactOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).value.toReal = a.toReal + b.toReal

/-- Guarded opposite-sign nonzero-branch exactness obligation. -/
def AddFiniteOppositeSignNonzeroExactOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    (a.addFiniteOppositeSign b mode).value.toReal = a.toReal + b.toReal

/-- Guarded opposite-sign zero-branch arithmetic cancellation obligation. -/
def AddFiniteOppositeSignZeroSumOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    a.toReal + b.toReal = 0

private def addFiniteOppositeSignPrimaryBranch {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  let (m1, e1) := a.getExtendedSignificand
  let (m2, e2) := b.getExtendedSignificand
  let diff := e1 - e2
  let m1Ext := m1.toNat <<< 2
  let m2Ext := m2.toNat <<< 2
  let m2Aligned := m2Ext / 2 ^ diff
  let sticky := if m2Ext % 2 ^ diff != 0 then 1 else 0
  m1Ext + sticky ≥ m2Aligned

private def addFiniteSameSignRawExp {spec : BinarySpec} (a _b : FloatBits spec) : Int :=
  let (_, e1) := a.getExtendedSignificand
  (e1 : Int)

private def addFiniteSameSignRawSig {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  let (m1, e1) := a.getExtendedSignificand
  let (m2, e2) := b.getExtendedSignificand
  let diff := e1 - e2
  let m1Ext := m1.toNat <<< 2
  let m2Ext := m2.toNat <<< 2
  let m2Aligned := m2Ext / 2 ^ diff
  let sticky := if m2Ext % 2 ^ diff != 0 then 1 else 0
  (m1Ext + m2Aligned + sticky) / 4

private def addFiniteOppositeSignPrimaryDiffVal {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  let (m1, e1) := a.getExtendedSignificand
  let (m2, e2) := b.getExtendedSignificand
  let diff := e1 - e2
  let m1Ext := m1.toNat <<< 2
  let m2Ext := m2.toNat <<< 2
  let m2Aligned := m2Ext / 2 ^ diff
  let sticky := if m2Ext % 2 ^ diff != 0 then 1 else 0
  (m1Ext + sticky) - m2Aligned

private def addFiniteOppositeSignSecondaryDiffVal {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  let (m1, e1) := a.getExtendedSignificand
  let (m2, e2) := b.getExtendedSignificand
  let diff := e1 - e2
  let m1Ext := m1.toNat <<< 2
  let m2Ext := m2.toNat <<< 2
  let m2Aligned := m2Ext / 2 ^ diff
  let sticky := if m2Ext % 2 ^ diff != 0 then 1 else 0
  m2Aligned - (m1Ext + sticky)

private def addFiniteOppositeSignShiftNeeded {spec : BinarySpec} (diffVal : Nat) : Nat :=
  (spec.sigWidth + 2) - Nat.log2 diffVal

private def addFiniteOppositeSignRawExpFromDiff {spec : BinarySpec}
    (a : FloatBits spec) (diffVal : Nat) : Int :=
  let (_, e1) := a.getExtendedSignificand
  (e1 : Int) - (addFiniteOppositeSignShiftNeeded (spec := spec) diffVal)

private def addFiniteOppositeSignRawSigFromDiff {spec : BinarySpec} (diffVal : Nat) : Nat :=
  let shiftNeeded := addFiniteOppositeSignShiftNeeded (spec := spec) diffVal
  let scaledSig := diffVal <<< shiftNeeded
  scaledSig / 4

private def addFiniteOppositeSignPrimaryRawExp {spec : BinarySpec} (a b : FloatBits spec) : Int :=
  addFiniteOppositeSignRawExpFromDiff (spec := spec) a (addFiniteOppositeSignPrimaryDiffVal a b)

private def addFiniteOppositeSignPrimaryRawSig {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  addFiniteOppositeSignRawSigFromDiff (spec := spec) (addFiniteOppositeSignPrimaryDiffVal a b)

private def addFiniteOppositeSignSecondaryRawExp {spec : BinarySpec} (a b : FloatBits spec) : Int :=
  addFiniteOppositeSignRawExpFromDiff (spec := spec) a (addFiniteOppositeSignSecondaryDiffVal a b)

private def addFiniteOppositeSignSecondaryRawSig {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  addFiniteOppositeSignRawSigFromDiff (spec := spec) (addFiniteOppositeSignSecondaryDiffVal a b)

/-- Guarded same-sign obligation phrased directly on the same-sign `roundAndPack` call. -/
def AddFiniteSameSignRoundAndPackToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = true →
    (roundAndPack (spec := spec) mode a.isNeg (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign primary/non-zero obligation on the branch `roundAndPack` call. -/
def AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
    (roundAndPack (spec := spec) mode a.isNeg
      (addFiniteOppositeSignPrimaryRawExp a b)
      (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign secondary/non-zero obligation on the branch `roundAndPack` call. -/
def AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
    (roundAndPack (spec := spec) mode b.isNeg
      (addFiniteOppositeSignSecondaryRawExp a b)
      (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign non-zero `roundAndPack` obligations bundled by branch. -/
def AddFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode ∧
    AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode

/-- Guarded add `roundAndPack` obligations bundled for auto-nonzero closure paths. -/
def AddFiniteRoundAndPackToSpecOrderedGuardedAutoNonzero
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode ∧
    AddFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded spec mode

/-- Primary opposite-sign non-zero branch: implementation equals selected `roundAndPack` call. -/
def AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
    a.addFiniteOppositeSign b mode =
      roundAndPack (spec := spec) mode a.isNeg
        (addFiniteOppositeSignPrimaryRawExp a b)
        (addFiniteOppositeSignPrimaryRawSig a b)

/-- Secondary opposite-sign non-zero branch: implementation equals selected `roundAndPack` call. -/
def AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
    a.addFiniteOppositeSign b mode =
      roundAndPack (spec := spec) mode b.isNeg
        (addFiniteOppositeSignSecondaryRawExp a b)
        (addFiniteOppositeSignSecondaryRawSig a b)

/-- Primary opposite-sign non-zero class implies `diffVal ≠ 0`. -/
def AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    addFiniteOppositeSignPrimaryDiffVal a b ≠ 0

/-- Secondary opposite-sign non-zero class implies `diffVal ≠ 0`. -/
def AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    addFiniteOppositeSignSecondaryDiffVal a b ≠ 0

/-- Primary opposite-sign zero class implies `diffVal = 0`. -/
def AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    addFiniteOppositeSignPrimaryDiffVal a b = 0

/-- Secondary opposite-sign zero class implies `diffVal = 0`. -/
def AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    addFiniteOppositeSignSecondaryDiffVal a b = 0

/-- Primary opposite-sign zero branch: `diffVal = 0` implies exact zero spec result. -/
def AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b = 0 →
    addSpec spec.toFormat mode a.toReal b.toReal = 0

/-- Secondary opposite-sign zero branch: `diffVal = 0` implies exact zero spec result. -/
def AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    addFiniteOppositeSignSecondaryDiffVal a b = 0 →
    addSpec spec.toFormat mode a.toReal b.toReal = 0

/-- Guarded opposite-sign `zero` obligation on the primary (`m1+sticky ≥ m2Aligned`) branch. -/
def AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign `zero` obligation on the secondary (`m1+sticky < m2Aligned`) branch. -/
def AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign non-zero obligation on the primary branch. -/
def AddFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign non-zero obligation on the secondary branch. -/
def AddFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
      (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
    (a.addFiniteOppositeSign b mode).value.toReal =
      addSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded primary-branch diff-zero arithmetic cancellation obligation. -/
def AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded (spec : BinarySpec) (_mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b = 0 →
    a.toReal + b.toReal = 0

/-- Guarded secondary-branch diff-zero arithmetic cancellation obligation. -/
def AddFiniteOppositeSignSecondaryZeroSumOrderedGuarded (spec : BinarySpec) (_mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = false →
    addFiniteOppositeSignSecondaryDiffVal a b = 0 →
    a.toReal + b.toReal = 0

/-- Guarded primary-branch diff-zero repr-magnitude-equality obligation. -/
def AddFiniteOppositeSignPrimaryDiffZeroReprMagEqOrderedGuarded
    (spec : BinarySpec) (_mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b = 0 →
    a.toRepr.significand = b.toRepr.significand ∧
      a.toRepr.exponent = b.toRepr.exponent

/-- Guarded primary-branch diff-zero extended-magnitude-equality obligation. -/
def AddFiniteOppositeSignPrimaryDiffZeroExtendedMagEqOrderedGuarded
    (spec : BinarySpec) (_mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b = 0 →
    a.getExtendedSignificand.1.toNat = b.getExtendedSignificand.1.toNat ∧
      a.getExtendedSignificand.2 = b.getExtendedSignificand.2

/-- Guarded primary-branch diff-zero extended-exponent-equality obligation. -/
def AddFiniteOppositeSignPrimaryDiffZeroExpEqOrderedGuarded
    (spec : BinarySpec) (_mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b = 0 →
    a.getExtendedSignificand.2 = b.getExtendedSignificand.2

/-- Guarded primary-branch diff-zero repr-exponent-equality obligation. -/
def AddFiniteOppositeSignPrimaryDiffZeroReprExpEqOrderedGuarded
    (spec : BinarySpec) (_mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    addFiniteOppositeSignPrimaryBranch a b = true →
    addFiniteOppositeSignPrimaryDiffVal a b = 0 →
    a.toRepr.exponent = b.toRepr.exponent

/-- Guarded add roundAndPack branch obligations bundled for auto-nonzero closure paths
    (same-sign + opposite-sign zero branches + opposite-sign nonzero branches). -/
def AddFiniteRoundAndPackBranchObligationsGuardedAutoNonzero
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode ∧
    AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode ∧
    AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode ∧
    AddFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded spec mode

/-- Ordered same-sign flag obligation guarded by sign-equality. -/
def AddFiniteSameSignFlagsToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = true →
    (a.addFiniteSameSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign flag obligation guarded by sign-inequality. -/
def AddFiniteOppositeSignFlagsToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    (a.addFiniteOppositeSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded add sign-partitioned flag obligations bundled together. -/
def AddSignFlagsToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode ∧
    AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode

/-- Guarded add obligations for primary-diff-zero auto-nonzero value+flag closure. -/
def AddPrimaryDiffZeroRoundAndSignFlagsObligationsGuardedAutoNonzero
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  AddFiniteRoundAndPackToSpecOrderedGuardedAutoNonzero spec mode ∧
    AddSignFlagsToSpecOrderedGuarded spec mode

/-- Guarded add obligations for exact+primary-diff-zero auto-nonzero value+flag closure. -/
def AddExactAndPrimaryDiffZeroRoundAndSignFlagsObligationsGuardedAutoNonzero
    (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  AddFiniteSameSignExactOrderedGuarded spec mode ∧
    AddFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded spec mode ∧
    AddSignFlagsToSpecOrderedGuarded spec mode

/-- Ordered opposite-sign flag obligation restricted to cancellation (`zero`) outputs. -/
def AddFiniteOppositeSignZeroFlagsToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Ordered opposite-sign flag obligation restricted to non-zero outputs. -/
def AddFiniteOppositeSignNonzeroFlagsToSpecOrdered (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.addFiniteOppositeSign b mode).value.classify ≠ .zero →
    (a.addFiniteOppositeSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign cancellation (`zero`) flag obligation. -/
def AddFiniteOppositeSignZeroFlagsToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    (a.addFiniteOppositeSign b mode).value.classify = .zero →
    (a.addFiniteOppositeSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Guarded opposite-sign non-zero flag obligation. -/
def AddFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    FloatBits.finiteMagGE a b = true →
    (a.isNeg == b.isNeg) = false →
    (a.addFiniteOppositeSign b mode).value.classify ≠ .zero →
    (a.addFiniteOppositeSign b mode).flags =
      addFlagsSpec spec.toFormat mode a.toReal b.toReal

private theorem addSpec_comm (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    addSpec fmt mode a b = addSpec fmt mode b a := by
  simp [addSpec, add_comm]

private theorem addFlagsSpec_comm (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) :
    addFlagsSpec fmt mode a b = addFlagsSpec fmt mode b a := by
  simp [addFlagsSpec, addSpec, add_comm]

private theorem finiteMagGE_total {spec : BinarySpec} (a b : FloatBits spec) :
    FloatBits.finiteMagGE a b = true ∨ FloatBits.finiteMagGE b a = true := by
  unfold FloatBits.finiteMagGE
  let width := spec.expWidth + spec.sigWidth
  let amag := (a.bits.extractLsb' 0 width).toNat
  let bmag := (b.bits.extractLsb' 0 width).toNat
  rcases Nat.le_total amag bmag with h | h
  · right
    simpa [width, amag, bmag, h]
  · left
    simpa [width, amag, bmag, h]

private theorem finiteMagLower_toNat_eq_expSigNat {spec : BinarySpec} (f : FloatBits spec) :
    (f.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth)).toNat =
      (f.expField.toNat <<< spec.sigWidth ||| f.sigField.toNat) := by
  have hsplit :
      f.bits.extractLsb' spec.sigWidth spec.expWidth ++
          f.bits.extractLsb' 0 spec.sigWidth =
        f.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) := by
    simpa using
      (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (x := f.bits)
        (start₂ := spec.sigWidth) (start₁ := 0)
        (len₁ := spec.sigWidth) (len₂ := spec.expWidth) (by omega))
  have hsplitNat := congrArg BitVec.toNat hsplit
  calc
    (f.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth)).toNat
        = (f.bits.extractLsb' spec.sigWidth spec.expWidth ++
            f.bits.extractLsb' 0 spec.sigWidth).toNat := by
          exact hsplitNat.symm
    _ = (f.expField ++ f.sigField).toNat := by
          simp [FloatBits.expField, FloatBits.sigField]
    _ = (f.expField.toNat <<< spec.sigWidth ||| f.sigField.toNat) := by
          simp [BitVec.toNat_append]

private theorem finiteMagLower_mod_eq_expSigNat {spec : BinarySpec} (f : FloatBits spec) :
    f.bits.toNat % 2 ^ (spec.expWidth + spec.sigWidth) =
      (f.expField.toNat <<< spec.sigWidth ||| f.sigField.toNat) := by
  simpa [BitVec.extractLsb'_toNat] using finiteMagLower_toNat_eq_expSigNat f

private theorem finiteMagGE_expField_ge {spec : BinarySpec} {a b : FloatBits spec}
    (hge : FloatBits.finiteMagGE a b = true) :
    b.expField.toNat ≤ a.expField.toNat := by
  have hmag :
      b.bits.toNat % 2 ^ (spec.expWidth + spec.sigWidth) ≤
        a.bits.toNat % 2 ^ (spec.expWidth + spec.sigWidth) := by
    simpa [FloatBits.finiteMagGE] using hge
  have hmag' :
      (b.expField.toNat <<< spec.sigWidth ||| b.sigField.toNat) ≤
        (a.expField.toNat <<< spec.sigWidth ||| a.sigField.toNat) := by
    simpa [finiteMagLower_mod_eq_expSigNat] using hmag
  have hbSigLt : b.sigField.toNat < 2 ^ spec.sigWidth := b.sigField.isLt
  have haSigLt : a.sigField.toNat < 2 ^ spec.sigWidth := a.sigField.isLt
  have hbOrAdd :
      (b.expField.toNat <<< spec.sigWidth ||| b.sigField.toNat) =
        b.expField.toNat <<< spec.sigWidth + b.sigField.toNat := by
    symm
    exact Nat.shiftLeft_add_eq_or_of_lt hbSigLt b.expField.toNat
  have haOrAdd :
      (a.expField.toNat <<< spec.sigWidth ||| a.sigField.toNat) =
        a.expField.toNat <<< spec.sigWidth + a.sigField.toNat := by
    symm
    exact Nat.shiftLeft_add_eq_or_of_lt haSigLt a.expField.toNat
  have hdiv :
      ((b.expField.toNat <<< spec.sigWidth ||| b.sigField.toNat) / 2 ^ spec.sigWidth) ≤
        ((a.expField.toNat <<< spec.sigWidth ||| a.sigField.toNat) / 2 ^ spec.sigWidth) := by
    exact Nat.div_le_div_right hmag'
  have hbDiv :
      (b.expField.toNat <<< spec.sigWidth ||| b.sigField.toNat) / 2 ^ spec.sigWidth =
        b.expField.toNat := by
    rw [hbOrAdd, Nat.shiftLeft_eq]
    have hbDiv' :=
      Nat.add_mul_div_right b.sigField.toNat b.expField.toNat
        (show 0 < 2 ^ spec.sigWidth by exact pow_pos (by decide) _)
    rw [Nat.add_comm] at hbDiv'
    rw [hbDiv']
    simp [Nat.div_eq_of_lt hbSigLt]
  have haDiv :
      (a.expField.toNat <<< spec.sigWidth ||| a.sigField.toNat) / 2 ^ spec.sigWidth =
        a.expField.toNat := by
    rw [haOrAdd, Nat.shiftLeft_eq]
    have haDiv' :=
      Nat.add_mul_div_right a.sigField.toNat a.expField.toNat
        (show 0 < 2 ^ spec.sigWidth by exact pow_pos (by decide) _)
    rw [Nat.add_comm] at haDiv'
    rw [haDiv']
    simp [Nat.div_eq_of_lt haSigLt]
  simpa [hbDiv, haDiv] using hdiv

private theorem finiteMagGE_extendedExp_ge_of_finite {spec : BinarySpec}
    {a b : FloatBits spec}
    (ha : a.classify = .normal ∨ a.classify = .subnormal)
    (hb : b.classify = .normal ∨ b.classify = .subnormal)
    (hge : FloatBits.finiteMagGE a b = true) :
    b.getExtendedSignificand.2 ≤ a.getExtendedSignificand.2 := by
  have hExpFieldGe : b.expField.toNat ≤ a.expField.toNat := finiteMagGE_expField_ge hge
  have hreprA := FloatBits.getExtendedSignificand_eq_toRepr_of_finite a ha
  have hreprB := FloatBits.getExtendedSignificand_eq_toRepr_of_finite b hb
  have hreprExpLe : b.toRepr.exponent ≤ a.toRepr.exponent := by
    rcases hb with hbNorm | hbSub
    · have hbExpZeroFalse : b.isExpZero = false := by
        unfold FloatBits.classify at hbNorm
        split_ifs at hbNorm; simp_all
      have hbReprExp : b.toRepr.exponent = b.expField.toNat := by
        unfold FloatBits.toRepr
        simp [hbExpZeroFalse]
      have hbFieldPos : 1 ≤ b.expField.toNat := by
        have hbFieldNe : b.expField ≠ 0 := by
          intro hb0
          simp [FloatBits.isExpZero, hb0] at hbExpZeroFalse
        exact BitVec.toNat_pos_of_ne_zero hbFieldNe
      have haFieldPos : 1 ≤ a.expField.toNat := le_trans hbFieldPos hExpFieldGe
      have haExpZeroFalse : a.isExpZero = false := by
        have haFieldNe : a.expField ≠ 0 := by
          intro ha0
          have : a.expField.toNat = 0 := by simp [ha0]
          omega
        unfold FloatBits.isExpZero
        exact beq_eq_false_iff_ne.mpr haFieldNe
      have haReprExp : a.toRepr.exponent = a.expField.toNat := by
        unfold FloatBits.toRepr
        simp [haExpZeroFalse]
      calc
        b.toRepr.exponent = b.expField.toNat := hbReprExp
        _ ≤ a.expField.toNat := hExpFieldGe
        _ = a.toRepr.exponent := haReprExp.symm
    · have hbReprOne : b.toRepr.exponent = 1 :=
        FloatBits.toRepr_exponent_eq_one_of_subnormal b hbSub
      have haReprPos : 1 ≤ a.toRepr.exponent :=
        FloatBits.toRepr_exponent_pos_of_finite a ha
      exact by simpa [hbReprOne] using haReprPos
  calc
    b.getExtendedSignificand.2 = b.toRepr.exponent := by simpa using hreprB.2
    _ ≤ a.toRepr.exponent := hreprExpLe
    _ = a.getExtendedSignificand.2 := by simpa using hreprA.2.symm

private theorem machineEpsilon_le_one (fmt : FloatFormat) : machineEpsilon fmt ≤ 1 := by
  unfold machineEpsilon
  have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
  have hle : 1 - (fmt.prec : ℤ) ≤ 0 := by omega
  calc (fmt.β : ℝ) ^ (1 - (fmt.prec : ℤ))
      ≤ (fmt.β : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ fmt.β_one_lt.le hle
    _ = 1 := zpow_zero _

private theorem maxFinite_nonneg (fmt : FloatFormat) : 0 ≤ maxFinite fmt := by
  unfold maxFinite
  have hpow : 0 ≤ (fmt.β : ℝ) ^ fmt.emax := by
    exact zpow_nonneg (show 0 ≤ (fmt.β : ℝ) by positivity) _
  have htail : 0 ≤ 2 - machineEpsilon fmt := by
    have heps : machineEpsilon fmt ≤ 1 := machineEpsilon_le_one fmt
    linarith
  exact mul_nonneg hpow htail

private theorem overflowFlag_zero_false (fmt : FloatFormat) :
    overflowFlag fmt 0 = false := by
  unfold overflowFlag
  classical
  have hnot : ¬ maxFinite fmt < |(0 : ℝ)| := by
    simpa [abs_zero] using not_lt_of_ge (maxFinite_nonneg fmt)
  exact decide_eq_false_iff_not.mpr hnot

private theorem maxFinite_toFormat_eq_scaled (spec : BinarySpec) :
    maxFinite spec.toFormat =
      ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) *
        (2 : ℝ) ^ ((spec.bias : ℤ) - spec.sigWidth) := by
  unfold maxFinite machineEpsilon BinarySpec.toFormat
  change (2 : ℝ) ^ (spec.bias : ℤ) * (2 - (2 : ℝ) ^ (1 - ((spec.sigWidth + 1 : Nat) : ℤ))) =
    ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) * (2 : ℝ) ^ ((spec.bias : ℤ) - spec.sigWidth)
  have hsig : (1 - ((spec.sigWidth + 1 : Nat) : ℤ)) = -(spec.sigWidth : ℤ) := by omega
  rw [hsig]
  have hfactor :
      ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) =
        2 - (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) := by
    have hpowmul :
        (2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) = 2 := by
      calc
        (2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ))
            = (2 : ℝ) ^ ((((spec.sigWidth + 1 : Nat) : ℤ) + (-(spec.sigWidth : ℤ)))) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ = (2 : ℝ) ^ (1 : ℤ) := by congr; omega
        _ = 2 := by norm_num
    have hpowsub :
        (2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ))
          - (2 : ℝ) ^ (-(spec.sigWidth : ℤ))
          = 2 - (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) := by
      simpa using congrArg (fun t => t - (2 : ℝ) ^ (-(spec.sigWidth : ℤ))) hpowmul
    calc
      ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ))
          = (2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ))
              - (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) := by ring
      _ = 2 - (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) := hpowsub
  have hshift :
      (2 : ℝ) ^ ((spec.bias : ℤ) - spec.sigWidth) =
        (2 : ℝ) ^ (spec.bias : ℤ) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ)) := by
    simpa [sub_eq_add_neg] using
      (zpow_add₀ (a := (2 : ℝ)) (m := (spec.bias : ℤ)) (n := (-(spec.sigWidth : ℤ)))
        (by norm_num : (2 : ℝ) ≠ 0))
  calc
    (2 : ℝ) ^ (spec.bias : ℤ) * (2 - (2 : ℝ) ^ (-(spec.sigWidth : ℤ)))
        = (2 : ℝ) ^ (spec.bias : ℤ) *
            (((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ))) := by
          rw [hfactor]
    _ = ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) *
          ((2 : ℝ) ^ (spec.bias : ℤ) * (2 : ℝ) ^ (-(spec.sigWidth : ℤ))) := by ring
    _ = ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) * (2 : ℝ) ^ ((spec.bias : ℤ) - spec.sigWidth) := by
          rw [← hshift]

private theorem abs_le_maxFinite_of_isBitRepresentable {spec : BinarySpec} {x : ℝ}
    (hx : isBitRepresentable spec x) :
    |x| ≤ maxFinite spec.toFormat := by
  obtain ⟨m, e, rfl, hm, _, hemax, _⟩ := hx
  have hm_le : |m| ≤ (2 : ℤ) ^ (spec.sigWidth + 1) - 1 := by omega
  have hm_le' : (|m| : ℝ) ≤ (2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1 := by
    exact_mod_cast hm_le
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ e := by
    exact zpow_nonneg (by positivity) _
  have hpow_le : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ ((spec.bias : ℤ) - spec.sigWidth) := by
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by simpa using hemax)
  calc
    |(m : ℝ) * (2 : ℝ) ^ e| = (|m| : ℝ) * (2 : ℝ) ^ e := by
      rw [abs_mul, abs_of_nonneg hpow_nonneg]
    _ ≤ ((2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1) * (2 : ℝ) ^ ((spec.bias : ℤ) - spec.sigWidth) := by
      have hbound_nonneg : 0 ≤ (2 : ℝ) ^ (((spec.sigWidth + 1 : Nat) : ℤ)) - 1 := by
        exact le_trans (by positivity : (0 : ℝ) ≤ (|m| : ℝ)) hm_le'
      exact mul_le_mul hm_le' hpow_le hpow_nonneg hbound_nonneg
    _ = maxFinite spec.toFormat := by
      symm
      exact maxFinite_toFormat_eq_scaled spec

private theorem abs_toReal_le_maxFinite_of_finite {spec : BinarySpec} (a : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal) :
    |a.toReal| ≤ maxFinite spec.toFormat :=
  abs_le_maxFinite_of_isBitRepresentable (FloatBits.toReal_isBitRepresentable a ha)

private theorem overflowFlag_toReal_false_of_finite {spec : BinarySpec} (a : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal) :
    overflowFlag spec.toFormat a.toReal = false := by
  unfold overflowFlag
  classical
  exact decide_eq_false_iff_not.mpr
    (not_lt_of_ge (abs_toReal_le_maxFinite_of_finite a ha))

/-- Split the ordered finite/non-zero value obligation by sign parity. -/
theorem addFiniteKernelFiniteFiniteToSpec_of_signOrdered (spec : BinarySpec) (mode : RoundingMode)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteSameSign b mode).value.classify = .normal ∨
          (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
          (a.addFiniteSameSign b mode).value.classify = .zero) →
        (a.addFiniteSameSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .zero) →
        (a.addFiniteOppositeSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteKernelFiniteFiniteToSpec spec mode := by
  intro a b ha hb hout
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inl hb) hge hout'
      · have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inl ha) (Or.inl hb) hge hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : b.isNeg == a.isNeg
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inl hb) (Or.inl ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'

      · have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hopp b a (Or.inl hb) (Or.inl ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inr hb) hge hout'
      · have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inl ha) (Or.inr hb) hge hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : b.isNeg == a.isNeg
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inr hb) (Or.inl ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hopp b a (Or.inr hb) (Or.inl ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inl hb) hge hout'
      · have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inr ha) (Or.inl hb) hge hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : b.isNeg == a.isNeg
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inl hb) (Or.inr ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hopp b a (Or.inl hb) (Or.inr ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inr hb) hge hout'
      · have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inr ha) (Or.inr hb) hge hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : b.isNeg == a.isNeg
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inr hb) (Or.inr ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hopp b a (Or.inr hb) (Or.inr ha) hba_true houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'

theorem addFiniteKernelFiniteFiniteToSpec_of_signObligations (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrdered spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrdered spec mode) :
    AddFiniteKernelFiniteFiniteToSpec spec mode := by
  exact addFiniteKernelFiniteFiniteToSpec_of_signOrdered spec mode hsame hopp

theorem addFiniteKernelFiniteFiniteToSpec_of_signOrderedGuarded (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddFiniteKernelFiniteFiniteToSpec spec mode := by
  intro a b ha hb hout
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inl hb) hge hsgn hout'
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inl ha) (Or.inl hb) hge hsgn_false hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inl hb) (Or.inl ha) hba_true hsgn houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn_false] using houtSwap
        have hswap := hopp b a (Or.inl hb) (Or.inl ha) hba_true hsgn_false houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inr hb) hge hsgn hout'
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inl ha) (Or.inr hb) hge hsgn_false hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inr hb) (Or.inl ha) hba_true hsgn houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn_false] using houtSwap
        have hswap := hopp b a (Or.inr hb) (Or.inl ha) hba_true hsgn_false houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inl hb) hge hsgn hout'
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inr ha) (Or.inl hb) hge hsgn_false hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inl hb) (Or.inr ha) hba_true hsgn houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn_false] using houtSwap
        have hswap := hopp b a (Or.inl hb) (Or.inr ha) hba_true hsgn_false houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · have hout' :
          ((a.addFiniteSameSign b mode).value.classify = .normal ∨
            (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
            (a.addFiniteSameSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inr hb) hge hsgn hout'
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        have hout' :
          ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
            (a.addFiniteOppositeSign b mode).value.classify = .zero) := by
          simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using hout
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inr ha) (Or.inr hb) hge hsgn_false hout'
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      have houtSwap :
          ((if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (if b.isNeg == a.isNeg then
              b.addFiniteSameSign a mode
            else
              b.addFiniteOppositeSign a mode).value.classify = .zero) := by
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hout
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have houtSwap' :
          ((b.addFiniteSameSign a mode).value.classify = .normal ∨
            (b.addFiniteSameSign a mode).value.classify = .subnormal ∨
            (b.addFiniteSameSign a mode).value.classify = .zero) := by
          simpa [hsgn] using houtSwap
        have hswap := hsame b a (Or.inr hb) (Or.inr ha) hba_true hsgn houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have houtSwap' :
          ((b.addFiniteOppositeSign a mode).value.classify = .normal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .subnormal ∨
            (b.addFiniteOppositeSign a mode).value.classify = .zero) := by
          simpa [hsgn_false] using houtSwap
        have hswap := hopp b a (Or.inr hb) (Or.inr ha) hba_true hsgn_false houtSwap'
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).value.toReal =
              addSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'

theorem addFiniteKernelFiniteFiniteToSpec_of_signObligationsGuarded
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddFiniteKernelFiniteFiniteToSpec spec mode := by
  exact addFiniteKernelFiniteFiniteToSpec_of_signOrderedGuarded spec mode hsame hopp

theorem addFiniteOppositeSignToSpecOrdered_of_zeroNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzero : AddFiniteOppositeSignZeroToSpecOrdered spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroToSpecOrdered spec mode) :
    AddFiniteOppositeSignToSpecOrdered spec mode := by
  intro a b ha hb hge hout
  rcases hout with hnorm | hsub | hzero_cls
  · exact hnonzero a b ha hb hge (Or.inl hnorm)
  · exact hnonzero a b ha hb hge (Or.inr hsub)
  · exact hzero a b ha hb hge hzero_cls

theorem addFiniteOppositeSignZeroToSpecOrdered_of_addFiniteOppositeSignToSpecOrdered
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignToSpecOrdered spec mode) :
    AddFiniteOppositeSignZeroToSpecOrdered spec mode := by
  intro a b ha hb hge hzero
  exact hopp a b ha hb hge (Or.inr (Or.inr hzero))

theorem addFiniteOppositeSignNonzeroToSpecOrdered_of_addFiniteOppositeSignToSpecOrdered
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignToSpecOrdered spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrdered spec mode := by
  intro a b ha hb hge hnonzero
  rcases hnonzero with hnorm | hsub
  · exact hopp a b ha hb hge (Or.inl hnorm)
  · exact hopp a b ha hb hge (Or.inr (Or.inl hsub))

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzero : AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hout
  rcases hout with hnorm | hsub | hzero_cls
  · exact hnonzero a b ha hb hge hsgn (Or.inl hnorm)
  · exact hnonzero a b ha hb hge hsgn (Or.inr hsub)
  · exact hzero a b ha hb hge hsgn hzero_cls

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_addFiniteOppositeSignToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hzero
  exact hopp a b ha hb hge hsgn (Or.inr (Or.inr hzero))

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_addFiniteOppositeSignToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hnonzero
  rcases hnonzero with hnorm | hsub
  · exact hopp a b ha hb hge hsgn (Or.inl hnorm)
  · exact hopp a b ha hb hge hsgn (Or.inr (Or.inl hsub))

theorem addFiniteSameSignToSpecOrderedGuarded_of_exactAndRepresentable
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hrepr : AddFiniteSameSignRepresentableOrderedGuarded spec mode) :
    AddFiniteSameSignToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hout
  calc
    (a.addFiniteSameSign b mode).value.toReal = a.toReal + b.toReal :=
      hexact a b ha hb hge hsgn hout
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by
      simpa using (addSpec_repr_fixed spec.toFormat mode (hrepr a b ha hb hge hsgn hout)).symm

private theorem addRepresentable_of_exactFiniteResult {spec : BinarySpec}
    (a b : FloatBits spec) (r : OpResult (FloatBits spec))
    (hout :
      r.value.classify = .normal ∨
      r.value.classify = .subnormal ∨
      r.value.classify = .zero)
    (hexact : r.value.toReal = a.toReal + b.toReal) :
    isRepresentable spec.toFormat (a.toReal + b.toReal) := by
  have hreprOut :
      isRepresentable spec.toFormat r.value.toReal :=
    toReal_isRepresentable_of_finiteOrZero r.value hout
  simpa [hexact] using hreprOut

theorem addFiniteSameSignToSpecOrderedGuarded_of_exact
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : AddFiniteSameSignExactOrderedGuarded spec mode) :
    AddFiniteSameSignToSpecOrderedGuarded spec mode := by
  exact addFiniteSameSignToSpecOrderedGuarded_of_exactAndRepresentable spec mode hexact
    (fun a b ha hb hge hsgn hout => by
      exact addRepresentable_of_exactFiniteResult a b (a.addFiniteSameSign b mode) hout
        (hexact a b ha hb hge hsgn hout))

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_exactAndRepresentable
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hrepr :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        (a.addFiniteOppositeSign b mode).value.classify = .zero →
        isRepresentable spec.toFormat (a.toReal + b.toReal)) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hzero
  calc
    (a.addFiniteOppositeSign b mode).value.toReal = a.toReal + b.toReal :=
      hexact a b ha hb hge hsgn hzero
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by
      simpa using (addSpec_repr_fixed spec.toFormat mode (hrepr a b ha hb hge hsgn hzero)).symm

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_exact
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignZeroToSpecOrderedGuarded_of_exactAndRepresentable spec mode hexact
    (fun a b ha hb hge hsgn hzero => by
      exact addRepresentable_of_exactFiniteResult a b (a.addFiniteOppositeSign b mode)
        (Or.inr (Or.inr hzero)) (hexact a b ha hb hge hsgn hzero))

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_sumZero
    (spec : BinarySpec) (mode : RoundingMode)
    (hsum : AddFiniteOppositeSignZeroSumOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hzero
  have hto0 : (a.addFiniteOppositeSign b mode).value.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hzero]
  have hsum0 : a.toReal + b.toReal = 0 := hsum a b ha hb hge hsgn hzero
  have hspec0 : addSpec spec.toFormat mode a.toReal b.toReal = 0 := by
    simp [addSpec, hsum0, round_zero]
  calc
    (a.addFiniteOppositeSign b mode).value.toReal = 0 := hto0
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by simp [hspec0]

theorem addFiniteOppositeSignZeroExactOrderedGuarded_of_sumZero
    (spec : BinarySpec) (mode : RoundingMode)
    (hsum : AddFiniteOppositeSignZeroSumOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroExactOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hzero
  have hto0 : (a.addFiniteOppositeSign b mode).value.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hzero]
  have hsum0 : a.toReal + b.toReal = 0 := hsum a b ha hb hge hsgn hzero
  simpa [hsum0] using hto0

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_exactAndRepresentable
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : AddFiniteOppositeSignNonzeroExactOrderedGuarded spec mode)
    (hrepr :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .subnormal) →
        isRepresentable spec.toFormat (a.toReal + b.toReal)) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hnonzero
  calc
    (a.addFiniteOppositeSign b mode).value.toReal = a.toReal + b.toReal :=
      hexact a b ha hb hge hsgn hnonzero
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by
      exact (addSpec_repr_fixed spec.toFormat mode (hrepr a b ha hb hge hsgn hnonzero)).symm

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_exact
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : AddFiniteOppositeSignNonzeroExactOrderedGuarded spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_exactAndRepresentable spec mode hexact
    (fun a b ha hb hge hsgn hnonzero => by
      rcases hnonzero with hnorm | hsub
      · exact addRepresentable_of_exactFiniteResult a b (a.addFiniteOppositeSign b mode)
          (Or.inl hnorm) (hexact a b ha hb hge hsgn (Or.inl hnorm))
      · exact addRepresentable_of_exactFiniteResult a b (a.addFiniteOppositeSign b mode)
          (Or.inr (Or.inl hsub)) (hexact a b ha hb hge hsgn (Or.inr hsub)))

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_exact
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroExact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hnonzeroExact : AddFiniteOppositeSignNonzeroExactOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero spec mode
    (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_exact spec mode hzeroExact)
    (addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_exact spec mode hnonzeroExact)

theorem addFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded_of_diffAndSpecZero
    (spec : BinarySpec) (mode : RoundingMode)
    (hdiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hspec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimary hzero
  have hdiff0 := hdiff a b ha hb hge hsgn hprimary hzero
  have hspec0 := hspec a b ha hb hge hsgn hprimary hdiff0
  have hto0 : (a.addFiniteOppositeSign b mode).value.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hzero]
  calc
    (a.addFiniteOppositeSign b mode).value.toReal = 0 := hto0
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by simp [hspec0]

theorem addFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded_of_diffAndSpecZero
    (spec : BinarySpec) (mode : RoundingMode)
    (hdiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hspec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondary hzero
  have hdiff0 := hdiff a b ha hb hge hsgn hsecondary hzero
  have hspec0 := hspec a b ha hb hge hsgn hsecondary hdiff0
  have hto0 : (a.addFiniteOppositeSign b mode).value.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hzero]
  calc
    (a.addFiniteOppositeSign b mode).value.toReal = 0 := hto0
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by simp [hspec0]

theorem addFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded_of_sumZero
    (spec : BinarySpec) (mode : RoundingMode)
    (hsum :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b = 0 →
        a.toReal + b.toReal = 0) :
    AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimary hdiff0
  have hsum0 := hsum a b ha hb hge hsgn hprimary hdiff0
  simp [addSpec, hsum0, round_zero]

theorem addFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded_of_sumZero
    (spec : BinarySpec) (mode : RoundingMode)
    (hsum :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = false →
        addFiniteOppositeSignSecondaryDiffVal a b = 0 →
        a.toReal + b.toReal = 0) :
    AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondary hdiff0
  have hsum0 := hsum a b ha hb hge hsgn hsecondary hdiff0
  simp [addSpec, hsum0, round_zero]

theorem addFiniteOppositeSignSecondaryZeroSumOrderedGuarded_auto
    (spec : BinarySpec) (_mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = false →
      addFiniteOppositeSignSecondaryDiffVal a b = 0 →
      a.toReal + b.toReal = 0 := by
  intro a b ha hb hge hsgn hsecondary hdiff0
  have hsecondary' :
      ¬(b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
          a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) := by
    simpa [addFiniteOppositeSignPrimaryBranch] using hsecondary
  have hdiff' :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) -
        (a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) = 0 := by
    simpa [addFiniteOppositeSignSecondaryDiffVal] using hdiff0
  have hle :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
        a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) :=
    Nat.sub_eq_zero_iff_le.mp hdiff'
  exact (False.elim (hsecondary' hle))

private theorem finiteOppositeSignSumZero_of_reprMagEq {spec : BinarySpec}
    (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal)
    (hb : b.classify = .normal ∨ b.classify = .subnormal)
    (hsgn : (a.isNeg == b.isNeg) = false)
    (hsig : a.toRepr.significand = b.toRepr.significand)
    (hexp : a.toRepr.exponent = b.toRepr.exponent) :
    a.toReal + b.toReal = 0 := by
  have htoa :
      a.toReal = (a.toRepr.sign.toInt : ℝ) * (a.toRepr.significand : ℝ) *
        (2 : ℝ) ^ ((a.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth) := by
    exact a.toReal_eq_toRepr_of_finite ha
  have htob :
      b.toReal = (b.toRepr.sign.toInt : ℝ) * (b.toRepr.significand : ℝ) *
        (2 : ℝ) ^ ((b.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth) := by
    exact b.toReal_eq_toRepr_of_finite hb
  have hsignSum : ((a.toRepr.sign.toInt : ℝ) + (b.toRepr.sign.toInt : ℝ)) = 0 := by
    cases haNeg : a.isNeg <;> cases hbNeg : b.isNeg
    · simp [haNeg, hbNeg] at hsgn
    · have hsa : a.toRepr.sign.toInt = 1 := by
        simpa [haNeg] using FloatBits.toRepr_sign_toInt_of_isNeg a
      have hsb : b.toRepr.sign.toInt = -1 := by
        simpa [hbNeg] using FloatBits.toRepr_sign_toInt_of_isNeg b
      simp [hsa, hsb]
    · have hsa : a.toRepr.sign.toInt = -1 := by
        simpa [haNeg] using FloatBits.toRepr_sign_toInt_of_isNeg a
      have hsb : b.toRepr.sign.toInt = 1 := by
        simpa [hbNeg] using FloatBits.toRepr_sign_toInt_of_isNeg b
      simp [hsa, hsb]
    · simp [haNeg, hbNeg] at hsgn
  calc
    a.toReal + b.toReal
        = (a.toRepr.sign.toInt : ℝ) * (b.toRepr.significand : ℝ) *
            (2 : ℝ) ^ ((b.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth) +
          (b.toRepr.sign.toInt : ℝ) * (b.toRepr.significand : ℝ) *
            (2 : ℝ) ^ ((b.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth) := by
      rw [htoa, htob, hsig, hexp]
    _ = ((a.toRepr.sign.toInt : ℝ) + (b.toRepr.sign.toInt : ℝ)) *
          (b.toRepr.significand : ℝ) *
          (2 : ℝ) ^ ((b.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth) := by
      ring
    _ = 0 := by simp [hsignSum]

theorem addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprMagEq
    (spec : BinarySpec) (_mode : RoundingMode)
    (hmagEq :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b = 0 →
        a.toRepr.significand = b.toRepr.significand ∧
          a.toRepr.exponent = b.toRepr.exponent) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.toReal + b.toReal = 0 := by
  intro a b ha hb hge hsgn hprimary hdiff0
  rcases hmagEq a b ha hb hge hsgn hprimary hdiff0 with ⟨hsig, hexp⟩
  exact finiteOppositeSignSumZero_of_reprMagEq a b ha hb hsgn hsig hexp

theorem addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_extendedMagEq
    (spec : BinarySpec) (_mode : RoundingMode)
    (hmagEq :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b = 0 →
        a.getExtendedSignificand.1.toNat = b.getExtendedSignificand.1.toNat ∧
          a.getExtendedSignificand.2 = b.getExtendedSignificand.2) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.toReal + b.toReal = 0 := by
  intro a b ha hb hge hsgn hprimary hdiff0
  rcases hmagEq a b ha hb hge hsgn hprimary hdiff0 with ⟨hmExt, heExt⟩
  have hreprA := FloatBits.getExtendedSignificand_eq_toRepr_of_finite a ha
  have hreprB := FloatBits.getExtendedSignificand_eq_toRepr_of_finite b hb
  have hsig : a.toRepr.significand = b.toRepr.significand := by
    calc
      a.toRepr.significand = a.getExtendedSignificand.1.toNat := by simpa using hreprA.1.symm
      _ = b.getExtendedSignificand.1.toNat := hmExt
      _ = b.toRepr.significand := by simpa using hreprB.1
  have hexp : a.toRepr.exponent = b.toRepr.exponent := by
    calc
      a.toRepr.exponent = a.getExtendedSignificand.2 := by simpa using hreprA.2.symm
      _ = b.getExtendedSignificand.2 := heExt
      _ = b.toRepr.exponent := by simpa using hreprB.2
  exact finiteOppositeSignSumZero_of_reprMagEq a b ha hb hsgn hsig hexp

theorem addFiniteOppositeSignPrimaryExpEqOrderedGuarded_auto
    (spec : BinarySpec) (_mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.getExtendedSignificand.2 = b.getExtendedSignificand.2 := by
  intro a b ha hb hge hsgn hprimary hdiff0
  have hbe_le_ae : b.getExtendedSignificand.2 ≤ a.getExtendedSignificand.2 :=
    finiteMagGE_extendedExp_ge_of_finite ha hb hge
  have hae_le_be : a.getExtendedSignificand.2 ≤ b.getExtendedSignificand.2 := by
    by_contra hnot
    have hbe_lt_ae : b.getExtendedSignificand.2 < a.getExtendedSignificand.2 :=
      Nat.lt_of_not_ge hnot
    have hreprA := FloatBits.getExtendedSignificand_eq_toRepr_of_finite a ha
    have hreprB := FloatBits.getExtendedSignificand_eq_toRepr_of_finite b hb
    have hbExpPos : 1 ≤ b.getExtendedSignificand.2 := by
      calc
        1 ≤ b.toRepr.exponent := FloatBits.toRepr_exponent_pos_of_finite b hb
        _ = b.getExtendedSignificand.2 := by simpa using hreprB.2.symm
    have haExpGeTwo : 2 ≤ a.getExtendedSignificand.2 := by
      have hOneLtAe : 1 < a.getExtendedSignificand.2 :=
        lt_of_le_of_lt hbExpPos hbe_lt_ae
      have : 1 + 1 ≤ a.getExtendedSignificand.2 := by
        exact Nat.succ_le_of_lt hOneLtAe
      simpa using this
    have haNotSub : a.classify ≠ .subnormal := by
      intro haSub
      have haExpOne : a.getExtendedSignificand.2 = 1 := by
        have haReprOne : a.toRepr.exponent = 1 :=
          FloatBits.toRepr_exponent_eq_one_of_subnormal a haSub
        calc
          a.getExtendedSignificand.2 = a.toRepr.exponent := by simpa using hreprA.2
          _ = 1 := haReprOne
      omega
    have haNorm : a.classify = .normal := by
      rcases ha with haNorm | haSub
      · exact haNorm
      · exact False.elim (haNotSub haSub)
    have haNormRange := FloatBits.normal_significand_range a haNorm
    have hm1_ge :
        2 ^ spec.sigWidth ≤ a.getExtendedSignificand.1.toNat := by
      calc
        2 ^ spec.sigWidth ≤ a.toRepr.significand := haNormRange.1
        _ = a.getExtendedSignificand.1.toNat := by simpa using hreprA.1.symm
    have hm2_lt :
        b.getExtendedSignificand.1.toNat < 2 ^ (spec.sigWidth + 1) := by
      have hbSigLt := FloatBits.significand_lt_two_pow_succ_of_finite b hb
      simpa using (show b.getExtendedSignificand.1.toNat < 2 ^ (spec.sigWidth + 1) by
        simpa [hreprB.1] using hbSigLt)
    have hprimary_le :
        b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
          a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) := by
      simpa [addFiniteOppositeSignPrimaryBranch] using hprimary
    have hdiff_le :
        a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) ≤
          b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) := by
      have hdiff_eq :
          (a.getExtendedSignificand.1.toNat <<< 2 +
              (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) -
            b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 := by
        simpa [addFiniteOppositeSignPrimaryDiffVal] using hdiff0
      exact Nat.sub_eq_zero_iff_le.mp hdiff_eq
    have hleft_ge :
        2 ^ (spec.sigWidth + 2) ≤
          a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) := by
      have hm1Ext_ge : 2 ^ (spec.sigWidth + 2) ≤ a.getExtendedSignificand.1.toNat <<< 2 := by
        have hm1Mul_ge :
            2 ^ spec.sigWidth * 2 ^ 2 ≤ a.getExtendedSignificand.1.toNat * 2 ^ 2 :=
          Nat.mul_le_mul_right (2 ^ 2) hm1_ge
        simpa [Nat.shiftLeft_eq, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm1Mul_ge
      exact le_trans hm1Ext_ge (Nat.le_add_right _ _)
    have hright_ge :
        2 ^ (spec.sigWidth + 2) ≤
          b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) := by
      exact le_trans hleft_ge hdiff_le
    have hdiffPos : 0 < a.getExtendedSignificand.2 - b.getExtendedSignificand.2 :=
      Nat.sub_pos_of_lt hbe_lt_ae
    have hpowGeTwo : 2 ≤ 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) := by
      have hdiffGeOne : 1 ≤ a.getExtendedSignificand.2 - b.getExtendedSignificand.2 :=
        Nat.succ_le_of_lt hdiffPos
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) hdiffGeOne
    have hright_le_half :
        b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
          b.getExtendedSignificand.1.toNat <<< 2 / 2 := by
      exact Nat.div_le_div_left hpowGeTwo (by decide : 0 < 2)
    have hm2HalfEq :
        b.getExtendedSignificand.1.toNat <<< 2 / 2 =
          b.getExtendedSignificand.1.toNat <<< 1 := by
      rw [Nat.shiftLeft_eq, show 2 ^ 2 = 2 * 2 by norm_num, ← Nat.mul_assoc]
      rw [Nat.mul_comm (b.getExtendedSignificand.1.toNat * 2) 2]
      rw [Nat.mul_div_right (b.getExtendedSignificand.1.toNat * 2) (by decide : 0 < 2)]
      simp [Nat.shiftLeft_eq]
    have hm2Shift1Lt :
        b.getExtendedSignificand.1.toNat <<< 1 < 2 ^ (spec.sigWidth + 2) := by
      have hm2MulLt :
          b.getExtendedSignificand.1.toNat * 2 < 2 ^ (spec.sigWidth + 1) * 2 :=
        Nat.mul_lt_mul_of_pos_right hm2_lt (by decide : 0 < 2)
      simpa [Nat.shiftLeft_eq, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm2MulLt
    have hright_lt :
        b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) <
          2 ^ (spec.sigWidth + 2) := by
      exact lt_of_le_of_lt hright_le_half (by simpa [hm2HalfEq] using hm2Shift1Lt)
    exact (Nat.not_lt.mpr hright_ge) hright_lt
  exact Nat.le_antisymm hae_le_be hbe_le_ae

theorem addFiniteOppositeSignPrimaryZeroExtendedMagEqOrderedGuarded_of_expEq
    (spec : BinarySpec) (_mode : RoundingMode)
    (hExpEq :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b = 0 →
        a.getExtendedSignificand.2 = b.getExtendedSignificand.2) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.getExtendedSignificand.1.toNat = b.getExtendedSignificand.1.toNat ∧
        a.getExtendedSignificand.2 = b.getExtendedSignificand.2 := by
  intro a b ha hb hge hsgn hprimary hdiff0
  have hextExpEq : a.getExtendedSignificand.2 = b.getExtendedSignificand.2 :=
    hExpEq a b ha hb hge hsgn hprimary hdiff0
  have hprimary_le :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
        a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) := by
    simpa [addFiniteOppositeSignPrimaryBranch] using hprimary
  have hdiff_le :
      a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) ≤
        b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) := by
    have hdiff_eq :
        (a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) -
          b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 := by
      simpa [addFiniteOppositeSignPrimaryDiffVal] using hdiff0
    exact Nat.sub_eq_zero_iff_le.mp hdiff_eq
  have hmod1 : b.getExtendedSignificand.1.toNat <<< 2 % 1 = 0 := by
    exact Nat.mod_one _
  have hprimary_le' : b.getExtendedSignificand.1.toNat <<< 2 ≤ a.getExtendedSignificand.1.toNat <<< 2 := by
    simpa [hextExpEq, hmod1] using hprimary_le
  have hdiff_le' : a.getExtendedSignificand.1.toNat <<< 2 ≤ b.getExtendedSignificand.1.toNat <<< 2 := by
    simpa [hextExpEq, hmod1] using hdiff_le
  have hshiftEq :
      a.getExtendedSignificand.1.toNat <<< 2 = b.getExtendedSignificand.1.toNat <<< 2 :=
    Nat.le_antisymm hdiff_le' hprimary_le'
  have hsigEq :
      a.getExtendedSignificand.1.toNat = b.getExtendedSignificand.1.toNat := by
    have hmulEq :
        a.getExtendedSignificand.1.toNat * 2 ^ 2 = b.getExtendedSignificand.1.toNat * 2 ^ 2 := by
      simpa [Nat.shiftLeft_eq] using hshiftEq
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ 2 by decide) hmulEq
  exact ⟨hsigEq, hextExpEq⟩

theorem addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq
    (spec : BinarySpec) (mode : RoundingMode)
    (hExpEq :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b = 0 →
        a.getExtendedSignificand.2 = b.getExtendedSignificand.2) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.toReal + b.toReal = 0 := by
  exact addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_extendedMagEq spec mode
    (addFiniteOppositeSignPrimaryZeroExtendedMagEqOrderedGuarded_of_expEq spec mode hExpEq)

theorem addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprExpEq
    (spec : BinarySpec) (mode : RoundingMode)
    (hExpEq :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b = 0 →
        a.toRepr.exponent = b.toRepr.exponent) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.toReal + b.toReal = 0 := by
  exact addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq spec mode
    (fun a b ha hb hge hsgn hprimary hdiff0 => by
      have hreprExpEq : a.toRepr.exponent = b.toRepr.exponent :=
        hExpEq a b ha hb hge hsgn hprimary hdiff0
      have hreprA := FloatBits.getExtendedSignificand_eq_toRepr_of_finite a ha
      have hreprB := FloatBits.getExtendedSignificand_eq_toRepr_of_finite b hb
      calc
        a.getExtendedSignificand.2 = a.toRepr.exponent := by simpa using hreprA.2
        _ = b.toRepr.exponent := hreprExpEq
        _ = b.getExtendedSignificand.2 := by simpa using hreprB.2.symm)

theorem addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_auto
    (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      FloatBits.finiteMagGE a b = true →
      (a.isNeg == b.isNeg) = false →
      addFiniteOppositeSignPrimaryBranch a b = true →
      addFiniteOppositeSignPrimaryDiffVal a b = 0 →
      a.toReal + b.toReal = 0 := by
  exact addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq spec mode
    (addFiniteOppositeSignPrimaryExpEqOrderedGuarded_auto spec mode)

theorem addFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded_of_specZeroOrRoundAndPack
    (spec : BinarySpec) (mode : RoundingMode)
    (hspec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hcase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hround : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimary hzero
  by_cases hdiff0 : addFiniteOppositeSignPrimaryDiffVal a b = 0
  · have hspec0 := hspec a b ha hb hge hsgn hprimary hdiff0
    have hto0 : (a.addFiniteOppositeSign b mode).value.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hzero]
    calc
      (a.addFiniteOppositeSign b mode).value.toReal = 0 := hto0
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by simp [hspec0]
  · have hdiff_ne0 : addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 := hdiff0
    have hcase_eq := hcase a b ha hb hge hsgn hprimary hdiff_ne0
    calc
      (a.addFiniteOppositeSign b mode).value.toReal =
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteOppositeSignPrimaryRawExp a b)
            (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal := by
        simp [hcase_eq]
      _ = addSpec spec.toFormat mode a.toReal b.toReal :=
        hround a b ha hb hge hsgn hprimary hdiff_ne0

theorem addFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded_of_specZeroOrRoundAndPack
    (spec : BinarySpec) (mode : RoundingMode)
    (hspec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hcase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hround : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondary hzero
  by_cases hdiff0 : addFiniteOppositeSignSecondaryDiffVal a b = 0
  · have hspec0 := hspec a b ha hb hge hsgn hsecondary hdiff0
    have hto0 : (a.addFiniteOppositeSign b mode).value.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hzero]
    calc
      (a.addFiniteOppositeSign b mode).value.toReal = 0 := hto0
    _ = addSpec spec.toFormat mode a.toReal b.toReal := by simp [hspec0]
  · have hdiff_ne0 : addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 := hdiff0
    have hcase_eq := hcase a b ha hb hge hsgn hsecondary hdiff_ne0
    calc
      (a.addFiniteOppositeSign b mode).value.toReal =
          (roundAndPack (spec := spec) mode b.isNeg
            (addFiniteOppositeSignSecondaryRawExp a b)
            (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal := by
        simp [hcase_eq]
      _ = addSpec spec.toFormat mode a.toReal b.toReal :=
        hround a b ha hb hge hsgn hsecondary hdiff_ne0

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_primarySecondary
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hsecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hzero
  by_cases hprim : addFiniteOppositeSignPrimaryBranch a b = true
  · exact hprimary a b ha hb hge hsgn hprim hzero
  · have hprim_false : addFiniteOppositeSignPrimaryBranch a b = false := by
      cases hbool : addFiniteOppositeSignPrimaryBranch a b <;> simp [hbool] at hprim ⊢
    exact hsecondary a b ha hb hge hsgn hprim_false hzero

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_primarySecondary
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimary : AddFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded spec mode)
    (hsecondary : AddFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hnonzero
  by_cases hprim : addFiniteOppositeSignPrimaryBranch a b = true
  · exact hprimary a b ha hb hge hsgn hprim hnonzero
  · have hprim_false : addFiniteOppositeSignPrimaryBranch a b = false := by
      cases hbool : addFiniteOppositeSignPrimaryBranch a b <;> simp [hbool] at hprim ⊢
    exact hsecondary a b ha hb hge hsgn hprim_false hnonzero

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primarySecondary
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hnonzeroPrimary : AddFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded spec mode)
    (hnonzeroSecondary : AddFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero spec mode
    (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_primarySecondary
      spec mode hzeroPrimary hzeroSecondary)
    (addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_primarySecondary
      spec mode hnonzeroPrimary hnonzeroSecondary)

theorem addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack
    (spec : BinarySpec) (mode : RoundingMode)
    (hround : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteSameSignToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hout
  have hcase :
      a.addFiniteSameSign b mode =
        roundAndPack (spec := spec) mode a.isNeg (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b) := by
    unfold FloatBits.addFiniteSameSign addFiniteSameSignRawExp addFiniteSameSignRawSig
    simp
  calc
    (a.addFiniteSameSign b mode).value.toReal =
        (roundAndPack (spec := spec) mode a.isNeg (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.toReal := by
      simp [hcase]
    _ = addSpec spec.toFormat mode a.toReal b.toReal := hround a b ha hb hge hsgn

/-- Recover same-sign `roundAndPack` obligations from guarded same-sign correctness
plus an explicit non-finite fallback for the `roundAndPack` result. -/
theorem addFiniteSameSignRoundAndPackToSpecOrderedGuarded_of_signOrderedGuarded_and_nonfinite
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hnonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = true →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .subnormal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .zero) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn
  have hcase :
      a.addFiniteSameSign b mode =
        roundAndPack (spec := spec) mode a.isNeg (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b) := by
    unfold FloatBits.addFiniteSameSign addFiniteSameSignRawExp addFiniteSameSignRawSig
    simp
  by_cases hout :
      ((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .zero)
  · have hout' :
      ((a.addFiniteSameSign b mode).value.classify = .normal ∨
        (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
        (a.addFiniteSameSign b mode).value.classify = .zero) := by
      simpa [hcase] using hout
    have hspec := hsame a b ha hb hge hsgn hout'
    simpa [hcase] using hspec
  · exact hnonfinite a b ha hb hge hsgn hout

theorem addFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded_default
    (spec : BinarySpec) (mode : RoundingMode) :
    AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimary hdiff
  have hprimary' :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
        a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) := by
    simpa [addFiniteOppositeSignPrimaryBranch] using hprimary
  have hdiff' :
      (a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) -
        b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≠ 0 := by
    simpa [addFiniteOppositeSignPrimaryDiffVal] using hdiff
  unfold FloatBits.addFiniteOppositeSign
  simp [addFiniteOppositeSignPrimaryRawExp, addFiniteOppositeSignPrimaryRawSig,
    addFiniteOppositeSignRawExpFromDiff, addFiniteOppositeSignRawSigFromDiff,
    addFiniteOppositeSignShiftNeeded, addFiniteOppositeSignPrimaryDiffVal,
    hprimary', hdiff']

theorem addFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded_default
    (spec : BinarySpec) (mode : RoundingMode) :
    AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondary hdiff
  have hsecondary' :
      ¬(b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
          a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) := by
    simpa [addFiniteOppositeSignPrimaryBranch] using hsecondary
  have hdiff' :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) -
        (a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) ≠ 0 := by
    simpa [addFiniteOppositeSignSecondaryDiffVal] using hdiff
  unfold FloatBits.addFiniteOppositeSign
  simp [addFiniteOppositeSignSecondaryRawExp, addFiniteOppositeSignSecondaryRawSig,
    addFiniteOppositeSignRawExpFromDiff, addFiniteOppositeSignRawSigFromDiff,
    addFiniteOppositeSignShiftNeeded, addFiniteOppositeSignSecondaryDiffVal,
    hsecondary', hdiff']

theorem addFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded_default
    (spec : BinarySpec) (mode : RoundingMode) :
    AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimary hnonzero hdiff
  have hprimary' :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
        a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1) := by
    simpa [addFiniteOppositeSignPrimaryBranch] using hprimary
  have hdiff' :
      (a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) -
        b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 := by
      simpa [addFiniteOppositeSignPrimaryDiffVal] using hdiff
  have hzeroCls : (a.addFiniteOppositeSign b mode).value.classify = .zero := by
    unfold FloatBits.addFiniteOppositeSign
    by_cases hneg : mode = .roundTowardNegative
    · simp [hprimary', hdiff', hneg,
        FloatBits.negZero_classify]
    · simp [hprimary', hdiff', hneg,
        FloatBits.posZero_classify]
  rcases hnonzero with hnorm | hsub
  · simp [hzeroCls] at hnorm
  · simp [hzeroCls] at hsub

theorem addFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded_default
    (spec : BinarySpec) (mode : RoundingMode) :
    AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondary hnonzero hdiff
  have hsecondary' :
      ¬(b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) ≤
          a.getExtendedSignificand.1.toNat <<< 2 +
            (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) := by
    simpa [addFiniteOppositeSignPrimaryBranch] using hsecondary
  have hdiff' :
      b.getExtendedSignificand.1.toNat <<< 2 / 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) -
        (a.getExtendedSignificand.1.toNat <<< 2 +
          (if b.getExtendedSignificand.1.toNat <<< 2 % 2 ^ (a.getExtendedSignificand.2 - b.getExtendedSignificand.2) = 0 then 0 else 1)) = 0 := by
      simpa [addFiniteOppositeSignSecondaryDiffVal] using hdiff
  have hzeroCls : (a.addFiniteOppositeSign b mode).value.classify = .zero := by
    unfold FloatBits.addFiniteOppositeSign
    by_cases hneg : mode = .roundTowardNegative
    · simp [hsecondary', hdiff', hneg,
        FloatBits.negZero_classify]
    · simp [hsecondary', hdiff', hneg,
        FloatBits.posZero_classify]
  rcases hnonzero with hnorm | hsub
  · simp [hzeroCls] at hnorm
  · simp [hzeroCls] at hsub

/-- Recover primary non-zero opposite-sign `roundAndPack` obligations from guarded
primary non-zero correctness plus an explicit non-finite fallback. -/
theorem addFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded_of_primaryNonzeroToSpecOrderedGuarded_and_nonfinite
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimary : AddFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded spec mode)
    (hnonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteOppositeSignPrimaryRawExp a b)
            (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimaryBranch hdiff
  have hcase :=
    addFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode
      a b ha hb hge hsgn hprimaryBranch hdiff
  by_cases hout :
      ((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .subnormal)
  · have hout' :
      ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
        (a.addFiniteOppositeSign b mode).value.classify = .subnormal) := by
      simpa [hcase] using hout
    have hspec := hprimary a b ha hb hge hsgn hprimaryBranch hout'
    simpa [hcase] using hspec
  · exact hnonfinite a b ha hb hge hsgn hprimaryBranch hdiff hout

/-- Recover secondary non-zero opposite-sign `roundAndPack` obligations from guarded
secondary non-zero correctness plus an explicit non-finite fallback. -/
theorem addFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded_of_secondaryNonzeroToSpecOrderedGuarded_and_nonfinite
    (spec : BinarySpec) (mode : RoundingMode)
    (hsecondary : AddFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded spec mode)
    (hnonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = false →
        addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode b.isNeg
            (addFiniteOppositeSignSecondaryRawExp a b)
            (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondaryBranch hdiff
  have hcase :=
    addFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode
      a b ha hb hge hsgn hsecondaryBranch hdiff
  by_cases hout :
      ((roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .subnormal)
  · have hout' :
      ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
        (a.addFiniteOppositeSign b mode).value.classify = .subnormal) := by
      simpa [hcase] using hout
    have hspec := hsecondary a b ha hb hge hsgn hsecondaryBranch hout'
    simpa [hcase] using hspec
  · exact hnonfinite a b ha hb hge hsgn hsecondaryBranch hdiff hout

theorem addFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded_of_roundAndPack
    (spec : BinarySpec) (mode : RoundingMode)
    (hcase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hround : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hdiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hprimary hnonzero
  have hdiff_ne0 := hdiff a b ha hb hge hsgn hprimary hnonzero
  have hcase_eq := hcase a b ha hb hge hsgn hprimary hdiff_ne0
  calc
    (a.addFiniteOppositeSign b mode).value.toReal =
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal := by
      simp [hcase_eq]
    _ = addSpec spec.toFormat mode a.toReal b.toReal :=
      hround a b ha hb hge hsgn hprimary hdiff_ne0

theorem addFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded_of_roundAndPack
    (spec : BinarySpec) (mode : RoundingMode)
    (hcase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hround : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hdiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hsecondary hnonzero
  have hdiff_ne0 := hdiff a b ha hb hge hsgn hsecondary hnonzero
  have hcase_eq := hcase a b ha hb hge hsgn hsecondary hdiff_ne0
  calc
    (a.addFiniteOppositeSign b mode).value.toReal =
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal := by
      simp [hcase_eq]
    _ = addSpec spec.toFormat mode a.toReal b.toReal :=
      hround a b ha hb hge hsgn hsecondary hdiff_ne0

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_primarySecondary spec mode
    (addFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded_of_roundAndPack
      spec mode hprimaryCase hprimaryRound hprimaryDiff)
    (addFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded_of_roundAndPack
      spec mode hsecondaryCase hsecondaryRound hsecondaryDiff)

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack_auto
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack spec mode
    (addFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
    hprimaryRound
    (addFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded_default spec mode)
    (addFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
    hsecondaryRound
    (addFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded_default spec mode)

/-- Build opposite-sign non-zero `roundAndPack` branch obligations from guarded
opposite-sign non-zero correctness plus explicit non-finite fallbacks for each branch. -/
theorem addFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded_of_nonzeroToSpecOrderedGuarded_and_nonfinite
    (spec : BinarySpec) (mode : RoundingMode)
    (hnonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode)
    (hprimaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteOppositeSignPrimaryRawExp a b)
            (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hsecondaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = false →
        addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode b.isNeg
            (addFiniteOppositeSignSecondaryRawExp a b)
            (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded spec mode := by
  refine ⟨?_, ?_⟩
  · exact
      addFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded_of_primaryNonzeroToSpecOrderedGuarded_and_nonfinite
        spec mode
        (fun a b ha hb hge hsgn _ hcls =>
          hnonzero a b ha hb hge hsgn hcls)
        hprimaryNonfinite
  · exact
      addFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded_of_secondaryNonzeroToSpecOrderedGuarded_and_nonfinite
        spec mode
        (fun a b ha hb hge hsgn _ hcls =>
          hnonzero a b ha hb hge hsgn hcls)
        hsecondaryNonfinite

/-- Build bundled same-sign/opposite-sign non-zero `roundAndPack` obligations from
guarded sign-ordered obligations plus explicit non-finite fallbacks. -/
theorem addFiniteRoundAndPackToSpecOrderedGuardedAutoNonzero_of_signOrderedGuarded_and_nonfinite
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode)
    (hsameNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = true →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .subnormal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .zero) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hprimaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteOppositeSignPrimaryRawExp a b)
            (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hsecondaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = false →
        addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode b.isNeg
            (addFiniteOppositeSignSecondaryRawExp a b)
            (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteRoundAndPackToSpecOrderedGuardedAutoNonzero spec mode := by
  exact ⟨
    addFiniteSameSignRoundAndPackToSpecOrderedGuarded_of_signOrderedGuarded_and_nonfinite
      spec mode hsame hsameNonfinite,
    addFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded_of_nonzeroToSpecOrderedGuarded_and_nonfinite
      spec mode hnonzero hprimaryNonfinite hsecondaryNonfinite
  ⟩

/-- Build bundled guarded roundAndPack-branch obligations (including zero branches)
from guarded sign-ordered obligations plus explicit non-finite fallbacks. -/
theorem addFiniteRoundAndPackBranchObligationsGuardedAutoNonzero_of_signOrderedGuarded_and_zeroBranches_and_nonfinite
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hsameNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = true →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .subnormal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .zero) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hprimaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteOppositeSignPrimaryRawExp a b)
            (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hsecondaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = false →
        addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode b.isNeg
            (addFiniteOppositeSignSecondaryRawExp a b)
            (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteRoundAndPackBranchObligationsGuardedAutoNonzero spec mode := by
  refine ⟨?_, hzeroPrimary, hzeroSecondary, ?_⟩
  · exact
      addFiniteSameSignRoundAndPackToSpecOrderedGuarded_of_signOrderedGuarded_and_nonfinite
        spec mode hsame hsameNonfinite
  · exact
      addFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded_of_nonzeroToSpecOrderedGuarded_and_nonfinite
        spec mode hnonzero hprimaryNonfinite hsecondaryNonfinite

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackBranches
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primarySecondary spec mode
    hzeroPrimary
    hzeroSecondary
    (addFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded_of_roundAndPack
      spec mode hprimaryCase hprimaryRound hprimaryDiff)
    (addFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded_of_roundAndPack
      spec mode hsecondaryCase hsecondaryRound hsecondaryDiff)

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackBranches_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primarySecondary spec mode
    hzeroPrimary
    hzeroSecondary
    (addFiniteOppositeSignPrimaryNonzeroToSpecOrderedGuarded_of_roundAndPack
      spec mode
      (addFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
      hprimaryRound
      (addFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded_default spec mode))
    (addFiniteOppositeSignSecondaryNonzeroToSpecOrderedGuarded_of_roundAndPack
      spec mode
      (addFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
      hsecondaryRound
      (addFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded_default spec mode))

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackObligations_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzero : AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero spec mode
    hzero
    (addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack_auto
      spec mode hprimaryRound hsecondaryRound)

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_branchFacts
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimaryDiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondaryDiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackBranches spec mode
    (addFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded_of_diffAndSpecZero
      spec mode hzeroPrimaryDiff hzeroPrimarySpec)
    (addFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded_of_diffAndSpecZero
      spec mode hzeroSecondaryDiff hzeroSecondarySpec)
    hprimaryCase hprimaryRound hprimaryDiff
    hsecondaryCase hsecondaryRound hsecondaryDiff

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_branchFacts_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimaryDiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondaryDiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackBranches spec mode
    (addFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded_of_diffAndSpecZero
      spec mode hzeroPrimaryDiff hzeroPrimarySpec)
    (addFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded_of_diffAndSpecZero
      spec mode hzeroSecondaryDiff hzeroSecondarySpec)
    (addFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
    hprimaryRound
    (addFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded_default spec mode)
    (addFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
    hsecondaryRound
    (addFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded_default spec mode)

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_branchSpecs_auto
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignZeroToSpecOrderedGuarded_of_primarySecondary spec mode
    (addFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded_of_specZeroOrRoundAndPack
      spec mode
      hzeroPrimarySpec
      (addFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
      hprimaryRound)
    (addFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded_of_specZeroOrRoundAndPack
      spec mode
      hzeroSecondarySpec
      (addFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded_default spec mode)
      hsecondaryRound)

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_branchSpecs_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero spec mode
    (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_branchSpecs_auto
      spec mode hzeroPrimarySpec hzeroSecondarySpec hprimaryRound hsecondaryRound)
    (addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack_auto
      spec mode hprimaryRound hsecondaryRound)

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_sumZeroAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hsum :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        (a.addFiniteOppositeSign b mode).value.classify = .zero →
        a.toReal + b.toReal = 0)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero spec mode
    (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_sumZero spec mode hsum)
    (addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack_auto
      spec mode hprimaryRound hsecondaryRound)

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_diffZeroSumsAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hsecondaryZeroSum : AddFiniteOppositeSignSecondaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_branchSpecs_autoNonzero spec mode
    (addFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded_of_sumZero
      spec mode hprimaryZeroSum)
    (addFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded_of_sumZero
      spec mode hsecondaryZeroSum)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_diffZeroSumsAndRoundAndPack_autoNonzero
    spec mode
    hprimaryZeroSum
    (addFiniteOppositeSignSecondaryZeroSumOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroReprMagEqAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroReprMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero
    spec mode
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroExtendedMagEqAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroExtendedMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero
    spec mode
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_extendedMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroExpEqAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero
    spec mode
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroReprExpEqAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroReprExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero
    spec mode
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprExpEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroAndRoundAndPack_autoNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  exact addFiniteOppositeSignToSpecOrderedGuarded_of_primaryDiffZeroExpEqAndRoundAndPack_autoNonzero
    spec mode
    (addFiniteOppositeSignPrimaryExpEqOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addFiniteOppositeSignFlagsToSpecOrdered_of_zeroNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzero : AddFiniteOppositeSignZeroFlagsToSpecOrdered spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroFlagsToSpecOrdered spec mode) :
    AddFiniteOppositeSignFlagsToSpecOrdered spec mode := by
  intro a b ha hb hge
  by_cases hcls0 : (a.addFiniteOppositeSign b mode).value.classify = .zero
  · exact hzero a b ha hb hge hcls0
  · exact hnonzero a b ha hb hge hcls0

theorem addFiniteOppositeSignZeroFlagsToSpecOrdered_of_addFiniteOppositeSignFlagsToSpecOrdered
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrdered spec mode) :
    AddFiniteOppositeSignZeroFlagsToSpecOrdered spec mode := by
  intro a b ha hb hge hzero
  exact hopp a b ha hb hge

theorem addFiniteOppositeSignNonzeroFlagsToSpecOrdered_of_addFiniteOppositeSignFlagsToSpecOrdered
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrdered spec mode) :
    AddFiniteOppositeSignNonzeroFlagsToSpecOrdered spec mode := by
  intro a b ha hb hge hnonzero
  exact hopp a b ha hb hge

theorem addFiniteOppositeSignFlagsToSpecOrderedGuarded_of_zeroNonzero
    (spec : BinarySpec) (mode : RoundingMode)
    (hzero : AddFiniteOppositeSignZeroFlagsToSpecOrderedGuarded spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn
  by_cases hcls0 : (a.addFiniteOppositeSign b mode).value.classify = .zero
  · exact hzero a b ha hb hge hsgn hcls0
  · exact hnonzero a b ha hb hge hsgn hcls0

theorem addFiniteOppositeSignZeroFlagsToSpecOrderedGuarded_of_addFiniteOppositeSignFlagsToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignZeroFlagsToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hzero
  exact hopp a b ha hb hge hsgn

theorem addFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded_of_addFiniteOppositeSignFlagsToSpecOrderedGuarded
    (spec : BinarySpec) (mode : RoundingMode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hnonzero
  exact hopp a b ha hb hge hsgn

private theorem addZeroResult_toReal (spec : BinarySpec) (a b : FloatBits spec) (mode : RoundingMode) :
    (if addZeroSign a b mode then FloatBits.negZero spec else FloatBits.posZero spec).toReal = 0 := by
  by_cases hsign : addZeroSign a b mode = true
  · simp [hsign, FloatBits.negZero_toReal]
  · simp [hsign, FloatBits.posZero_toReal]

private theorem addFiniteKernelToSpec_zero_right (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero)
    (hb : b.classify = .zero) :
    (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal := by
  have hb0 : b.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hb]
  rcases ha with ha | ha | ha
  · have hround : round spec.toFormat mode a.toReal = a.toReal :=
      toReal_round_id a (Or.inl ha) mode
    have himpl : (addFiniteKernelResult a b mode).value.toReal = a.toReal := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addSpec spec.toFormat mode a.toReal b.toReal = a.toReal := by
      simp [addSpec, hb0, hround]
    simpa [hspec] using himpl
  · have hround : round spec.toFormat mode a.toReal = a.toReal :=
      toReal_round_id a (Or.inr ha) mode
    have himpl : (addFiniteKernelResult a b mode).value.toReal = a.toReal := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addSpec spec.toFormat mode a.toReal b.toReal = a.toReal := by
      simp [addSpec, hb0, hround]
    simpa [hspec] using himpl
  · have ha0 : a.toReal = 0 := by
      unfold FloatBits.toReal
      rw [ha]
    have himpl : (addFiniteKernelResult a b mode).value.toReal = 0 := by
      simp [addFiniteKernelResult, ha, hb, addZeroResult_toReal]
    have hspec : addSpec spec.toFormat mode a.toReal b.toReal = 0 := by
      simp [addSpec, ha0, hb0, round_zero]
    simpa [hspec] using himpl

private theorem addFiniteKernelToSpec_zero_left (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .zero)
    (hb : b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) :
    (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal := by
  have ha0 : a.toReal = 0 := by
    unfold FloatBits.toReal
    rw [ha]
  rcases hb with hb | hb | hb
  · have hround : round spec.toFormat mode b.toReal = b.toReal :=
      toReal_round_id b (Or.inl hb) mode
    have himpl : (addFiniteKernelResult a b mode).value.toReal = b.toReal := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addSpec spec.toFormat mode a.toReal b.toReal = b.toReal := by
      simp [addSpec, ha0, hround]
    simpa [hspec] using himpl
  · have hround : round spec.toFormat mode b.toReal = b.toReal :=
      toReal_round_id b (Or.inr hb) mode
    have himpl : (addFiniteKernelResult a b mode).value.toReal = b.toReal := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addSpec spec.toFormat mode a.toReal b.toReal = b.toReal := by
      simp [addSpec, ha0, hround]
    simpa [hspec] using himpl
  · have hb0 : b.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hb]
    have himpl : (addFiniteKernelResult a b mode).value.toReal = 0 := by
      simp [addFiniteKernelResult, ha, hb, addZeroResult_toReal]
    have hspec : addSpec spec.toFormat mode a.toReal b.toReal = 0 := by
      simp [addSpec, ha0, hb0, round_zero]
    simpa [hspec] using himpl

theorem addFiniteKernelToSpec_of_cases (spec : BinarySpec) (mode : RoundingMode)
    (hzeroLeft :
      ∀ (a b : FloatBits spec),
        a.classify = .zero →
        (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
        (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal)
    (hzeroRight :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
        b.classify = .zero →
        (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal)
    (hff : AddFiniteKernelFiniteFiniteToSpec spec mode) :
    AddFiniteKernelToSpec spec mode := by
  intro a b ha hb hout
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · exact hff a b (Or.inl ha) (Or.inl hb) hout
    · exact hff a b (Or.inl ha) (Or.inr hb) hout
    · exact hzeroRight a b (Or.inl ha) hb
  · rcases hb with hb | hb | hb
    · exact hff a b (Or.inr ha) (Or.inl hb) hout
    · exact hff a b (Or.inr ha) (Or.inr hb) hout
    · exact hzeroRight a b (Or.inr (Or.inl ha)) hb
  · exact hzeroLeft a b ha hb

theorem addFiniteKernelFiniteFiniteToSpec_of_addFiniteKernelToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelToSpec spec mode) :
    AddFiniteKernelFiniteFiniteToSpec spec mode := by
  intro a b ha hb hout
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hkernel a b (Or.inl ha) (Or.inl hb) hout
  · exact hkernel a b (Or.inl ha) (Or.inr (Or.inl hb)) hout
  · exact hkernel a b (Or.inr (Or.inl ha)) (Or.inl hb) hout
  · exact hkernel a b (Or.inr (Or.inl ha)) (Or.inr (Or.inl hb)) hout

theorem addFiniteSameSignToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteToSpec spec mode) :
    AddFiniteSameSignToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hout
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inl ha) (Or.inl hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inl ha) (Or.inr hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inr ha) (Or.inl hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inr ha) (Or.inr hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase

theorem addFiniteOppositeSignToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteToSpec spec mode) :
    AddFiniteOppositeSignToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn hout
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inl ha) (Or.inl hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inl ha) (Or.inr hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inr ha) (Or.inl hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hout' :
        ((addFiniteKernelResult a b mode).value.classify = .normal ∨
          (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
          (addFiniteKernelResult a b mode).value.classify = .zero) := by
      simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hout
    have hcase := hff a b (Or.inr ha) (Or.inr hb) hout'
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase

theorem addFiniteOppositeSignZeroToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteToSpec spec mode) :
    AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode := by
  exact
    addFiniteOppositeSignZeroToSpecOrderedGuarded_of_addFiniteOppositeSignToSpecOrderedGuarded
      spec mode
      (addFiniteOppositeSignToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteToSpec spec mode hff)

theorem addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteToSpec spec mode) :
    AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode := by
  exact
    addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_addFiniteOppositeSignToSpecOrderedGuarded
      spec mode
      (addFiniteOppositeSignToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteToSpec spec mode hff)

theorem addFiniteKernelZeroLeftToSpec_of_addFiniteKernelToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelToSpec spec mode) :
    ∀ (a b : FloatBits spec),
      a.classify = .zero →
      (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
      (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal := by
  intro a b ha hb
  have hout :
      ((addFiniteKernelResult a b mode).value.classify = .normal ∨
        (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
        (addFiniteKernelResult a b mode).value.classify = .zero) := by
    rcases hb with hb | hb | hb
    · exact Or.inl (by simp [addFiniteKernelResult, ha, hb])
    · exact Or.inr (Or.inl (by simp [addFiniteKernelResult, ha, hb]))
    · exact Or.inr (Or.inr (by
        by_cases hzs : addZeroSign a b mode = true
        · simp [addFiniteKernelResult, ha, hb, hzs, FloatBits.negZero_classify]
        · simp [addFiniteKernelResult, ha, hb, hzs, FloatBits.posZero_classify]))
  exact hkernel a b (Or.inr (Or.inr ha)) hb hout

theorem addFiniteKernelZeroRightToSpec_of_addFiniteKernelToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelToSpec spec mode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
      b.classify = .zero →
      (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal := by
  intro a b ha hb
  have hout :
      ((addFiniteKernelResult a b mode).value.classify = .normal ∨
        (addFiniteKernelResult a b mode).value.classify = .subnormal ∨
        (addFiniteKernelResult a b mode).value.classify = .zero) := by
    rcases ha with ha | ha | ha
    · exact Or.inl (by simp [addFiniteKernelResult, ha, hb])
    · exact Or.inr (Or.inl (by simp [addFiniteKernelResult, ha, hb]))
    · exact Or.inr (Or.inr (by
        by_cases hzs : addZeroSign a b mode = true
        · simp [addFiniteKernelResult, ha, hb, hzs, FloatBits.negZero_classify]
        · simp [addFiniteKernelResult, ha, hb, hzs, FloatBits.posZero_classify]))
  exact hkernel a b ha (Or.inr (Or.inr hb)) hout

theorem addFiniteKernelToSpec_of_signOrdered (spec : BinarySpec) (mode : RoundingMode)
    (hzeroLeft :
      ∀ (a b : FloatBits spec),
        a.classify = .zero →
        (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
        (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal)
    (hzeroRight :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
        b.classify = .zero →
        (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteSameSign b mode).value.classify = .normal ∨
          (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
          (a.addFiniteSameSign b mode).value.classify = .zero) →
        (a.addFiniteSameSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .zero) →
        (a.addFiniteOppositeSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_cases spec mode hzeroLeft hzeroRight
    (addFiniteKernelFiniteFiniteToSpec_of_signOrdered spec mode hsame hopp)

theorem addFiniteKernelToSpec_of_signOrdered_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteSameSign b mode).value.classify = .normal ∨
          (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
          (a.addFiniteSameSign b mode).value.classify = .zero) →
        (a.addFiniteSameSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .zero) →
        (a.addFiniteOppositeSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrdered spec mode
    (addFiniteKernelToSpec_zero_left spec mode)
    (addFiniteKernelToSpec_zero_right spec mode)
    hsame hopp

theorem addFiniteKernelToSpec_of_signOrderedOppositeSplit_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrdered spec mode)
    (hoppZero : AddFiniteOppositeSignZeroToSpecOrdered spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroToSpecOrdered spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrdered_noZeroAssumptions spec mode hsame
    (addFiniteOppositeSignToSpecOrdered_of_zeroNonzero spec mode hoppZero hoppNonzero)

theorem addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_cases spec mode
    (addFiniteKernelToSpec_zero_left spec mode)
    (addFiniteKernelToSpec_zero_right spec mode)
    (addFiniteKernelFiniteFiniteToSpec_of_signOrderedGuarded spec mode hsame hopp)

theorem addFiniteKernelToSpec_of_signOrderedOppositeSplitGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hoppZero : AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode hsame
    (addFiniteOppositeSignToSpecOrderedGuarded_of_zeroNonzero spec mode hoppZero hoppNonzero)

theorem addFiniteKernelToSpec_of_roundAndPackBranchObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedOppositeSplitGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_primarySecondary spec mode hzeroPrimary hzeroSecondary)
    (addFiniteOppositeSignNonzeroToSpecOrderedGuarded_of_roundAndPack spec mode
      hprimaryCase hprimaryRound hprimaryDiff
      hsecondaryCase hsecondaryRound hsecondaryDiff)

theorem addFiniteKernelToSpec_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackBranches_autoNonzero spec mode
      hzeroPrimary hzeroSecondary hprimaryRound hsecondaryRound)

theorem addFiniteKernelToSpec_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions_bundle
    (spec : BinarySpec) (mode : RoundingMode)
    (h : AddFiniteRoundAndPackBranchObligationsGuardedAutoNonzero spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions
    spec mode
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem addFiniteKernelToSpec_of_roundAndPackObligationsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzero : AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackObligations_autoNonzero
      spec mode hzero hprimaryRound hsecondaryRound)

theorem addFiniteKernelToSpec_of_branchFactsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimaryDiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondaryDiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_branchFacts spec mode
      hzeroPrimaryDiff hzeroPrimarySpec
      hzeroSecondaryDiff hzeroSecondarySpec
      hprimaryCase hprimaryRound hprimaryDiff
      hsecondaryCase hsecondaryRound hsecondaryDiff)

theorem addFiniteKernelToSpec_of_branchFactsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimaryDiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondaryDiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_branchFacts_autoNonzero spec mode
      hzeroPrimaryDiff hzeroPrimarySpec
      hzeroSecondaryDiff hzeroSecondarySpec
      hprimaryRound hsecondaryRound)

theorem addFiniteKernelToSpec_of_branchSpecsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_branchSpecs_autoNonzero spec mode
      hzeroPrimarySpec hzeroSecondarySpec
      hprimaryRound hsecondaryRound)

theorem addFiniteKernelToSpec_of_exactRepresentableAndSumZeroRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hsameRepr : AddFiniteSameSignRepresentableOrderedGuarded spec mode)
    (hoppSumZero : AddFiniteOppositeSignZeroSumOrderedGuarded spec mode)
    (hoppPrimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hoppSecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_exactAndRepresentable
      spec mode hsameExact hsameRepr)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_sumZeroAndRoundAndPack_autoNonzero
      spec mode hoppSumZero hoppPrimaryRound hoppSecondaryRound)

theorem addFiniteKernelToSpec_of_exactAndSumZeroRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppSumZero : AddFiniteOppositeSignZeroSumOrderedGuarded spec mode)
    (hoppPrimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hoppSecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_exact spec mode hsameExact)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackObligations_autoNonzero
      spec mode
      (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_exact spec mode
        (addFiniteOppositeSignZeroExactOrderedGuarded_of_sumZero spec mode hoppSumZero))
      hoppPrimaryRound hoppSecondaryRound)

theorem addFiniteKernelToSpec_of_exactAndZeroExactRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppZeroExact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hoppPrimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hoppSecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_exact spec mode hsameExact)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_roundAndPackObligations_autoNonzero
      spec mode
      (addFiniteOppositeSignZeroToSpecOrderedGuarded_of_exact spec mode hoppZeroExact)
      hoppPrimaryRound hoppSecondaryRound)

theorem addFiniteKernelToSpec_of_exact_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppZeroExact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hoppNonzeroExact : AddFiniteOppositeSignNonzeroExactOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_exact spec mode hsameExact)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_exact spec mode
      hoppZeroExact hoppNonzeroExact)

theorem addFiniteKernelToSpec_of_diffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hsecondaryZeroSum : AddFiniteOppositeSignSecondaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_roundAndPack spec mode hsameRound)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_diffZeroSumsAndRoundAndPack_autoNonzero
      spec mode hprimaryZeroSum hsecondaryZeroSum hprimaryRound hsecondaryRound)

theorem addFiniteKernelToSpec_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_diffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    hprimaryZeroSum
    (addFiniteOppositeSignSecondaryZeroSumOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addFiniteKernelToSpec_of_primaryDiffZeroReprMagEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroReprMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addFiniteKernelToSpec_of_primaryDiffZeroExtendedMagEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroExtendedMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_extendedMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addFiniteKernelToSpec_of_primaryDiffZeroExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addFiniteKernelToSpec_of_primaryDiffZeroReprExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroReprExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprExpEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addFiniteKernelToSpec_of_primaryDiffZeroAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_primaryDiffZeroExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryExpEqOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addFiniteKernelToSpec_of_exactAndDiffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hsecondaryZeroSum : AddFiniteOppositeSignSecondaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode
    (addFiniteSameSignToSpecOrderedGuarded_of_exact spec mode hsameExact)
    (addFiniteOppositeSignToSpecOrderedGuarded_of_diffZeroSumsAndRoundAndPack_autoNonzero
      spec mode hprimaryZeroSum hsecondaryZeroSum hprimaryRound hsecondaryRound)

theorem addFiniteKernelToSpec_of_exactAndPrimaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddFiniteKernelToSpec spec mode := by
  exact addFiniteKernelToSpec_of_exactAndDiffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    hprimaryZeroSum
    (addFiniteOppositeSignSecondaryZeroSumOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_signOrdered (spec : BinarySpec) (mode : RoundingMode)
    (hzeroLeft :
      ∀ (a b : FloatBits spec),
        a.classify = .zero →
        (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
        (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal)
    (hzeroRight :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
        b.classify = .zero →
        (addFiniteKernelResult a b mode).value.toReal = addSpec spec.toFormat mode a.toReal b.toReal)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteSameSign b mode).value.classify = .normal ∨
          (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
          (a.addFiniteSameSign b mode).value.classify = .zero) →
        (a.addFiniteSameSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .zero) →
        (a.addFiniteOppositeSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_signOrdered spec mode hzeroLeft hzeroRight hsame hopp)

theorem addBitEquiv_of_signOrdered_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteSameSign b mode).value.classify = .normal ∨
          (a.addFiniteSameSign b mode).value.classify = .subnormal ∨
          (a.addFiniteSameSign b mode).value.classify = .zero) →
        (a.addFiniteSameSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        ((a.addFiniteOppositeSign b mode).value.classify = .normal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .subnormal ∨
          (a.addFiniteOppositeSign b mode).value.classify = .zero) →
        (a.addFiniteOppositeSign b mode).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_signOrdered_noZeroAssumptions spec mode hsame hopp)

theorem addBitEquiv_of_signObligations_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrdered spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrdered spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_signOrdered_noZeroAssumptions spec mode hsame hopp

theorem addBitEquiv_of_signOrderedOppositeSplit_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrdered spec mode)
    (hoppZero : AddFiniteOppositeSignZeroToSpecOrdered spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroToSpecOrdered spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_signOrderedOppositeSplit_noZeroAssumptions
      spec mode hsame hoppZero hoppNonzero)

theorem addBitEquiv_of_signOrderedGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode hsame hopp)

theorem addBitEquiv_of_signObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_signOrderedGuarded_noZeroAssumptions spec mode hsame hopp

theorem addBitEquiv_of_signOrderedOppositeSplitGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hoppZero : AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_signOrderedOppositeSplitGuarded_noZeroAssumptions
      spec mode hsame hoppZero hoppNonzero)

theorem addBitEquiv_of_roundAndPackBranchObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_roundAndPackBranchObligationsGuarded_noZeroAssumptions spec mode
      hsameRound
      hzeroPrimary hzeroSecondary
      hprimaryCase hprimaryRound hprimaryDiff
      hsecondaryCase hsecondaryRound hsecondaryDiff)

theorem addBitEquiv_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions
      spec mode hsameRound hzeroPrimary hzeroSecondary hprimaryRound hsecondaryRound)

theorem addBitEquiv_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions_bundle
    (spec : BinarySpec) (mode : RoundingMode)
    (h : AddFiniteRoundAndPackBranchObligationsGuardedAutoNonzero spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions
    spec mode
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem addBitEquiv_of_roundAndPackObligationsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzero : AddFiniteOppositeSignZeroToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_roundAndPackObligationsGuarded_autoNonzero_noZeroAssumptions
      spec mode hsameRound hzero hprimaryRound hsecondaryRound)

theorem addBitEquiv_of_branchFactsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimaryDiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondaryDiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryCase : AddFiniteOppositeSignPrimaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryDiff : AddFiniteOppositeSignPrimaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode)
    (hsecondaryCase : AddFiniteOppositeSignSecondaryCaseRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryDiff : AddFiniteOppositeSignSecondaryNonzeroDiffNonzeroToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_branchFactsGuarded_noZeroAssumptions spec mode
      hsameRound
      hzeroPrimaryDiff hzeroPrimarySpec
      hzeroSecondaryDiff hzeroSecondarySpec
      hprimaryCase hprimaryRound hprimaryDiff
      hsecondaryCase hsecondaryRound hsecondaryDiff)

theorem addBitEquiv_of_branchFactsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimaryDiff : AddFiniteOppositeSignPrimaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondaryDiff : AddFiniteOppositeSignSecondaryZeroDiffZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_branchFactsGuarded_autoNonzero_noZeroAssumptions spec mode
      hsameRound
      hzeroPrimaryDiff hzeroPrimarySpec
      hzeroSecondaryDiff hzeroSecondarySpec
      hprimaryRound hsecondaryRound)

theorem addBitEquiv_of_branchSpecsGuarded_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hzeroPrimarySpec : AddFiniteOppositeSignPrimaryZeroSpecToSpecOrderedGuarded spec mode)
    (hzeroSecondarySpec : AddFiniteOppositeSignSecondaryZeroSpecToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_branchSpecsGuarded_autoNonzero_noZeroAssumptions spec mode
      hsameRound hzeroPrimarySpec hzeroSecondarySpec hprimaryRound hsecondaryRound)

theorem addBitEquiv_of_exactRepresentableAndSumZeroRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hsameRepr : AddFiniteSameSignRepresentableOrderedGuarded spec mode)
    (hoppSumZero : AddFiniteOppositeSignZeroSumOrderedGuarded spec mode)
    (hoppPrimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hoppSecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_exactRepresentableAndSumZeroRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode
      hsameExact hsameRepr
      hoppSumZero
      hoppPrimaryRound hoppSecondaryRound)

theorem addBitEquiv_of_exactAndSumZeroRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppSumZero : AddFiniteOppositeSignZeroSumOrderedGuarded spec mode)
    (hoppPrimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hoppSecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_exactAndSumZeroRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode hsameExact hoppSumZero hoppPrimaryRound hoppSecondaryRound)

theorem addBitEquiv_of_exactAndZeroExactRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppZeroExact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hoppPrimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hoppSecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_exactAndZeroExactRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode hsameExact hoppZeroExact hoppPrimaryRound hoppSecondaryRound)

theorem addBitEquiv_of_exact_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppZeroExact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hoppNonzeroExact : AddFiniteOppositeSignNonzeroExactOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_exact_noZeroAssumptions spec mode
      hsameExact hoppZeroExact hoppNonzeroExact)

theorem addBitEquiv_of_diffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hsecondaryZeroSum : AddFiniteOppositeSignSecondaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_diffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode hsameRound hprimaryZeroSum hsecondaryZeroSum hprimaryRound hsecondaryRound)

theorem addBitEquiv_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_diffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    hprimaryZeroSum
    (addFiniteOppositeSignSecondaryZeroSumOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_primaryDiffZeroReprMagEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroReprMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_primaryDiffZeroExtendedMagEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroExtendedMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_extendedMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_primaryDiffZeroExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_primaryDiffZeroReprExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroReprExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_primaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprExpEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_primaryDiffZeroExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameRound
    (addFiniteOppositeSignPrimaryExpEqOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_exactAndDiffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hsecondaryZeroSum : AddFiniteOppositeSignSecondaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_addFiniteKernelToSpec spec mode
    (addFiniteKernelToSpec_of_exactAndDiffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode hsameExact hprimaryZeroSum hsecondaryZeroSum hprimaryRound hsecondaryRound)

theorem addBitEquiv_of_exactAndPrimaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryZeroSum : AddFiniteOppositeSignPrimaryZeroSumOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_exactAndDiffZeroSumsAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    hprimaryZeroSum
    (addFiniteOppositeSignSecondaryZeroSumOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_exactAndPrimaryDiffZeroReprMagEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroReprMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_exactAndPrimaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_exactAndPrimaryDiffZeroExtendedMagEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryMagEq : AddFiniteOppositeSignPrimaryDiffZeroExtendedMagEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_exactAndPrimaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_extendedMagEq spec mode hprimaryMagEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_exactAndPrimaryDiffZeroExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_exactAndPrimaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_expEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_exactAndPrimaryDiffZeroReprExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryExpEq : AddFiniteOppositeSignPrimaryDiffZeroReprExpEqOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_exactAndPrimaryDiffZeroSumAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    (addFiniteOppositeSignPrimaryZeroSumOrderedGuarded_of_reprExpEq spec mode hprimaryExpEq)
    hprimaryRound hsecondaryRound

theorem addBitEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode := by
  exact addBitEquiv_of_exactAndPrimaryDiffZeroExpEqAndRoundAndPack_autoNonzero_noZeroAssumptions
    spec mode
    hsameExact
    (addFiniteOppositeSignPrimaryExpEqOrderedGuarded_auto spec mode)
    hprimaryRound hsecondaryRound

/-- Split the ordered finite/non-zero flag obligation by sign parity. -/
theorem addFiniteKernelFiniteFiniteFlagsToSpec_of_signOrdered (spec : BinarySpec) (mode : RoundingMode)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteSameSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteOppositeSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteKernelFiniteFiniteFlagsToSpec spec mode := by
  intro a b ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inl hb) hge
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inl ha) (Or.inl hb) hge
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : b.isNeg == a.isNeg
      · have hswap := hsame b a (Or.inl hb) (Or.inl ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'

      · have hswap := hopp b a (Or.inl hb) (Or.inl ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inr hb) hge
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inl ha) (Or.inr hb) hge
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : b.isNeg == a.isNeg
      · have hswap := hsame b a (Or.inr hb) (Or.inl ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hswap := hopp b a (Or.inr hb) (Or.inl ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inl hb) hge
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inr ha) (Or.inl hb) hge
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : b.isNeg == a.isNeg
      · have hswap := hsame b a (Or.inl hb) (Or.inr ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hswap := hopp b a (Or.inl hb) (Or.inr ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : a.isNeg == b.isNeg
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inr hb) hge
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hopp a b (Or.inr ha) (Or.inr hb) hge
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : b.isNeg == a.isNeg
      · have hswap := hsame b a (Or.inr hb) (Or.inr ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hswap := hopp b a (Or.inr hb) (Or.inr ha) hba_true
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'

theorem addFiniteKernelFiniteFiniteFlagsToSpec_of_signObligations (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrdered spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrdered spec mode) :
    AddFiniteKernelFiniteFiniteFlagsToSpec spec mode := by
  exact addFiniteKernelFiniteFiniteFlagsToSpec_of_signOrdered spec mode hsame hopp

theorem addFiniteKernelFiniteFiniteFlagsToSpec_of_signOrderedGuarded (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteKernelFiniteFiniteFlagsToSpec spec mode := by
  intro a b ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inl hb) hge hsgn
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inl ha) (Or.inl hb) hge hsgn_false
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have hswap := hsame b a (Or.inl hb) (Or.inl ha) hba_true hsgn
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have hswap := hopp b a (Or.inl hb) (Or.inl ha) hba_true hsgn_false
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inl ha) (Or.inr hb) hge hsgn
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inl ha) (Or.inr hb) hge hsgn_false
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have hswap := hsame b a (Or.inr hb) (Or.inl ha) hba_true hsgn
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have hswap := hopp b a (Or.inr hb) (Or.inl ha) hba_true hsgn_false
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inl hb) hge hsgn
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inr ha) (Or.inl hb) hge hsgn_false
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have hswap := hsame b a (Or.inl hb) (Or.inr ha) hba_true hsgn
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have hswap := hopp b a (Or.inl hb) (Or.inr ha) hba_true hsgn_false
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
  · by_cases hge : FloatBits.finiteMagGE a b = true
    · by_cases hsgn : (a.isNeg == b.isNeg) = true
      · simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using
          hsame a b (Or.inr ha) (Or.inr hb) hge hsgn
      · have hsgn_false : (a.isNeg == b.isNeg) = false := by
          cases hbool : (a.isNeg == b.isNeg) <;> simp [hbool] at hsgn ⊢
        simpa [addFiniteKernelResult, ha, hb, hge, hsgn_false] using
          hopp a b (Or.inr ha) (Or.inr hb) hge hsgn_false
    · have hab_false : FloatBits.finiteMagGE a b = false := by
        cases hbool : FloatBits.finiteMagGE a b <;> simp [hbool] at hge ⊢
      have hba_true : FloatBits.finiteMagGE b a = true := by
        rcases finiteMagGE_total a b with hab_true | hba_true
        · simp [hab_false] at hab_true
        · exact hba_true
      by_cases hsgn : (b.isNeg == a.isNeg) = true
      · have hswap := hsame b a (Or.inr hb) (Or.inr ha) hba_true hsgn
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'
      · have hsgn_false : (b.isNeg == a.isNeg) = false := by
          cases hbool : (b.isNeg == a.isNeg) <;> simp [hbool] at hsgn ⊢
        have hswap := hopp b a (Or.inr hb) (Or.inr ha) hba_true hsgn_false
        have hswap' :
            (if b.isNeg == a.isNeg then
                b.addFiniteSameSign a mode
              else
                b.addFiniteOppositeSign a mode).flags =
              addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
          simpa [hsgn_false] using hswap.trans (addFlagsSpec_comm spec.toFormat mode b.toReal a.toReal)
        simpa [addFiniteKernelResult, ha, hb, hab_false] using hswap'

theorem addFiniteKernelFiniteFiniteFlagsToSpec_of_signObligationsGuarded
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteKernelFiniteFiniteFlagsToSpec spec mode := by
  exact addFiniteKernelFiniteFiniteFlagsToSpec_of_signOrderedGuarded spec mode hsame hopp

private theorem addFiniteKernelFlagsToSpec_zero_right (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero)
    (hb : b.classify = .zero) :
    (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  have hb0 : b.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hb]
  rcases ha with ha | ha | ha
  · have hround : round spec.toFormat mode a.toReal = a.toReal :=
      toReal_round_id a (Or.inl ha) mode
    have hover : overflowFlag spec.toFormat a.toReal = false :=
      overflowFlag_toReal_false_of_finite a (Or.inl ha)
    have himpl : (addFiniteKernelResult a b mode).flags = {} := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
      rw [addFlagsSpec_correct, roundedFlagsSpec_correct]
      simp [hb0, addSpec, hround, hover, inexactFlag, underflowFlag]
    simpa [hspec] using himpl
  · have hround : round spec.toFormat mode a.toReal = a.toReal :=
      toReal_round_id a (Or.inr ha) mode
    have hover : overflowFlag spec.toFormat a.toReal = false :=
      overflowFlag_toReal_false_of_finite a (Or.inr ha)
    have himpl : (addFiniteKernelResult a b mode).flags = {} := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
      rw [addFlagsSpec_correct, roundedFlagsSpec_correct]
      simp [hb0, addSpec, hround, hover, inexactFlag, underflowFlag]
    simpa [hspec] using himpl
  · have ha0 : a.toReal = 0 := by
      unfold FloatBits.toReal
      rw [ha]
    have hover0 : overflowFlag spec.toFormat 0 = false := overflowFlag_zero_false spec.toFormat
    have himpl : (addFiniteKernelResult a b mode).flags = {} := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
      rw [addFlagsSpec_correct, roundedFlagsSpec_correct]
      simp [ha0, hb0, addSpec, round_zero, hover0, inexactFlag, underflowFlag]
    simpa [hspec] using himpl

private theorem addFiniteKernelFlagsToSpec_zero_left (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .zero)
    (hb : b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) :
    (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  have ha0 : a.toReal = 0 := by
    unfold FloatBits.toReal
    rw [ha]
  rcases hb with hb | hb | hb
  · have hround : round spec.toFormat mode b.toReal = b.toReal :=
      toReal_round_id b (Or.inl hb) mode
    have hover : overflowFlag spec.toFormat b.toReal = false :=
      overflowFlag_toReal_false_of_finite b (Or.inl hb)
    have himpl : (addFiniteKernelResult a b mode).flags = {} := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
      rw [addFlagsSpec_correct, roundedFlagsSpec_correct]
      simp [ha0, addSpec, hround, hover, inexactFlag, underflowFlag]
    simpa [hspec] using himpl
  · have hround : round spec.toFormat mode b.toReal = b.toReal :=
      toReal_round_id b (Or.inr hb) mode
    have hover : overflowFlag spec.toFormat b.toReal = false :=
      overflowFlag_toReal_false_of_finite b (Or.inr hb)
    have himpl : (addFiniteKernelResult a b mode).flags = {} := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
      rw [addFlagsSpec_correct, roundedFlagsSpec_correct]
      simp [ha0, addSpec, hround, hover, inexactFlag, underflowFlag]
    simpa [hspec] using himpl
  · have hb0 : b.toReal = 0 := by
      unfold FloatBits.toReal
      rw [hb]
    have hover0 : overflowFlag spec.toFormat 0 = false := overflowFlag_zero_false spec.toFormat
    have himpl : (addFiniteKernelResult a b mode).flags = {} := by
      simp [addFiniteKernelResult, ha, hb]
    have hspec : addFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
      rw [addFlagsSpec_correct, roundedFlagsSpec_correct]
      simp [ha0, hb0, addSpec, round_zero, hover0, inexactFlag, underflowFlag]
    simpa [hspec] using himpl

/-- Decomposition for flags: isolate zero-side obligations from non-zero/non-zero kernel flags. -/
theorem addFiniteKernelFlagsToSpec_of_cases (spec : BinarySpec) (mode : RoundingMode)
    (hzeroLeft :
      ∀ (a b : FloatBits spec),
        a.classify = .zero →
        (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
        (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hzeroRight :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
        b.classify = .zero →
        (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hff : AddFiniteKernelFiniteFiniteFlagsToSpec spec mode) :
    AddFiniteKernelFlagsToSpec spec mode := by
  intro a b ha hb
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · exact hff a b (Or.inl ha) (Or.inl hb)
    · exact hff a b (Or.inl ha) (Or.inr hb)
    · exact hzeroRight a b (Or.inl ha) hb
  · rcases hb with hb | hb | hb
    · exact hff a b (Or.inr ha) (Or.inl hb)
    · exact hff a b (Or.inr ha) (Or.inr hb)
    · exact hzeroRight a b (Or.inr (Or.inl ha)) hb
  · exact hzeroLeft a b ha hb

theorem addFiniteKernelFiniteFiniteFlagsToSpec_of_addFiniteKernelFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelFlagsToSpec spec mode) :
    AddFiniteKernelFiniteFiniteFlagsToSpec spec mode := by
  intro a b ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hkernel a b (Or.inl ha) (Or.inl hb)
  · exact hkernel a b (Or.inl ha) (Or.inr (Or.inl hb))
  · exact hkernel a b (Or.inr (Or.inl ha)) (Or.inl hb)
  · exact hkernel a b (Or.inr (Or.inl ha)) (Or.inr (Or.inl hb))

theorem addFiniteSameSignFlagsToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteFlagsToSpec spec mode) :
    AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hcase := hff a b (Or.inl ha) (Or.inl hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hcase := hff a b (Or.inl ha) (Or.inr hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hcase := hff a b (Or.inr ha) (Or.inl hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hcase := hff a b (Or.inr ha) (Or.inr hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase

theorem addFiniteOppositeSignFlagsToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteFlagsToSpec spec mode) :
    AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode := by
  intro a b ha hb hge hsgn
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hcase := hff a b (Or.inl ha) (Or.inl hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hcase := hff a b (Or.inl ha) (Or.inr hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hcase := hff a b (Or.inr ha) (Or.inl hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase
  · have hcase := hff a b (Or.inr ha) (Or.inr hb)
    simpa [addFiniteKernelResult, ha, hb, hge, hsgn] using hcase

theorem addFiniteOppositeSignZeroFlagsToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteFlagsToSpec spec mode) :
    AddFiniteOppositeSignZeroFlagsToSpecOrderedGuarded spec mode := by
  exact
    addFiniteOppositeSignZeroFlagsToSpecOrderedGuarded_of_addFiniteOppositeSignFlagsToSpecOrderedGuarded
      spec mode
      (addFiniteOppositeSignFlagsToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteFlagsToSpec
        spec mode hff)

theorem addFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hff : AddFiniteKernelFiniteFiniteFlagsToSpec spec mode) :
    AddFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded spec mode := by
  exact
    addFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded_of_addFiniteOppositeSignFlagsToSpecOrderedGuarded
      spec mode
      (addFiniteOppositeSignFlagsToSpecOrderedGuarded_of_addFiniteKernelFiniteFiniteFlagsToSpec
        spec mode hff)

theorem addFiniteKernelZeroLeftFlagsToSpec_of_addFiniteKernelFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelFlagsToSpec spec mode) :
    ∀ (a b : FloatBits spec),
      a.classify = .zero →
      (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
      (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  intro a b ha hb
  exact hkernel a b (Or.inr (Or.inr ha)) hb

theorem addFiniteKernelZeroRightFlagsToSpec_of_addFiniteKernelFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelFlagsToSpec spec mode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
      b.classify = .zero →
      (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  intro a b ha hb
  exact hkernel a b ha (Or.inr (Or.inr hb))

theorem addFiniteKernelFlagsToSpec_of_signOrdered (spec : BinarySpec) (mode : RoundingMode)
    (hzeroLeft :
      ∀ (a b : FloatBits spec),
        a.classify = .zero →
        (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
        (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hzeroRight :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
        b.classify = .zero →
        (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteSameSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteOppositeSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteKernelFlagsToSpec spec mode := by
  exact addFiniteKernelFlagsToSpec_of_cases spec mode hzeroLeft hzeroRight
    (addFiniteKernelFiniteFiniteFlagsToSpec_of_signOrdered spec mode hsame hopp)

theorem addFiniteKernelFlagsToSpec_of_signOrdered_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteSameSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteOppositeSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    AddFiniteKernelFlagsToSpec spec mode := by
  exact addFiniteKernelFlagsToSpec_of_signOrdered spec mode
    (addFiniteKernelFlagsToSpec_zero_left spec mode)
    (addFiniteKernelFlagsToSpec_zero_right spec mode)
    hsame hopp

theorem addFiniteKernelFlagsToSpec_of_signOrderedGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteKernelFlagsToSpec spec mode := by
  exact addFiniteKernelFlagsToSpec_of_cases spec mode
    (addFiniteKernelFlagsToSpec_zero_left spec mode)
    (addFiniteKernelFlagsToSpec_zero_right spec mode)
    (addFiniteKernelFiniteFiniteFlagsToSpec_of_signOrderedGuarded spec mode hsame hopp)

theorem addFiniteKernelFlagsToSpec_of_signOrderedOppositeSplit_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrdered spec mode)
    (hoppZero : AddFiniteOppositeSignZeroFlagsToSpecOrdered spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroFlagsToSpecOrdered spec mode) :
    AddFiniteKernelFlagsToSpec spec mode := by
  exact addFiniteKernelFlagsToSpec_of_signOrdered_noZeroAssumptions spec mode hsame
    (addFiniteOppositeSignFlagsToSpecOrdered_of_zeroNonzero spec mode hoppZero hoppNonzero)

theorem addFiniteKernelFlagsToSpec_of_signOrderedOppositeSplitGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hoppZero : AddFiniteOppositeSignZeroFlagsToSpecOrderedGuarded spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded spec mode) :
    AddFiniteKernelFlagsToSpec spec mode := by
  exact addFiniteKernelFlagsToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode hsame
    (addFiniteOppositeSignFlagsToSpecOrderedGuarded_of_zeroNonzero spec mode hoppZero hoppNonzero)

theorem addBitFlagEquiv_of_addFiniteKernelFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hkernel : AddFiniteKernelFlagsToSpec spec mode) :
    AddBitFlagEquiv spec mode := by
  intro a b ha hb
  calc
    (a.add b mode).flags = (addFiniteKernelResult a b mode).flags := addBitFlagEquiv spec mode a b ha hb
    _ = addFlagsSpec spec.toFormat mode a.toReal b.toReal := hkernel a b ha hb

theorem addBitFlagEquiv_of_signOrdered (spec : BinarySpec) (mode : RoundingMode)
    (hzeroLeft :
      ∀ (a b : FloatBits spec),
        a.classify = .zero →
        (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
        (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hzeroRight :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
        b.classify = .zero →
        (addFiniteKernelResult a b mode).flags = addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteSameSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteOppositeSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_addFiniteKernelFlagsToSpec spec mode
    (addFiniteKernelFlagsToSpec_of_signOrdered spec mode hzeroLeft hzeroRight hsame hopp)

theorem addBitFlagEquiv_of_signOrdered_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteSameSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hopp :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.addFiniteOppositeSign b mode).flags =
          addFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_addFiniteKernelFlagsToSpec spec mode
    (addFiniteKernelFlagsToSpec_of_signOrdered_noZeroAssumptions spec mode hsame hopp)

theorem addBitFlagEquiv_of_signOrderedGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_addFiniteKernelFlagsToSpec spec mode
    (addFiniteKernelFlagsToSpec_of_signOrderedGuarded_noZeroAssumptions spec mode hsame hopp)

theorem addBitFlagEquiv_of_signOrderedOppositeSplit_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrdered spec mode)
    (hoppZero : AddFiniteOppositeSignZeroFlagsToSpecOrdered spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroFlagsToSpecOrdered spec mode) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_addFiniteKernelFlagsToSpec spec mode
    (addFiniteKernelFlagsToSpec_of_signOrderedOppositeSplit_noZeroAssumptions
      spec mode hsame hoppZero hoppNonzero)

theorem addBitFlagEquiv_of_signOrderedOppositeSplitGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hoppZero : AddFiniteOppositeSignZeroFlagsToSpecOrderedGuarded spec mode)
    (hoppNonzero : AddFiniteOppositeSignNonzeroFlagsToSpecOrderedGuarded spec mode) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_addFiniteKernelFlagsToSpec spec mode
    (addFiniteKernelFlagsToSpec_of_signOrderedOppositeSplitGuarded_noZeroAssumptions
      spec mode hsame hoppZero hoppNonzero)

theorem addBitFlagEquiv_of_signObligations_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrdered spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrdered spec mode) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_signOrdered_noZeroAssumptions spec mode hsame hopp

theorem addBitFlagEquiv_of_signObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hopp : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitFlagEquiv spec mode := by
  exact addBitFlagEquiv_of_signOrderedGuarded_noZeroAssumptions spec mode hsame hopp

theorem addBitEquivAndFlagEquiv_of_addFiniteKernelObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hval : AddFiniteKernelToSpec spec mode)
    (hflag : AddFiniteKernelFlagsToSpec spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact ⟨
    addBitEquiv_of_addFiniteKernelToSpec spec mode hval,
    addBitFlagEquiv_of_addFiniteKernelFlagsToSpec spec mode hflag
  ⟩

theorem addBitEquivAndFlagEquiv_of_signObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameVal : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hoppVal : AddFiniteOppositeSignToSpecOrderedGuarded spec mode)
    (hsameFlag : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hoppFlag : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact ⟨
    addBitEquiv_of_signObligationsGuarded_noZeroAssumptions spec mode hsameVal hoppVal,
    addBitFlagEquiv_of_signObligationsGuarded_noZeroAssumptions spec mode hsameFlag hoppFlag
  ⟩

theorem addBitEquivAndFlagEquiv_of_exactAndSignFlagObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hoppZeroExact : AddFiniteOppositeSignZeroExactOrderedGuarded spec mode)
    (hoppNonzeroExact : AddFiniteOppositeSignNonzeroExactOrderedGuarded spec mode)
    (hsameFlag : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hoppFlag : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact ⟨
    addBitEquiv_of_exact_noZeroAssumptions spec mode
      hsameExact hoppZeroExact hoppNonzeroExact,
    addBitFlagEquiv_of_signObligationsGuarded_noZeroAssumptions spec mode
      hsameFlag hoppFlag
  ⟩

theorem addBitEquivAndFlagEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameRound : AddFiniteSameSignRoundAndPackToSpecOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsameFlag : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hoppFlag : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact ⟨
    addBitEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode hsameRound hprimaryRound hsecondaryRound,
    addBitFlagEquiv_of_signObligationsGuarded_noZeroAssumptions spec mode
      hsameFlag hoppFlag
  ⟩

theorem addBitEquivAndFlagEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hprimaryRound : AddFiniteOppositeSignPrimaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsecondaryRound : AddFiniteOppositeSignSecondaryNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hsameFlag : AddFiniteSameSignFlagsToSpecOrderedGuarded spec mode)
    (hoppFlag : AddFiniteOppositeSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact ⟨
    addBitEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_noZeroAssumptions
      spec mode hsameExact hprimaryRound hsecondaryRound,
    addBitFlagEquiv_of_signObligationsGuarded_noZeroAssumptions spec mode
      hsameFlag hoppFlag
  ⟩

theorem addBitEquivAndFlagEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions_bundled
    (spec : BinarySpec) (mode : RoundingMode)
    (hround : AddFiniteRoundAndPackToSpecOrderedGuardedAutoNonzero spec mode)
    (hflags : AddSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact addBitEquivAndFlagEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions
    spec mode
    hround.1 hround.2.1 hround.2.2
    hflags.1 hflags.2

theorem addBitEquivAndFlagEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions_bundled
    (spec : BinarySpec) (mode : RoundingMode)
    (hsameExact : AddFiniteSameSignExactOrderedGuarded spec mode)
    (hround : AddFiniteOppositeSignNonzeroRoundAndPackToSpecOrderedGuarded spec mode)
    (hflags : AddSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact addBitEquivAndFlagEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions
    spec mode
    hsameExact hround.1 hround.2
    hflags.1 hflags.2

theorem addBitEquivAndFlagEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions_bundle
    (spec : BinarySpec) (mode : RoundingMode)
    (h : AddPrimaryDiffZeroRoundAndSignFlagsObligationsGuardedAutoNonzero spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact addBitEquivAndFlagEquiv_of_primaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions_bundled
    spec mode h.1 h.2

theorem addBitEquivAndFlagEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions_bundle
    (spec : BinarySpec) (mode : RoundingMode)
    (h : AddExactAndPrimaryDiffZeroRoundAndSignFlagsObligationsGuardedAutoNonzero spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact addBitEquivAndFlagEquiv_of_exactAndPrimaryDiffZeroAndRoundAndPack_autoNonzero_andSignFlagObligationsGuarded_noZeroAssumptions_bundled
    spec mode h.1 h.2.1 h.2.2

theorem addBitEquivAndFlagEquiv_of_roundAndPackBranchObligationsGuarded_autoNonzero_andSignFlagObligations_noZeroAssumptions_bundle
    (spec : BinarySpec) (mode : RoundingMode)
    (hround : AddFiniteRoundAndPackBranchObligationsGuardedAutoNonzero spec mode)
    (hflags : AddSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact ⟨
    addBitEquiv_of_roundAndPackBranchObligationsGuarded_autoNonzero_noZeroAssumptions_bundle
      spec mode hround,
    addBitFlagEquiv_of_signObligationsGuarded_noZeroAssumptions spec mode
      hflags.1 hflags.2
  ⟩

theorem addBitEquivAndFlagEquiv_of_signOrderedGuarded_and_zeroBranches_and_roundAndPackNonfinite_andSignFlagObligations_noZeroAssumptions
    (spec : BinarySpec) (mode : RoundingMode)
    (hsame : AddFiniteSameSignToSpecOrderedGuarded spec mode)
    (hnonzero : AddFiniteOppositeSignNonzeroToSpecOrderedGuarded spec mode)
    (hzeroPrimary : AddFiniteOppositeSignPrimaryZeroToSpecOrderedGuarded spec mode)
    (hzeroSecondary : AddFiniteOppositeSignSecondaryZeroToSpecOrderedGuarded spec mode)
    (hsameNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = true →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .subnormal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.classify = .zero) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteSameSignRawExp a b) (addFiniteSameSignRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hprimaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = true →
        addFiniteOppositeSignPrimaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode a.isNeg
            (addFiniteOppositeSignPrimaryRawExp a b)
            (addFiniteOppositeSignPrimaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode a.isNeg
          (addFiniteOppositeSignPrimaryRawExp a b)
          (addFiniteOppositeSignPrimaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hsecondaryNonfinite :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        FloatBits.finiteMagGE a b = true →
        (a.isNeg == b.isNeg) = false →
        addFiniteOppositeSignPrimaryBranch a b = false →
        addFiniteOppositeSignSecondaryDiffVal a b ≠ 0 →
        ¬((roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .normal ∨
          (roundAndPack (spec := spec) mode b.isNeg
            (addFiniteOppositeSignSecondaryRawExp a b)
            (addFiniteOppositeSignSecondaryRawSig a b)).value.classify = .subnormal) →
        (roundAndPack (spec := spec) mode b.isNeg
          (addFiniteOppositeSignSecondaryRawExp a b)
          (addFiniteOppositeSignSecondaryRawSig a b)).value.toReal =
          addSpec spec.toFormat mode a.toReal b.toReal)
    (hflags : AddSignFlagsToSpecOrderedGuarded spec mode) :
    AddBitEquiv spec mode ∧ AddBitFlagEquiv spec mode := by
  exact addBitEquivAndFlagEquiv_of_roundAndPackBranchObligationsGuarded_autoNonzero_andSignFlagObligations_noZeroAssumptions_bundle
    spec mode
    (addFiniteRoundAndPackBranchObligationsGuardedAutoNonzero_of_signOrderedGuarded_and_zeroBranches_and_nonfinite
      spec mode hsame hnonzero hzeroPrimary hzeroSecondary hsameNonfinite hprimaryNonfinite hsecondaryNonfinite)
    hflags

theorem mulBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      a.mul b mode = a.mulFinite b mode := by
  intro a b ha hb
  have hnone := mulSpecial_none_of_finite a b ha hb
  unfold FloatBits.mul
  rw [hnone]

theorem mulBitFlagEquivFinite (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      (a.mul b mode).flags = (a.mulFinite b mode).flags := by
  intro a b ha hb
  simpa using congrArg (fun r => r.flags) (mulBitEquiv spec mode a b ha hb)

/-- Finite/non-zero multiplication-kernel value obligation needed for `MulBitEquiv`. -/
def MulFiniteToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((a.mulFinite b mode).value.classify = .normal ∨
      (a.mulFinite b mode).value.classify = .subnormal ∨
      (a.mulFinite b mode).value.classify = .zero) →
    (a.mulFinite b mode).value.toReal = mulSpec spec.toFormat mode a.toReal b.toReal

/-- Finite/non-zero multiplication-kernel flag obligation needed for `MulBitFlagEquivFinite`. -/
def MulFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (a.mulFinite b mode).flags = mulFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Finite/non-zero multiplication-kernel exactness obligation on `toReal`. -/
def MulFiniteExact (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((a.mulFinite b mode).value.classify = .normal ∨
      (a.mulFinite b mode).value.classify = .subnormal ∨
      (a.mulFinite b mode).value.classify = .zero) →
    (a.mulFinite b mode).value.toReal = a.toReal * b.toReal

/-- Finite/non-zero multiplication representability obligation for exact products. -/
def MulFiniteRepresentable (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((a.mulFinite b mode).value.classify = .normal ∨
      (a.mulFinite b mode).value.classify = .subnormal ∨
      (a.mulFinite b mode).value.classify = .zero) →
    isRepresentable spec.toFormat (a.toReal * b.toReal)

/-- Finite/non-zero multiplication exactness plus flag obligations bundled together. -/
def MulFiniteExactAndFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  MulFiniteExact spec mode ∧ MulFiniteFlagsToSpec spec mode

theorem mulFiniteToSpec_of_exactAndRepresentable (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode)
    (hrepr : MulFiniteRepresentable spec mode) :
    MulFiniteToSpec spec mode := by
  intro a b ha hb hout
  calc
    (a.mulFinite b mode).value.toReal = a.toReal * b.toReal :=
      hexact a b ha hb hout
    _ = mulSpec spec.toFormat mode a.toReal b.toReal := by
      simpa using (mulSpec_repr_fixed spec.toFormat mode (hrepr a b ha hb hout)).symm

theorem mulFiniteToSpec_of_exact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode) :
    MulFiniteToSpec spec mode := by
  exact mulFiniteToSpec_of_exactAndRepresentable spec mode hexact
    (fun a b ha hb hout => by
      have hreprOut :
          isRepresentable spec.toFormat (a.mulFinite b mode).value.toReal :=
        toReal_isRepresentable_of_finiteOrZero (a.mulFinite b mode).value hout
      simpa [hexact a b ha hb hout] using hreprOut)

private def finiteSigNat {spec : BinarySpec} (f : FloatBits spec) : Nat :=
  (f.getExtendedSignificand).1.toNat

private def finiteExpNat {spec : BinarySpec} (f : FloatBits spec) : Nat :=
  (f.getExtendedSignificand).2

private def mulFiniteIsNeg {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  a.isNeg != b.isNeg

private def mulFiniteProd {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  finiteSigNat a * finiteSigNat b

private def mulFiniteRawExp {spec : BinarySpec} (a b : FloatBits spec) : Int :=
  (finiteExpNat a : Int) + (finiteExpNat b : Int) - (spec.bias : Int)

private def mulFiniteHighBranch {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  mulFiniteProd a b ≥ 2 ^ (2 * spec.sigWidth + 1)

private theorem mulFinite_eq_roundAndPack_by_branch {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode) :
    a.mulFinite b mode =
      if mulFiniteHighBranch a b then
        roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)
      else
        roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b) := by
  unfold FloatBits.mulFinite mulFiniteHighBranch mulFiniteProd mulFiniteRawExp mulFiniteIsNeg
  simp [finiteSigNat, finiteExpNat]

/-- High-branch value obligation for finite multiplication kernel. -/
def MulFiniteHighBranchToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    mulFiniteHighBranch a b = true →
    ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.toReal =
      mulSpec spec.toFormat mode a.toReal b.toReal

/-- Low-branch value obligation for finite multiplication kernel. -/
def MulFiniteLowBranchToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    mulFiniteHighBranch a b = false →
    ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.toReal =
      mulSpec spec.toFormat mode a.toReal b.toReal

/-- High-branch exactness obligation for finite multiplication kernels. -/
def MulFiniteHighBranchExact (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    mulFiniteHighBranch a b = true →
    ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.toReal =
      a.toReal * b.toReal

/-- Low-branch exactness obligation for finite multiplication kernels. -/
def MulFiniteLowBranchExact (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    mulFiniteHighBranch a b = false →
    ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.toReal =
      a.toReal * b.toReal

theorem mulFiniteExact_of_branchExact (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : MulFiniteHighBranchExact spec mode)
    (hlowExact : MulFiniteLowBranchExact spec mode) :
    MulFiniteExact spec mode := by
  intro a b ha hb hout
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  by_cases hhighb : mulFiniteHighBranch a b = true
  · have hout' :
      ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .zero) := by
      simpa [hbranch, hhighb] using hout
    have hcase := hhighExact a b ha hb hhighb hout'
    simpa [hbranch, hhighb] using hcase
  · have hlowb : mulFiniteHighBranch a b = false := by
      cases hbool : mulFiniteHighBranch a b <;> simp [hbool] at hhighb ⊢
    have hout' :
      ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .zero) := by
      simpa [hbranch, hlowb] using hout
    have hcase := hlowExact a b ha hb hlowb hout'
    simpa [hbranch, hlowb] using hcase

/-- High-branch flag obligation for finite multiplication kernel. -/
def MulFiniteHighBranchFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    mulFiniteHighBranch a b = true →
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).flags =
      mulFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Low-branch flag obligation for finite multiplication kernel. -/
def MulFiniteLowBranchFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    mulFiniteHighBranch a b = false →
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).flags =
      mulFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Bundled finite multiplication branch obligations (value + flags). -/
def MulFiniteBranchObligationsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  MulFiniteHighBranchToSpec spec mode ∧
    MulFiniteLowBranchToSpec spec mode ∧
    MulFiniteHighBranchFlagsToSpec spec mode ∧
    MulFiniteLowBranchFlagsToSpec spec mode

theorem mulFiniteToSpec_of_branchObligations (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : MulFiniteHighBranchToSpec spec mode)
    (hlow : MulFiniteLowBranchToSpec spec mode) :
    MulFiniteToSpec spec mode := by
  intro a b ha hb hout
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  by_cases hhighb : mulFiniteHighBranch a b = true
  · have hout' :
      ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.classify = .zero) := by
      simpa [hbranch, hhighb] using hout
    have hcase := hhigh a b ha hb hhighb hout'
    simpa [hbranch, hhighb] using hcase
  · have hlowb : mulFiniteHighBranch a b = false := by
      cases hbool : mulFiniteHighBranch a b <;> simp [hbool] at hhighb ⊢
    have hout' :
      ((roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).value.classify = .zero) := by
      simpa [hbranch, hlowb] using hout
    have hcase := hlow a b ha hb hlowb hout'
    simpa [hbranch, hlowb] using hcase

theorem mulFiniteToSpec_of_branches (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : MulFiniteHighBranchToSpec spec mode)
    (hlow : MulFiniteLowBranchToSpec spec mode) :
    MulFiniteToSpec spec mode := by
  exact mulFiniteToSpec_of_branchObligations spec mode hhigh hlow

private theorem mulSpec_of_exactFiniteResult {spec : BinarySpec} (mode : RoundingMode)
    (a b : FloatBits spec) (r : OpResult (FloatBits spec))
    (hout :
      r.value.classify = .normal ∨
      r.value.classify = .subnormal ∨
      r.value.classify = .zero)
    (hexact : r.value.toReal = a.toReal * b.toReal) :
    r.value.toReal = mulSpec spec.toFormat mode a.toReal b.toReal := by
  have hrepr :
      isRepresentable spec.toFormat r.value.toReal :=
    toReal_isRepresentable_of_finiteOrZero r.value hout
  have hreprExact : isRepresentable spec.toFormat (a.toReal * b.toReal) := by
    simpa [hexact] using hrepr
  calc
    r.value.toReal = a.toReal * b.toReal := hexact
    _ = mulSpec spec.toFormat mode a.toReal b.toReal := by
      simpa using (mulSpec_repr_fixed spec.toFormat mode hreprExact).symm

theorem mulFiniteToSpec_of_branchExact (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : MulFiniteHighBranchExact spec mode)
    (hlowExact : MulFiniteLowBranchExact spec mode) :
    MulFiniteToSpec spec mode := by
  refine mulFiniteToSpec_of_branchObligations spec mode ?_ ?_
  · intro a b ha hb hhighb hout
    have hexact :
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.toReal =
          a.toReal * b.toReal :=
      hhighExact a b ha hb hhighb hout
    exact mulSpec_of_exactFiniteResult mode a b
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
        (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2))
      hout hexact
  · intro a b ha hb hlowb hout
    have hexact :
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
          (mulFiniteRawExp a b) (mulFiniteProd a b)).value.toReal =
          a.toReal * b.toReal :=
      hlowExact a b ha hb hlowb hout
    exact mulSpec_of_exactFiniteResult mode a b
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
        (mulFiniteRawExp a b) (mulFiniteProd a b))
      hout hexact

theorem mulFiniteHighBranchExact_of_mulFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode) :
    MulFiniteHighBranchExact spec mode := by
  intro a b ha hb hhighb hout
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.mulFinite b mode).value.classify = .normal ∨
        (a.mulFinite b mode).value.classify = .subnormal ∨
        (a.mulFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hhighb] using hout
  have hcase := hexact a b ha hb hout'
  simpa [hbranch, hhighb] using hcase

theorem mulFiniteLowBranchExact_of_mulFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode) :
    MulFiniteLowBranchExact spec mode := by
  intro a b ha hb hlowb hout
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.mulFinite b mode).value.classify = .normal ∨
        (a.mulFinite b mode).value.classify = .subnormal ∨
        (a.mulFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hlowb] using hout
  have hcase := hexact a b ha hb hout'
  simpa [hbranch, hlowb] using hcase

theorem mulFiniteHighBranchToSpec_of_mulFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode) :
    MulFiniteHighBranchToSpec spec mode := by
  intro a b ha hb hhighb hout
  have hexact' :
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
        (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).value.toReal =
        a.toReal * b.toReal := by
    exact mulFiniteHighBranchExact_of_mulFiniteExact spec mode hexact a b ha hb hhighb hout
  exact mulSpec_of_exactFiniteResult mode a b
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
      (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2))
    hout hexact'

theorem mulFiniteLowBranchToSpec_of_mulFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode) :
    MulFiniteLowBranchToSpec spec mode := by
  intro a b ha hb hlowb hout
  have hexact' :
      (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
        (mulFiniteRawExp a b) (mulFiniteProd a b)).value.toReal =
        a.toReal * b.toReal := by
    exact mulFiniteLowBranchExact_of_mulFiniteExact spec mode hexact a b ha hb hlowb hout
  exact mulSpec_of_exactFiniteResult mode a b
    (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b)
      (mulFiniteRawExp a b) (mulFiniteProd a b))
    hout hexact'

theorem mulFiniteHighBranchToSpec_of_mulFiniteToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteToSpec spec mode) :
    MulFiniteHighBranchToSpec spec mode := by
  intro a b ha hb hhighb hout
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.mulFinite b mode).value.classify = .normal ∨
        (a.mulFinite b mode).value.classify = .subnormal ∨
        (a.mulFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hhighb] using hout
  have hcase := hfinite a b ha hb hout'
  simpa [hbranch, hhighb] using hcase

theorem mulFiniteLowBranchToSpec_of_mulFiniteToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteToSpec spec mode) :
    MulFiniteLowBranchToSpec spec mode := by
  intro a b ha hb hlowb hout
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.mulFinite b mode).value.classify = .normal ∨
        (a.mulFinite b mode).value.classify = .subnormal ∨
        (a.mulFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hlowb] using hout
  have hcase := hfinite a b ha hb hout'
  simpa [hbranch, hlowb] using hcase

theorem mulFiniteFlagsToSpec_of_branchObligations (spec : BinarySpec) (mode : RoundingMode)
    (hhigh :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        mulFiniteHighBranch a b = true →
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b + 1) (mulFiniteProd a b / 2)).flags =
          mulFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hlow :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        mulFiniteHighBranch a b = false →
        (roundAndPack (spec := spec) mode (mulFiniteIsNeg a b) (mulFiniteRawExp a b) (mulFiniteProd a b)).flags =
          mulFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    MulFiniteFlagsToSpec spec mode := by
  intro a b ha hb
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  by_cases hhighb : mulFiniteHighBranch a b = true
  · have hcase := hhigh a b ha hb hhighb
    simpa [hbranch, hhighb] using hcase
  · have hlowb : mulFiniteHighBranch a b = false := by
      cases hbool : mulFiniteHighBranch a b <;> simp [hbool] at hhighb ⊢
    have hcase := hlow a b ha hb hlowb
    simpa [hbranch, hlowb] using hcase

theorem mulFiniteFlagsToSpec_of_branches (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlow : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulFiniteFlagsToSpec spec mode := by
  exact mulFiniteFlagsToSpec_of_branchObligations spec mode hhigh hlow

theorem mulFiniteHighBranchFlagsToSpec_of_mulFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteFlagsToSpec spec mode) :
    MulFiniteHighBranchFlagsToSpec spec mode := by
  intro a b ha hb hhighb
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  have hcase := hfinite a b ha hb
  simpa [hbranch, hhighb] using hcase

theorem mulFiniteLowBranchFlagsToSpec_of_mulFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteFlagsToSpec spec mode) :
    MulFiniteLowBranchFlagsToSpec spec mode := by
  intro a b ha hb hlowb
  have hbranch := mulFinite_eq_roundAndPack_by_branch a b mode
  have hcase := hfinite a b ha hb
  simpa [hbranch, hlowb] using hcase

theorem mulFiniteBranchObligationsToSpec_of_mulFiniteExactAndFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode)
    (hflag : MulFiniteFlagsToSpec spec mode) :
    MulFiniteBranchObligationsToSpec spec mode := by
  exact ⟨
    mulFiniteHighBranchToSpec_of_mulFiniteExact spec mode hexact,
    mulFiniteLowBranchToSpec_of_mulFiniteExact spec mode hexact,
    mulFiniteHighBranchFlagsToSpec_of_mulFiniteFlagsToSpec spec mode hflag,
    mulFiniteLowBranchFlagsToSpec_of_mulFiniteFlagsToSpec spec mode hflag
  ⟩

theorem mulFiniteBranchObligationsToSpec_of_mulFiniteExactAndFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (h : MulFiniteExactAndFlagsToSpec spec mode) :
    MulFiniteBranchObligationsToSpec spec mode := by
  exact mulFiniteBranchObligationsToSpec_of_mulFiniteExactAndFlagsToSpec
    spec mode h.1 h.2

private theorem mulZeroResult_toReal (spec : BinarySpec) (a b : FloatBits spec) :
    (if mulZeroSign a b then FloatBits.negZero spec else FloatBits.posZero spec).toReal = 0 := by
  by_cases hsign : mulZeroSign a b = true
  · simp [hsign, FloatBits.negZero_toReal]
  · simp [hsign, FloatBits.posZero_toReal]

private theorem mulBitToSpec_zero_right (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero)
    (hb : b.classify = .zero) :
    (a.mul b mode).value.toReal = mulSpec spec.toFormat mode a.toReal b.toReal := by
  have hb0 : b.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hb]
  rcases ha with ha | ha | ha
  · unfold FloatBits.mul
    simp [FloatBits.mulSpecial, ha, hb, mulSpec, hb0, round_zero, mulZeroResult_toReal]
  · unfold FloatBits.mul
    simp [FloatBits.mulSpecial, ha, hb, mulSpec, hb0, round_zero, mulZeroResult_toReal]
  · unfold FloatBits.mul
    simp [FloatBits.mulSpecial, ha, hb, mulSpec, hb0, round_zero, mulZeroResult_toReal]

private theorem mulBitToSpec_zero_left (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .zero)
    (hb : b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) :
    (a.mul b mode).value.toReal = mulSpec spec.toFormat mode a.toReal b.toReal := by
  have ha0 : a.toReal = 0 := by
    unfold FloatBits.toReal
    rw [ha]
  rcases hb with hb | hb | hb
  · unfold FloatBits.mul
    simp [FloatBits.mulSpecial, ha, hb, mulSpec, ha0, round_zero, mulZeroResult_toReal]
  · unfold FloatBits.mul
    simp [FloatBits.mulSpecial, ha, hb, mulSpec, ha0, round_zero, mulZeroResult_toReal]
  · unfold FloatBits.mul
    simp [FloatBits.mulSpecial, ha, hb, mulSpec, ha0, round_zero, mulZeroResult_toReal]

theorem mulBitEquiv_of_mulFiniteToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteToSpec spec mode) :
    MulBitEquiv spec mode := by
  intro a b ha hb
  dsimp [MulBitEquiv]
  intro hout
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · have himpl := mulBitEquiv spec mode a b (Or.inl ha) (Or.inl hb)
      have hout' :
          ((a.mulFinite b mode).value.classify = .normal ∨
            (a.mulFinite b mode).value.classify = .subnormal ∨
            (a.mulFinite b mode).value.classify = .zero) := by
        simpa [himpl] using hout
      calc
        (a.mul b mode).value.toReal = (a.mulFinite b mode).value.toReal := by
          simp [himpl]
        _ = mulSpec spec.toFormat mode a.toReal b.toReal :=
          hfinite a b (Or.inl ha) (Or.inl hb) hout'
    · have himpl := mulBitEquiv spec mode a b (Or.inl ha) (Or.inr hb)
      have hout' :
          ((a.mulFinite b mode).value.classify = .normal ∨
            (a.mulFinite b mode).value.classify = .subnormal ∨
            (a.mulFinite b mode).value.classify = .zero) := by
        simpa [himpl] using hout
      calc
        (a.mul b mode).value.toReal = (a.mulFinite b mode).value.toReal := by
          simp [himpl]
        _ = mulSpec spec.toFormat mode a.toReal b.toReal :=
          hfinite a b (Or.inl ha) (Or.inr hb) hout'
    · exact mulBitToSpec_zero_right spec mode a b (Or.inl ha) hb
  · rcases hb with hb | hb | hb
    · have himpl := mulBitEquiv spec mode a b (Or.inr ha) (Or.inl hb)
      have hout' :
          ((a.mulFinite b mode).value.classify = .normal ∨
            (a.mulFinite b mode).value.classify = .subnormal ∨
            (a.mulFinite b mode).value.classify = .zero) := by
        simpa [himpl] using hout
      calc
        (a.mul b mode).value.toReal = (a.mulFinite b mode).value.toReal := by
          simp [himpl]
        _ = mulSpec spec.toFormat mode a.toReal b.toReal :=
          hfinite a b (Or.inr ha) (Or.inl hb) hout'
    · have himpl := mulBitEquiv spec mode a b (Or.inr ha) (Or.inr hb)
      have hout' :
          ((a.mulFinite b mode).value.classify = .normal ∨
            (a.mulFinite b mode).value.classify = .subnormal ∨
            (a.mulFinite b mode).value.classify = .zero) := by
        simpa [himpl] using hout
      calc
        (a.mul b mode).value.toReal = (a.mulFinite b mode).value.toReal := by
          simp [himpl]
        _ = mulSpec spec.toFormat mode a.toReal b.toReal :=
          hfinite a b (Or.inr ha) (Or.inr hb) hout'
    · exact mulBitToSpec_zero_right spec mode a b (Or.inr (Or.inl ha)) hb
  · exact mulBitToSpec_zero_left spec mode a b ha hb

theorem mulBitEquiv_of_mulFiniteBranches (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : MulFiniteHighBranchToSpec spec mode)
    (hlow : MulFiniteLowBranchToSpec spec mode) :
    MulBitEquiv spec mode := by
  exact mulBitEquiv_of_mulFiniteToSpec spec mode
    (mulFiniteToSpec_of_branches spec mode hhigh hlow)

theorem mulBitEquiv_of_mulFiniteBranchExact (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : MulFiniteHighBranchExact spec mode)
    (hlowExact : MulFiniteLowBranchExact spec mode) :
    MulBitEquiv spec mode := by
  exact mulBitEquiv_of_mulFiniteToSpec spec mode
    (mulFiniteToSpec_of_branchExact spec mode hhighExact hlowExact)

theorem mulBitEquiv_of_mulFiniteExactAndRepresentable (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode)
    (hrepr : MulFiniteRepresentable spec mode) :
    MulBitEquiv spec mode := by
  exact mulBitEquiv_of_mulFiniteToSpec spec mode
    (mulFiniteToSpec_of_exactAndRepresentable spec mode hexact hrepr)

theorem mulBitEquiv_of_mulFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode) :
    MulBitEquiv spec mode := by
  exact mulBitEquiv_of_mulFiniteToSpec spec mode
    (mulFiniteToSpec_of_exact spec mode hexact)

theorem mulBitFlagEquivFinite_of_mulFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteFlagsToSpec spec mode) :
    MulBitFlagEquivFinite spec mode := by
  intro a b ha hb
  calc
    (a.mul b mode).flags = (a.mulFinite b mode).flags := mulBitFlagEquivFinite spec mode a b ha hb
    _ = mulFlagsSpec spec.toFormat mode a.toReal b.toReal := hfinite a b ha hb

theorem mulBitFlagEquivFinite_of_mulFiniteBranchFlags (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlow : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitFlagEquivFinite spec mode := by
  exact mulBitFlagEquivFinite_of_mulFiniteFlagsToSpec spec mode
    (mulFiniteFlagsToSpec_of_branches spec mode hhigh hlow)

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hval : MulFiniteToSpec spec mode)
    (hflag : MulFiniteFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact ⟨
    mulBitEquiv_of_mulFiniteToSpec spec mode hval,
    mulBitFlagEquivFinite_of_mulFiniteFlagsToSpec spec mode hflag
  ⟩

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hhighVal : MulFiniteHighBranchToSpec spec mode)
    (hlowVal : MulFiniteLowBranchToSpec spec mode)
    (hhighFlag : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact ⟨
    mulBitEquiv_of_mulFiniteBranches spec mode hhighVal hlowVal,
    mulBitFlagEquivFinite_of_mulFiniteBranchFlags spec mode hhighFlag hlowFlag
  ⟩

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchObligationsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hbranch : MulFiniteBranchObligationsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchObligations
    spec mode hbranch.1 hbranch.2.1 hbranch.2.2.1 hbranch.2.2.2

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchExactAndFlagObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : MulFiniteHighBranchExact spec mode)
    (hlowExact : MulFiniteLowBranchExact spec mode)
    (hhighFlag : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact ⟨
    mulBitEquiv_of_mulFiniteBranchExact spec mode hhighExact hlowExact,
    mulBitFlagEquivFinite_of_mulFiniteBranchFlags spec mode hhighFlag hlowFlag
  ⟩

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteExactAndBranchFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode)
    (hhighFlag : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchExactAndFlagObligations
    spec mode
    (mulFiniteHighBranchExact_of_mulFiniteExact spec mode hexact)
    (mulFiniteLowBranchExact_of_mulFiniteExact spec mode hexact)
    hhighFlag hlowFlag

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteExactAndFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode)
    (hflag : MulFiniteFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact ⟨
    mulBitEquiv_of_mulFiniteExact spec mode hexact,
    mulBitFlagEquivFinite_of_mulFiniteFlagsToSpec spec mode hflag
  ⟩

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteExactAndFlags_viaBranchObligationsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (h : MulFiniteExactAndFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchObligationsToSpec spec mode
    (mulFiniteBranchObligationsToSpec_of_mulFiniteExactAndFlags spec mode h)

theorem mulBitEquivAndFlagEquivFinite_of_mulFiniteExactAndFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (h : MulFiniteExactAndFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquivFinite spec mode := by
  exact mulBitEquivAndFlagEquivFinite_of_mulFiniteExactAndFlagsToSpec
    spec mode h.1 h.2

theorem divBitEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      a.div b mode = a.divFinite b mode := by
  intro a b ha hb
  have hnone := divSpecial_none_of_finite a b ha hb
  unfold FloatBits.div
  rw [hnone]

theorem divBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal) →
      (b.classify = .normal ∨ b.classify = .subnormal) →
      (a.div b mode).flags = (a.divFinite b mode).flags := by
  intro a b ha hb
  simpa using congrArg (fun r => r.flags) (divBitEquiv spec mode a b ha hb)

/-- Finite division-kernel value obligation needed for `DivBitEquiv`. -/
def DivFiniteToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((a.divFinite b mode).value.classify = .normal ∨
      (a.divFinite b mode).value.classify = .subnormal ∨
      (a.divFinite b mode).value.classify = .zero) →
    (a.divFinite b mode).value.toReal = divSpec spec.toFormat mode a.toReal b.toReal

/-- Finite division-kernel flag obligation needed for `DivBitFlagEquiv`. -/
def DivFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (a.divFinite b mode).flags = divFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Finite division-kernel exactness obligation on `toReal`. -/
def DivFiniteExact (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((a.divFinite b mode).value.classify = .normal ∨
      (a.divFinite b mode).value.classify = .subnormal ∨
      (a.divFinite b mode).value.classify = .zero) →
    (a.divFinite b mode).value.toReal = a.toReal / b.toReal

/-- Finite division representability obligation for exact quotients. -/
def DivFiniteRepresentable (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    ((a.divFinite b mode).value.classify = .normal ∨
      (a.divFinite b mode).value.classify = .subnormal ∨
      (a.divFinite b mode).value.classify = .zero) →
    isRepresentable spec.toFormat (a.toReal / b.toReal)

/-- Finite division exactness plus flag obligations bundled together. -/
def DivFiniteExactAndFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  DivFiniteExact spec mode ∧ DivFiniteFlagsToSpec spec mode

theorem divFiniteToSpec_of_exactAndRepresentable (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode)
    (hrepr : DivFiniteRepresentable spec mode) :
    DivFiniteToSpec spec mode := by
  intro a b ha hb hout
  calc
    (a.divFinite b mode).value.toReal = a.toReal / b.toReal :=
      hexact a b ha hb hout
    _ = divSpec spec.toFormat mode a.toReal b.toReal := by
      simpa using (divSpec_repr_fixed spec.toFormat mode (hrepr a b ha hb hout)).symm

theorem divFiniteToSpec_of_exact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode) :
    DivFiniteToSpec spec mode := by
  exact divFiniteToSpec_of_exactAndRepresentable spec mode hexact
    (fun a b ha hb hout => by
      have hreprOut :
          isRepresentable spec.toFormat (a.divFinite b mode).value.toReal :=
        toReal_isRepresentable_of_finiteOrZero (a.divFinite b mode).value hout
      simpa [hexact a b ha hb hout] using hreprOut)

private def divFiniteIsNeg {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  a.isNeg != b.isNeg

private def divFiniteDividend {spec : BinarySpec} (a : FloatBits spec) : Nat :=
  finiteSigNat a <<< (spec.sigWidth + 2)

private def divFiniteQuot {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  divFiniteDividend a / finiteSigNat b

private def divFiniteRem {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  divFiniteDividend a % finiteSigNat b

private def divFiniteQuotWithSticky {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  if divFiniteRem a b != 0 then divFiniteQuot a b ||| 1 else divFiniteQuot a b

private def divFiniteRawExp {spec : BinarySpec} (a b : FloatBits spec) : Int :=
  (finiteExpNat a : Int) - (finiteExpNat b : Int) + (spec.bias : Int)

private def divFiniteHighBranch {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  divFiniteQuotWithSticky a b ≥ 2 ^ (2 * spec.sigWidth + 2)

private theorem divFinite_eq_roundAndPack_by_branch {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode) :
    a.divFinite b mode =
      if divFiniteHighBranch a b then
        roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)
      else
        roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2) := by
  unfold FloatBits.divFinite divFiniteHighBranch divFiniteQuotWithSticky divFiniteQuot divFiniteRem
    divFiniteDividend divFiniteRawExp divFiniteIsNeg
  simp [finiteSigNat, finiteExpNat]

/-- High-branch value obligation for finite division kernel. -/
def DivFiniteHighBranchToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    divFiniteHighBranch a b = true →
    ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.toReal =
      divSpec spec.toFormat mode a.toReal b.toReal

/-- Low-branch value obligation for finite division kernel. -/
def DivFiniteLowBranchToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    divFiniteHighBranch a b = false →
    ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.toReal =
      divSpec spec.toFormat mode a.toReal b.toReal

/-- High-branch exactness obligation for finite division kernels. -/
def DivFiniteHighBranchExact (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    divFiniteHighBranch a b = true →
    ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.toReal =
      a.toReal / b.toReal

/-- Low-branch exactness obligation for finite division kernels. -/
def DivFiniteLowBranchExact (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    divFiniteHighBranch a b = false →
    ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .normal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .subnormal ∨
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .zero) →
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.toReal =
      a.toReal / b.toReal

theorem divFiniteExact_of_branchExact (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : DivFiniteHighBranchExact spec mode)
    (hlowExact : DivFiniteLowBranchExact spec mode) :
    DivFiniteExact spec mode := by
  intro a b ha hb hout
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  by_cases hhighb : divFiniteHighBranch a b = true
  · have hout' :
      ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .zero) := by
      simpa [hbranch, hhighb] using hout
    have hcase := hhighExact a b ha hb hhighb hout'
    simpa [hbranch, hhighb] using hcase
  · have hlowb : divFiniteHighBranch a b = false := by
      cases hbool : divFiniteHighBranch a b <;> simp [hbool] at hhighb ⊢
    have hout' :
      ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .zero) := by
      simpa [hbranch, hlowb] using hout
    have hcase := hlowExact a b ha hb hlowb hout'
    simpa [hbranch, hlowb] using hcase

/-- High-branch flag obligation for finite division kernel. -/
def DivFiniteHighBranchFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    divFiniteHighBranch a b = true →
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).flags =
      divFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Low-branch flag obligation for finite division kernel. -/
def DivFiniteLowBranchFlagsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    divFiniteHighBranch a b = false →
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).flags =
      divFlagsSpec spec.toFormat mode a.toReal b.toReal

/-- Bundled finite division branch obligations (value + flags). -/
def DivFiniteBranchObligationsToSpec (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  DivFiniteHighBranchToSpec spec mode ∧
    DivFiniteLowBranchToSpec spec mode ∧
    DivFiniteHighBranchFlagsToSpec spec mode ∧
    DivFiniteLowBranchFlagsToSpec spec mode

theorem divFiniteToSpec_of_branchObligations (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : DivFiniteHighBranchToSpec spec mode)
    (hlow : DivFiniteLowBranchToSpec spec mode) :
    DivFiniteToSpec spec mode := by
  intro a b ha hb hout
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  by_cases hhighb : divFiniteHighBranch a b = true
  · have hout' :
      ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.classify = .zero) := by
      simpa [hbranch, hhighb] using hout
    have hcase := hhigh a b ha hb hhighb hout'
    simpa [hbranch, hhighb] using hcase
  · have hlowb : divFiniteHighBranch a b = false := by
      cases hbool : divFiniteHighBranch a b <;> simp [hbool] at hhighb ⊢
    have hout' :
      ((roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .normal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .subnormal ∨
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.classify = .zero) := by
      simpa [hbranch, hlowb] using hout
    have hcase := hlow a b ha hb hlowb hout'
    simpa [hbranch, hlowb] using hcase

theorem divFiniteToSpec_of_branches (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : DivFiniteHighBranchToSpec spec mode)
    (hlow : DivFiniteLowBranchToSpec spec mode) :
    DivFiniteToSpec spec mode := by
  exact divFiniteToSpec_of_branchObligations spec mode hhigh hlow

private theorem divSpec_of_exactFiniteResult {spec : BinarySpec} (mode : RoundingMode)
    (a b : FloatBits spec) (r : OpResult (FloatBits spec))
    (hout :
      r.value.classify = .normal ∨
      r.value.classify = .subnormal ∨
      r.value.classify = .zero)
    (hexact : r.value.toReal = a.toReal / b.toReal) :
    r.value.toReal = divSpec spec.toFormat mode a.toReal b.toReal := by
  have hrepr :
      isRepresentable spec.toFormat r.value.toReal :=
    toReal_isRepresentable_of_finiteOrZero r.value hout
  have hreprExact : isRepresentable spec.toFormat (a.toReal / b.toReal) := by
    simpa [hexact] using hrepr
  calc
    r.value.toReal = a.toReal / b.toReal := hexact
    _ = divSpec spec.toFormat mode a.toReal b.toReal := by
      simpa using (divSpec_repr_fixed spec.toFormat mode hreprExact).symm

theorem divFiniteToSpec_of_branchExact (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : DivFiniteHighBranchExact spec mode)
    (hlowExact : DivFiniteLowBranchExact spec mode) :
    DivFiniteToSpec spec mode := by
  refine divFiniteToSpec_of_branchObligations spec mode ?_ ?_
  · intro a b ha hb hhighb hout
    have hexact :
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.toReal =
          a.toReal / b.toReal :=
      hhighExact a b ha hb hhighb hout
    exact divSpec_of_exactFiniteResult mode a b
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
        (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4))
      hout hexact
  · intro a b ha hb hlowb hout
    have hexact :
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
          (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.toReal =
          a.toReal / b.toReal :=
      hlowExact a b ha hb hlowb hout
    exact divSpec_of_exactFiniteResult mode a b
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
        (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2))
      hout hexact

theorem divFiniteHighBranchExact_of_divFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode) :
    DivFiniteHighBranchExact spec mode := by
  intro a b ha hb hhighb hout
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.divFinite b mode).value.classify = .normal ∨
        (a.divFinite b mode).value.classify = .subnormal ∨
        (a.divFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hhighb] using hout
  have hcase := hexact a b ha hb hout'
  simpa [hbranch, hhighb] using hcase

theorem divFiniteLowBranchExact_of_divFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode) :
    DivFiniteLowBranchExact spec mode := by
  intro a b ha hb hlowb hout
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.divFinite b mode).value.classify = .normal ∨
        (a.divFinite b mode).value.classify = .subnormal ∨
        (a.divFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hlowb] using hout
  have hcase := hexact a b ha hb hout'
  simpa [hbranch, hlowb] using hcase

theorem divFiniteHighBranchToSpec_of_divFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode) :
    DivFiniteHighBranchToSpec spec mode := by
  intro a b ha hb hhighb hout
  have hexact' :
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
        (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).value.toReal =
        a.toReal / b.toReal := by
    exact divFiniteHighBranchExact_of_divFiniteExact spec mode hexact a b ha hb hhighb hout
  exact divSpec_of_exactFiniteResult mode a b
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
      (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4))
    hout hexact'

theorem divFiniteLowBranchToSpec_of_divFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode) :
    DivFiniteLowBranchToSpec spec mode := by
  intro a b ha hb hlowb hout
  have hexact' :
      (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
        (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).value.toReal =
        a.toReal / b.toReal := by
    exact divFiniteLowBranchExact_of_divFiniteExact spec mode hexact a b ha hb hlowb hout
  exact divSpec_of_exactFiniteResult mode a b
    (roundAndPack (spec := spec) mode (divFiniteIsNeg a b)
      (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2))
    hout hexact'

theorem divFiniteHighBranchToSpec_of_divFiniteToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : DivFiniteToSpec spec mode) :
    DivFiniteHighBranchToSpec spec mode := by
  intro a b ha hb hhighb hout
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.divFinite b mode).value.classify = .normal ∨
        (a.divFinite b mode).value.classify = .subnormal ∨
        (a.divFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hhighb] using hout
  have hcase := hfinite a b ha hb hout'
  simpa [hbranch, hhighb] using hcase

theorem divFiniteLowBranchToSpec_of_divFiniteToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : DivFiniteToSpec spec mode) :
    DivFiniteLowBranchToSpec spec mode := by
  intro a b ha hb hlowb hout
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  have hout' :
      ((a.divFinite b mode).value.classify = .normal ∨
        (a.divFinite b mode).value.classify = .subnormal ∨
        (a.divFinite b mode).value.classify = .zero) := by
    simpa [hbranch, hlowb] using hout
  have hcase := hfinite a b ha hb hout'
  simpa [hbranch, hlowb] using hcase

theorem divFiniteFlagsToSpec_of_branchObligations (spec : BinarySpec) (mode : RoundingMode)
    (hhigh :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        divFiniteHighBranch a b = true →
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b + 1) (divFiniteQuotWithSticky a b / 4)).flags =
          divFlagsSpec spec.toFormat mode a.toReal b.toReal)
    (hlow :
      ∀ (a b : FloatBits spec),
        (a.classify = .normal ∨ a.classify = .subnormal) →
        (b.classify = .normal ∨ b.classify = .subnormal) →
        divFiniteHighBranch a b = false →
        (roundAndPack (spec := spec) mode (divFiniteIsNeg a b) (divFiniteRawExp a b) (divFiniteQuotWithSticky a b / 2)).flags =
          divFlagsSpec spec.toFormat mode a.toReal b.toReal) :
    DivFiniteFlagsToSpec spec mode := by
  intro a b ha hb
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  by_cases hhighb : divFiniteHighBranch a b = true
  · have hcase := hhigh a b ha hb hhighb
    simpa [hbranch, hhighb] using hcase
  · have hlowb : divFiniteHighBranch a b = false := by
      cases hbool : divFiniteHighBranch a b <;> simp [hbool] at hhighb ⊢
    have hcase := hlow a b ha hb hlowb
    simpa [hbranch, hlowb] using hcase

theorem divFiniteFlagsToSpec_of_branches (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : DivFiniteHighBranchFlagsToSpec spec mode)
    (hlow : DivFiniteLowBranchFlagsToSpec spec mode) :
    DivFiniteFlagsToSpec spec mode := by
  exact divFiniteFlagsToSpec_of_branchObligations spec mode hhigh hlow

theorem divFiniteHighBranchFlagsToSpec_of_divFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : DivFiniteFlagsToSpec spec mode) :
    DivFiniteHighBranchFlagsToSpec spec mode := by
  intro a b ha hb hhighb
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  have hcase := hfinite a b ha hb
  simpa [hbranch, hhighb] using hcase

theorem divFiniteLowBranchFlagsToSpec_of_divFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : DivFiniteFlagsToSpec spec mode) :
    DivFiniteLowBranchFlagsToSpec spec mode := by
  intro a b ha hb hlowb
  have hbranch := divFinite_eq_roundAndPack_by_branch a b mode
  have hcase := hfinite a b ha hb
  simpa [hbranch, hlowb] using hcase

theorem divFiniteBranchObligationsToSpec_of_divFiniteExactAndFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode)
    (hflag : DivFiniteFlagsToSpec spec mode) :
    DivFiniteBranchObligationsToSpec spec mode := by
  exact ⟨
    divFiniteHighBranchToSpec_of_divFiniteExact spec mode hexact,
    divFiniteLowBranchToSpec_of_divFiniteExact spec mode hexact,
    divFiniteHighBranchFlagsToSpec_of_divFiniteFlagsToSpec spec mode hflag,
    divFiniteLowBranchFlagsToSpec_of_divFiniteFlagsToSpec spec mode hflag
  ⟩

theorem divFiniteBranchObligationsToSpec_of_divFiniteExactAndFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (h : DivFiniteExactAndFlagsToSpec spec mode) :
    DivFiniteBranchObligationsToSpec spec mode := by
  exact divFiniteBranchObligationsToSpec_of_divFiniteExactAndFlagsToSpec
    spec mode h.1 h.2

theorem divBitEquiv_of_divFiniteToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : DivFiniteToSpec spec mode) :
    DivBitEquiv spec mode := by
  intro a b ha hb
  dsimp [DivBitEquiv]
  intro hout
  have himpl := divBitEquiv spec mode a b ha hb
  have hout' :
      ((a.divFinite b mode).value.classify = .normal ∨
        (a.divFinite b mode).value.classify = .subnormal ∨
        (a.divFinite b mode).value.classify = .zero) := by
    simpa [himpl] using hout
  calc
    (a.div b mode).value.toReal = (a.divFinite b mode).value.toReal := by
      simp [himpl]
    _ = divSpec spec.toFormat mode a.toReal b.toReal := hfinite a b ha hb hout'

theorem divBitEquiv_of_divFiniteBranches (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : DivFiniteHighBranchToSpec spec mode)
    (hlow : DivFiniteLowBranchToSpec spec mode) :
    DivBitEquiv spec mode := by
  exact divBitEquiv_of_divFiniteToSpec spec mode
    (divFiniteToSpec_of_branches spec mode hhigh hlow)

theorem divBitEquiv_of_divFiniteBranchExact (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : DivFiniteHighBranchExact spec mode)
    (hlowExact : DivFiniteLowBranchExact spec mode) :
    DivBitEquiv spec mode := by
  exact divBitEquiv_of_divFiniteToSpec spec mode
    (divFiniteToSpec_of_branchExact spec mode hhighExact hlowExact)

theorem divBitEquiv_of_divFiniteExactAndRepresentable (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode)
    (hrepr : DivFiniteRepresentable spec mode) :
    DivBitEquiv spec mode := by
  exact divBitEquiv_of_divFiniteToSpec spec mode
    (divFiniteToSpec_of_exactAndRepresentable spec mode hexact hrepr)

theorem divBitEquiv_of_divFiniteExact (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode) :
    DivBitEquiv spec mode := by
  exact divBitEquiv_of_divFiniteToSpec spec mode
    (divFiniteToSpec_of_exact spec mode hexact)

theorem divBitFlagEquiv_of_divFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : DivFiniteFlagsToSpec spec mode) :
    DivBitFlagEquiv spec mode := by
  intro a b ha hb
  calc
    (a.div b mode).flags = (a.divFinite b mode).flags := divBitFlagEquiv spec mode a b ha hb
    _ = divFlagsSpec spec.toFormat mode a.toReal b.toReal := hfinite a b ha hb

theorem divBitFlagEquiv_of_divFiniteBranchFlags (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : DivFiniteHighBranchFlagsToSpec spec mode)
    (hlow : DivFiniteLowBranchFlagsToSpec spec mode) :
    DivBitFlagEquiv spec mode := by
  exact divBitFlagEquiv_of_divFiniteFlagsToSpec spec mode
    (divFiniteFlagsToSpec_of_branches spec mode hhigh hlow)

theorem divBitEquivAndFlagEquiv_of_divFiniteObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hval : DivFiniteToSpec spec mode)
    (hflag : DivFiniteFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact ⟨
    divBitEquiv_of_divFiniteToSpec spec mode hval,
    divBitFlagEquiv_of_divFiniteFlagsToSpec spec mode hflag
  ⟩

theorem divBitEquivAndFlagEquiv_of_divFiniteBranchObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hhighVal : DivFiniteHighBranchToSpec spec mode)
    (hlowVal : DivFiniteLowBranchToSpec spec mode)
    (hhighFlag : DivFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : DivFiniteLowBranchFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact ⟨
    divBitEquiv_of_divFiniteBranches spec mode hhighVal hlowVal,
    divBitFlagEquiv_of_divFiniteBranchFlags spec mode hhighFlag hlowFlag
  ⟩

theorem divBitEquivAndFlagEquiv_of_divFiniteBranchObligationsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hbranch : DivFiniteBranchObligationsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact divBitEquivAndFlagEquiv_of_divFiniteBranchObligations
    spec mode hbranch.1 hbranch.2.1 hbranch.2.2.1 hbranch.2.2.2

theorem divBitEquivAndFlagEquiv_of_divFiniteBranchExactAndFlagObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : DivFiniteHighBranchExact spec mode)
    (hlowExact : DivFiniteLowBranchExact spec mode)
    (hhighFlag : DivFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : DivFiniteLowBranchFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact ⟨
    divBitEquiv_of_divFiniteBranchExact spec mode hhighExact hlowExact,
    divBitFlagEquiv_of_divFiniteBranchFlags spec mode hhighFlag hlowFlag
  ⟩

theorem divBitEquivAndFlagEquiv_of_divFiniteExactAndBranchFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode)
    (hhighFlag : DivFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : DivFiniteLowBranchFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact divBitEquivAndFlagEquiv_of_divFiniteBranchExactAndFlagObligations
    spec mode
    (divFiniteHighBranchExact_of_divFiniteExact spec mode hexact)
    (divFiniteLowBranchExact_of_divFiniteExact spec mode hexact)
    hhighFlag hlowFlag

theorem divBitEquivAndFlagEquiv_of_divFiniteExactAndFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : DivFiniteExact spec mode)
    (hflag : DivFiniteFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact ⟨
    divBitEquiv_of_divFiniteExact spec mode hexact,
    divBitFlagEquiv_of_divFiniteFlagsToSpec spec mode hflag
  ⟩

theorem divBitEquivAndFlagEquiv_of_divFiniteExactAndFlags_viaBranchObligationsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (h : DivFiniteExactAndFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact divBitEquivAndFlagEquiv_of_divFiniteBranchObligationsToSpec spec mode
    (divFiniteBranchObligationsToSpec_of_divFiniteExactAndFlags spec mode h)

theorem divBitEquivAndFlagEquiv_of_divFiniteExactAndFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (h : DivFiniteExactAndFlagsToSpec spec mode) :
    DivBitEquiv spec mode ∧ DivBitFlagEquiv spec mode := by
  exact divBitEquivAndFlagEquiv_of_divFiniteExactAndFlagsToSpec
    spec mode h.1 h.2

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
