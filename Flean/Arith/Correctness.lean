import Flean.Bridge
import Flean.Core.ULP
import Flean.Arith.Operations
import Flean.Arith.Sqrt
import Flean.Arith.FMA
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Flean.Arith.Correctness

IEEE 754 arithmetic correctness: specification-level and bit-level.

## Architecture

Following Flocq's approach, we separate two concerns:

1. **Specification-level correctness** (this file, fully proved):
   Each operation is `round(exact_result)`. This is trivially correct
   by construction and gives us error bounds, monotonicity, etc. for free.

2. **Bit-level equivalence** (stated, not yet proved):
   The `FloatBits` implementations (`mul`, `add`, etc.) compute the same
   result as the spec-level operations. This requires verifying `roundAndPack`.

All theorems in Section 1 are sorry-free.
-/

namespace Flean

/-! ## Section 1: Specification-level operations (sorry-free)

These define the IEEE 754 semantics as `round(exact_result)` on ℝ.
Correctness is immediate. Error bounds follow from rounding properties. -/

/-- Spec-level multiplication: round the exact product. -/
noncomputable def mulSpec (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) : ℝ :=
  round fmt mode (a * b)

/-- Spec-level addition: round the exact sum. -/
noncomputable def addSpec (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) : ℝ :=
  round fmt mode (a + b)

/-- Spec-level division: round the exact quotient. -/
noncomputable def divSpec (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) : ℝ :=
  round fmt mode (a / b)

/-- Spec-level square root: round the exact root. -/
noncomputable def sqrtSpec (fmt : FloatFormat) (mode : RoundingMode) (a : ℝ) : ℝ :=
  round fmt mode (Real.sqrt a)

/-- Spec-level FMA: round the exact fused result (no intermediate rounding). -/
noncomputable def fmaSpec (fmt : FloatFormat) (mode : RoundingMode) (a b c : ℝ) : ℝ :=
  round fmt mode (a * b + c)

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

/-- Multiplication: NaN propagation is correct. -/
theorem mul_nan_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.mul b mode).value = a := by
  simp [FloatBits.mul, FloatBits.mulSpecial, ha]

theorem mul_nan_right {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify ≠ .nan) (hb : b.classify = .nan) :
    (a.mul b mode).value = b := by
  simp only [FloatBits.mul, FloatBits.mulSpecial]
  cases hac : a.classify <;> simp_all

/-- Addition: NaN propagation. -/
theorem add_nan_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.add b mode).value = a := by
  simp [FloatBits.add, FloatBits.addSpecial, ha]

theorem add_nan_right {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify ≠ .nan) (hb : b.classify = .nan) :
    (a.add b mode).value = b := by
  simp only [FloatBits.add, FloatBits.addSpecial]
  cases hac : a.classify <;> simp_all

/-- Division: NaN propagation. -/
theorem div_nan_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.div b mode).value = a := by
  simp [FloatBits.div, FloatBits.divSpecial, ha]

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
operations. Proving these requires verifying `roundAndPack`, which is
the main remaining verification task. -/

/-- Bit-level multiplication matches spec-level multiplication. -/
def MulBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    let r := a.mul b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = mulSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level addition matches spec-level addition. -/
def AddBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
    (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
    let r := a.add b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = addSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level division matches spec-level division. -/
def DivBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    b.toReal ≠ 0 →
    let r := a.div b mode
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = divSpec spec.toFormat mode a.toReal b.toReal

/-- Bit-level square root matches spec-level square root. -/
def SqrtBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    ¬a.isNeg →
    let r := a.sqrt
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = sqrtSpec spec.toFormat mode a.toReal

/-- Bit-level FMA matches spec-level FMA. -/
def FmaBitEquiv (spec : BinarySpec) (mode : RoundingMode) : Prop :=
  ∀ (a b c : FloatBits spec),
    (a.classify = .normal ∨ a.classify = .subnormal) →
    (b.classify = .normal ∨ b.classify = .subnormal) →
    (c.classify = .normal ∨ c.classify = .subnormal ∨ c.classify = .zero) →
    let r := a.fma b c
    (r.value.classify = .normal ∨ r.value.classify = .subnormal) →
    r.value.toReal = fmaSpec spec.toFormat mode a.toReal b.toReal c.toReal

end Flean
