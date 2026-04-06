import Flean.Arith.Correctness.Core

namespace Flean

/-! ## Special value correctness (unconditional) -/

/-- Multiplication: NaN propagation is correct. -/
theorem mul_nan_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.mul b mode).value = a.quietedNaN := by
  simp [FloatBits.mul, FloatBits.mulSpecial, binaryNaNResult, ha]

theorem mul_nan_right {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify ≠ .nan) (hb : b.classify = .nan) :
    (a.mul b mode).value = b.quietedNaN := by
  simp only [FloatBits.mul, FloatBits.mulSpecial, binaryNaNResult]
  cases hac : a.classify <;> simp_all

/-- Addition: NaN propagation. -/
theorem add_nan_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.add b mode).value = a.quietedNaN := by
  simp [FloatBits.add, FloatBits.addSpecial, binaryNaNResult, ha]

theorem add_nan_right {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify ≠ .nan) (hb : b.classify = .nan) :
    (a.add b mode).value = b.quietedNaN := by
  simp only [FloatBits.add, FloatBits.addSpecial, binaryNaNResult]
  cases hac : a.classify <;> simp_all

/-- Division: NaN propagation. -/
theorem div_nan_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.div b mode).value = a.quietedNaN := by
  simp [FloatBits.div, FloatBits.divSpecial, binaryNaNResult, ha]

theorem add_nan_invalid_flag {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.add b mode).flags.invalidOperation = (a.isSignalingNaN || b.isSignalingNaN) := by
  simp [FloatBits.add, FloatBits.addSpecial, binaryNaNResult, ha]

theorem mul_nan_invalid_flag {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.mul b mode).flags.invalidOperation = (a.isSignalingNaN || b.isSignalingNaN) := by
  simp [FloatBits.mul, FloatBits.mulSpecial, binaryNaNResult, ha]

theorem div_nan_invalid_flag {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.div b mode).flags.invalidOperation = (a.isSignalingNaN || b.isSignalingNaN) := by
  simp [FloatBits.div, FloatBits.divSpecial, binaryNaNResult, ha]

theorem sqrt_nan_invalid_flag {spec : BinarySpec} (a : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .nan) :
    (a.sqrt mode).flags.invalidOperation = a.isSignalingNaN := by
  simp [FloatBits.sqrt, unaryNaNResult, ha]

theorem cast_nan_invalid_flag {srcSpec dstSpec : BinarySpec}
    (a : FloatBits srcSpec) (mode : RoundingMode) (ha : a.classify = .nan) :
    (a.cast (dstSpec := dstSpec) mode).flags.invalidOperation = a.isSignalingNaN := by
  simp [FloatBits.cast, ha]

theorem fma_nan_invalid_flag_left {spec : BinarySpec}
    (a b c : FloatBits spec) (mode : RoundingMode) (ha : a.classify = .nan) :
    (a.fma b c mode).flags.invalidOperation = (a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN) := by
  simp [FloatBits.fma, ha]

theorem add_inf_opposite_invalid {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .infinite) (hb : b.classify = .infinite) (hs : a.isNeg ≠ b.isNeg) :
    (a.add b mode).flags.invalidOperation = true ∧
    (a.add b mode).value = FloatBits.quietNaN spec := by
  unfold FloatBits.add
  simp [FloatBits.addSpecial, ha, hb, hs]

theorem mul_inf_zero_invalid_left {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .infinite) (hb : b.classify = .zero) :
    (a.mul b mode).flags.invalidOperation = true ∧
    (a.mul b mode).value = FloatBits.quietNaN spec := by
  unfold FloatBits.mul
  simp [FloatBits.mulSpecial, ha, hb]

theorem mul_inf_zero_invalid_right {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .zero) (hb : b.classify = .infinite) :
    (a.mul b mode).flags.invalidOperation = true ∧
    (a.mul b mode).value = FloatBits.quietNaN spec := by
  unfold FloatBits.mul
  simp [FloatBits.mulSpecial, ha, hb]

theorem div_zero_zero_invalid {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .zero) (hb : b.classify = .zero) :
    (a.div b mode).flags.invalidOperation = true ∧
    (a.div b mode).value = FloatBits.quietNaN spec := by
  unfold FloatBits.div
  simp [FloatBits.divSpecial, ha, hb]

theorem div_inf_inf_invalid {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .infinite) (hb : b.classify = .infinite) :
    (a.div b mode).flags.invalidOperation = true ∧
    (a.div b mode).value = FloatBits.quietNaN spec := by
  unfold FloatBits.div
  simp [FloatBits.divSpecial, ha, hb]

theorem div_by_zero_flag {spec : BinarySpec} (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .infinite)
    (hb : b.classify = .zero) :
    (a.div b mode).flags.divisionByZero = true := by
  rcases ha with ha | ha | ha <;> unfold FloatBits.div <;> simp [FloatBits.divSpecial, ha, hb]

theorem sqrt_negative_invalid {spec : BinarySpec} (a : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .infinite)
    (hneg : a.isNeg = true) :
    (a.sqrt mode).flags.invalidOperation = true := by
  rcases ha with ha | ha | ha <;> unfold FloatBits.sqrt <;> simp [ha, hneg]

theorem fma_inf_zero_invalid_left {spec : BinarySpec}
    (a b c : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .infinite) (hb : b.classify = .zero) :
    (a.fma b c mode).flags.invalidOperation =
      (if c.classify = .nan then (a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN) else true) ∧
    (if c.classify = .nan then (a.fma b c mode).value = c.quietedNaN
     else (a.fma b c mode).value = FloatBits.quietNaN spec) := by
  unfold FloatBits.fma
  cases c.classify with
  | nan =>
      simp [ha, hb]
  | infinite =>
      simp [ha, hb]
  | zero =>
      simp [ha, hb]
  | normal =>
      simp [ha, hb]
  | subnormal =>
      simp [ha, hb]

end Flean
