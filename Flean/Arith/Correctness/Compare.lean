import Flean.Arith.Correctness.Core

namespace Flean

/-! ## Comparison correctness and flags -/

theorem eqResultSpec_correct {spec : BinarySpec} (a b : FloatBits spec) :
    a.eqResult b = eqResultSpec a b := rfl

theorem ltResultSpec_correct {spec : BinarySpec} (a b : FloatBits spec) :
    a.ltResult b = ltResultSpec a b := rfl

theorem leResultSpec_correct {spec : BinarySpec} (a b : FloatBits spec) :
    a.leResult b = leResultSpec a b := rfl

theorem minNumResultSpec_correct {spec : BinarySpec} (a b : FloatBits spec) :
    a.minNumResult b = minNumResultSpec a b := rfl

theorem maxNumResultSpec_correct {spec : BinarySpec} (a b : FloatBits spec) :
    a.maxNumResult b = maxNumResultSpec a b := rfl

theorem eqResult_nan_value_false {spec : BinarySpec} (a b : FloatBits spec)
    (h : a.classify = .nan ∨ b.classify = .nan) :
    (a.eqResult b).value = false := by
  rcases h with ha | hb
  · simp [FloatBits.eqResult, ha]
  · simp [FloatBits.eqResult, hb]

theorem eqResult_nan_invalid_flag {spec : BinarySpec} (a b : FloatBits spec)
    (h : a.classify = .nan ∨ b.classify = .nan) :
    (a.eqResult b).flags.invalidOperation = (a.isSignalingNaN || b.isSignalingNaN) := by
  rcases h with ha | hb
  · simp [FloatBits.eqResult, ha]
  · simp [FloatBits.eqResult, hb]

theorem ltResult_nan_value_false {spec : BinarySpec} (a b : FloatBits spec)
    (h : a.classify = .nan ∨ b.classify = .nan) :
    (a.ltResult b).value = false := by
  rcases h with ha | hb
  · simp [FloatBits.ltResult, ha]
  · simp [FloatBits.ltResult, hb]

theorem ltResult_nan_invalid_true {spec : BinarySpec} (a b : FloatBits spec)
    (h : a.classify = .nan ∨ b.classify = .nan) :
    (a.ltResult b).flags.invalidOperation = true := by
  rcases h with ha | hb
  · simp [FloatBits.ltResult, ha]
  · simp [FloatBits.ltResult, hb]

theorem leResult_value_def {spec : BinarySpec} (a b : FloatBits spec) :
    (a.leResult b).value = ((a.ltResult b).value || (a.eqResult b).value) := rfl

theorem leResult_flags_def {spec : BinarySpec} (a b : FloatBits spec) :
    (a.leResult b).flags = ((a.ltResult b).flags ++ (a.eqResult b).flags) := rfl

theorem minNumResult_nan_left {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify = .nan) :
    (a.minNumResult b).value = b ∧
    (a.minNumResult b).flags.invalidOperation = a.isSignalingNaN := by
  simp [FloatBits.minNumResult, ha]

theorem minNumResult_nan_right {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify ≠ .nan) (hb : b.classify = .nan) :
    (a.minNumResult b).value = a ∧
    (a.minNumResult b).flags.invalidOperation = b.isSignalingNaN := by
  simp [FloatBits.minNumResult, ha, hb]

theorem maxNumResult_nan_left {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify = .nan) :
    (a.maxNumResult b).value = b ∧
    (a.maxNumResult b).flags.invalidOperation = a.isSignalingNaN := by
  simp [FloatBits.maxNumResult, ha]

theorem maxNumResult_nan_right {spec : BinarySpec} (a b : FloatBits spec)
    (ha : a.classify ≠ .nan) (hb : b.classify = .nan) :
    (a.maxNumResult b).value = a ∧
    (a.maxNumResult b).flags.invalidOperation = b.isSignalingNaN := by
  simp [FloatBits.maxNumResult, ha, hb]

end Flean
