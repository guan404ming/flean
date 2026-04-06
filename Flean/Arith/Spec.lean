import Flean.Core.RoundProps
import Flean.Arith.Exceptions
import Flean.Arith.Compare

namespace Flean

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

/-- Spec-level cast: rounding a real value into the destination format. -/
noncomputable def castSpec (srcFmt dstFmt : FloatFormat) (mode : RoundingMode) (x : ℝ) : ℝ :=
  let _ := srcFmt
  round dstFmt mode x

/-- Spec-level exception flags for a rounded finite result. -/
noncomputable def roundedFlagsSpec (fmt : FloatFormat) (exact rounded : ℝ) : ExceptionFlags :=
  { inexact := by
      classical
      exact decide (exact ≠ rounded)
    overflow := by
      classical
      exact decide (maxFinite fmt < |exact|)
    underflow := by
      classical
      exact decide (rounded ≠ exact ∧ exact ≠ 0 ∧ |exact| < minNormal fmt) }

/-- Spec-level flags for addition. -/
noncomputable def addFlagsSpec (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) : ExceptionFlags :=
  let exact := a + b
  let rounded := addSpec fmt mode a b
  roundedFlagsSpec fmt exact rounded

/-- Spec-level flags for multiplication. -/
noncomputable def mulFlagsSpec (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) : ExceptionFlags :=
  let exact := a * b
  let rounded := mulSpec fmt mode a b
  roundedFlagsSpec fmt exact rounded

/-- Spec-level flags for division. -/
noncomputable def divFlagsSpec (fmt : FloatFormat) (mode : RoundingMode) (a b : ℝ) : ExceptionFlags :=
  let exact := a / b
  let rounded := divSpec fmt mode a b
  roundedFlagsSpec fmt exact rounded

/-- Spec-level flags for square root. -/
noncomputable def sqrtFlagsSpec (fmt : FloatFormat) (mode : RoundingMode) (a : ℝ) : ExceptionFlags :=
  let exact := Real.sqrt a
  let rounded := sqrtSpec fmt mode a
  roundedFlagsSpec fmt exact rounded

/-- Spec-level flags for fused multiply-add. -/
noncomputable def fmaFlagsSpec (fmt : FloatFormat) (mode : RoundingMode) (a b c : ℝ) : ExceptionFlags :=
  let exact := a * b + c
  let rounded := fmaSpec fmt mode a b c
  roundedFlagsSpec fmt exact rounded

/-- Spec-level flags for casts. -/
noncomputable def castFlagsSpec (srcFmt dstFmt : FloatFormat) (mode : RoundingMode) (x : ℝ) : ExceptionFlags :=
  let _ := srcFmt
  let rounded := castSpec srcFmt dstFmt mode x
  roundedFlagsSpec dstFmt x rounded

/-- Spec-level IEEE equality result (boolean + flags). -/
def eqResultSpec {spec : BinarySpec} (a b : FloatBits spec) : OpResult Bool :=
  a.eqResult b

/-- Spec-level IEEE ordered less-than result (boolean + flags). -/
def ltResultSpec {spec : BinarySpec} (a b : FloatBits spec) : OpResult Bool :=
  a.ltResult b

/-- Spec-level IEEE ordered less-or-equal result (boolean + flags). -/
def leResultSpec {spec : BinarySpec} (a b : FloatBits spec) : OpResult Bool :=
  a.leResult b

/-- Spec-level IEEE minimumNumber result. -/
def minNumResultSpec {spec : BinarySpec} (a b : FloatBits spec) : OpResult (FloatBits spec) :=
  a.minNumResult b

/-- Spec-level IEEE maximumNumber result. -/
def maxNumResultSpec {spec : BinarySpec} (a b : FloatBits spec) : OpResult (FloatBits spec) :=
  a.maxNumResult b

end Flean
