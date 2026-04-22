import Flean.Binary.Properties
import Flean.Core.Rounding
import Flean.Core.RoundProps
import Flean.Arith.Spec
import Flean.Arith.Exceptions
import Flean.Arith.RoundingHelper

/-!
# Flean.Arith.Operations

IEEE 754 arithmetic operation specifications.
Fully refactored to support all rounding modes, gradual underflow,
and all required IEEE 754-2019 operations.
-/

namespace Flean

noncomputable def inexactFlag (exact rounded : ℝ) : Bool := by
  classical
  exact decide (rounded ≠ exact)

noncomputable def overflowFlag (fmt : FloatFormat) (exact : ℝ) : Bool := by
  classical
  exact decide (maxFinite fmt < |exact|)

/-- Tininess check based on the exact (pre-rounding) result. -/
noncomputable def tinyBeforeRoundingFlag (fmt : FloatFormat) (exact : ℝ) : Bool := by
  classical
  exact decide (exact ≠ 0 ∧ |exact| < minNormal fmt)

/-- Tininess check based on the rounded (post-rounding) result. -/
noncomputable def tinyAfterRoundingFlag (fmt : FloatFormat) (rounded : ℝ) : Bool := by
  classical
  exact decide (|rounded| < minNormal fmt)

/-- Underflow flag with configurable tininess detection point. -/
noncomputable def underflowFlagWithTininess
    (fmt : FloatFormat) (tininess : TininessDetectionMode) (exact rounded : ℝ) : Bool := by
  classical
  exact decide (rounded ≠ exact ∧
    match tininess with
    | .beforeRounding => exact ≠ 0 ∧ |exact| < minNormal fmt
    | .afterRounding => |rounded| < minNormal fmt)

noncomputable def underflowFlag (fmt : FloatFormat) (exact rounded : ℝ) : Bool := by
  classical
  exact decide (rounded ≠ exact ∧ exact ≠ 0 ∧ |exact| < minNormal fmt)

noncomputable def addZeroSign {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode) : Bool :=
  if a.classify = .zero ∧ b.classify = .zero then
    if a.isNeg == b.isNeg then a.isNeg else mode = .roundTowardNegative
  else
    let exact := a.toReal + b.toReal
    if exact < 0 then true else if exact > 0 then false else mode = .roundTowardNegative

def mulZeroSign {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  a.isNeg != b.isNeg

def unaryNaNResult {spec : BinarySpec} (a : FloatBits spec) : OpResult (FloatBits spec) :=
  { value := a.quietedNaN, flags := { invalidOperation := a.isSignalingNaN } }

/-- Select which NaN payload source to use for a binary NaN result. -/
def chooseNaNOperand {spec : BinarySpec}
    (policy : NaNPropagationPolicy) (a b : FloatBits spec) : FloatBits spec :=
  match policy with
  | .preferLeft => a
  | .preferRight => b
  | .preferLargerPayload =>
      if a.nanPayload.toNat ≥ b.nanPayload.toNat then a else b

/-- Binary NaN result with configurable payload-selection policy. -/
def binaryNaNResultWithPolicy {spec : BinarySpec}
    (policy : NaNPropagationPolicy) (a b : FloatBits spec) : OpResult (FloatBits spec) :=
  if a.classify == .nan || b.classify == .nan then
    let picked :=
      if a.classify == .nan && b.classify == .nan then
        chooseNaNOperand policy a b
      else if a.classify == .nan then
        a
      else
        b
    { value := picked.quietedNaN
      flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN } }
  else
    { value := FloatBits.quietNaN spec }

def binaryNaNResult {spec : BinarySpec} (a b : FloatBits spec) : OpResult (FloatBits spec) :=
  if a.classify == .nan then
    { value := a.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN } }
  else
    { value := b.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN } }

/-- Copy sign from `src` to `dst`. -/
def FloatBits.copySign {spec : BinarySpec} (dst src : FloatBits spec) : FloatBits spec :=
  let signMask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  let dstCleared := dst.bits &&& (~~~ signMask)
  let srcSign := src.bits &&& signMask
  ⟨dstCleared ||| srcSign⟩

/-- Compare magnitudes by exponent/significand bit pattern (ignoring sign bit). -/
def FloatBits.finiteMagGE {spec : BinarySpec} (a b : FloatBits spec) : Bool :=
  let width := spec.expWidth + spec.sigWidth
  let amag := (a.bits.extractLsb' 0 width).toNat
  let bmag := (b.bits.extractLsb' 0 width).toNat
  amag ≥ bmag

/-- Specification of addition behavior for special values. -/
def FloatBits.addSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some (binaryNaNResult a b)
  | _, .nan => some (binaryNaNResult a b)
  | .infinite, .infinite =>
    if a.isNeg == b.isNeg then some { value := a }
    else some { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _ => some { value := a }
  | _, .infinite => some { value := b }
  | _, _ => none

/-- Specification of multiplication behavior for special values. -/
def FloatBits.mulSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some (binaryNaNResult a b)
  | _, .nan => some (binaryNaNResult a b)
  | .infinite, .zero | .zero, .infinite =>
    some { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _ | _, .infinite =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec else FloatBits.negInf spec
    some { value := result }
  | .zero, _ | _, .zero =>
    let result := if mulZeroSign a b then FloatBits.negZero spec else FloatBits.posZero spec
    some { value := result }
  | _, _ => none

/-- Specification of division behavior for special values. -/
def FloatBits.divSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some (binaryNaNResult a b)
  | _, .nan => some (binaryNaNResult a b)
  | .infinite, .infinite | .zero, .zero =>
    some { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _ | _, .zero =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec else FloatBits.negInf spec
    let flags := if b.classify == .zero then { divisionByZero := true } else {}
    some { value := result, flags := flags }
  | _, .infinite | .zero, _ =>
    let result := if a.isNeg == b.isNeg then FloatBits.posZero spec else FloatBits.negZero spec
    some { value := result }
  | _, _ => none

/-- Perform finite floating-point addition (same sign). -/
noncomputable def FloatBits.addFiniteSameSign {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let diff := e1 - e2
  let m1Ext := m1.toNat <<< 2
  let m2Ext := m2.toNat <<< 2
  let m2Aligned := m2Ext / 2 ^ diff
  let sticky := if m2Ext % 2 ^ diff != 0 then 1 else 0
  let sum := m1Ext + m2Aligned + sticky
  roundAndPack mode f1.isNeg (e1 : Int) (sum / 4)

/-- Perform finite floating-point addition (opposite sign). -/
noncomputable def FloatBits.addFiniteOppositeSign {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let p := spec.sigWidth
  let diff := e1 - e2
  let m1Ext := m1.toNat <<< 2
  let m2Ext := m2.toNat <<< 2
  let m2Aligned := m2Ext / 2 ^ diff
  let sticky := if m2Ext % 2 ^ diff != 0 then 1 else 0
  if m1Ext + sticky ≥ m2Aligned then
    let diffVal := (m1Ext + sticky) - m2Aligned
    if diffVal == 0 then
      let z := if mode = .roundTowardNegative then FloatBits.negZero spec else FloatBits.posZero spec
      { value := z }
    else
      let hbit := Nat.log2 diffVal
      let shiftNeeded := (p + 2) - hbit
      let rawExp := (e1 : Int) - shiftNeeded
      let scaledSig := diffVal <<< shiftNeeded
      roundAndPack mode f1.isNeg rawExp (scaledSig / 4)
  else
    let diffVal := m2Aligned - (m1Ext + sticky)
    if diffVal == 0 then
      let z := if mode = .roundTowardNegative then FloatBits.negZero spec else FloatBits.posZero spec
      { value := z }
    else
      let hbit := Nat.log2 diffVal
      let shiftNeeded := (p + 2) - hbit
      let rawExp := (e1 : Int) - shiftNeeded
      let scaledSig := diffVal <<< shiftNeeded
      roundAndPack mode f2.isNeg rawExp (scaledSig / 4)

/-- Perform finite floating-point multiplication. -/
noncomputable def FloatBits.mulFinite {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let isNeg := f1.isNeg != f2.isNeg
  let p := spec.sigWidth
  let bias := spec.bias
  let prod := m1.toNat * m2.toNat
  let rawExp : Int := (e1 : Int) + (e2 : Int) - (bias : Int)
  if prod ≥ 2 ^ (2 * p + 1) then roundAndPack mode isNeg (rawExp + 1) (prod / 2)
  else roundAndPack mode isNeg rawExp prod

/-- Perform finite floating-point division. -/
noncomputable def FloatBits.divFinite {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let isNeg := f1.isNeg != f2.isNeg
  let p := spec.sigWidth
  let bias := spec.bias
  let dividend := m1.toNat <<< (p + 2)
  let q := dividend / m2.toNat
  let r := dividend % m2.toNat
  let qWithSticky := if r != 0 then q ||| 1 else q
  let rawExp : Int := (e1 : Int) - (e2 : Int) + (bias : Int)
  if qWithSticky ≥ 2 ^ (2 * p + 2) then roundAndPack mode isNeg (rawExp + 1) (qWithSticky / 4)
  else roundAndPack mode isNeg rawExp (qWithSticky / 2)

/-- Main addition function. -/
noncomputable def FloatBits.add {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  match f1.addSpecial f2 with
  | some res => res
  | none =>
      match f1.classify, f2.classify with
      | .zero, .zero =>
          let z := if addZeroSign f1 f2 mode then FloatBits.negZero spec else FloatBits.posZero spec
          { value := z }
      | .zero, _ => { value := f2 }
      | _, .zero => { value := f1 }
      | _, _ =>
          let (a, b) := if FloatBits.finiteMagGE f1 f2 then (f1, f2) else (f2, f1)
          if a.isNeg == b.isNeg then
            a.addFiniteSameSign b mode
          else
            a.addFiniteOppositeSign b mode

/-- Main multiplication function. -/
noncomputable def FloatBits.mul {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  match f1.mulSpecial f2 with
  | some res => res
  | none => f1.mulFinite f2 mode

/-- Main division function. -/
noncomputable def FloatBits.div {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  match f1.divSpecial f2 with
  | some res => res
  | none => f1.divFinite f2 mode

/-- scaleB(x, N): Compute x * 2^N, rounding according to `mode` when needed. -/
noncomputable def FloatBits.scaleB {spec : BinarySpec} (f : FloatBits spec) (N : Int)
    (mode : RoundingMode := .roundNearestTiesToEven) :
    OpResult (FloatBits spec) :=
  match f.classify with
  | .nan | .infinite | .zero => { value := f }
  | .normal | .subnormal =>
    let (m, e) := f.getExtendedSignificand
    roundAndPack mode f.isNeg ((e : Int) + N) m.toNat

end Flean
