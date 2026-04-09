import Flean.Arith.Operations
import Flean.Arith.ULP
import Flean.Core.RoundProps

/-!
# Flean.Arith.MiscOps

Additional IEEE 754-style operations: remainder, logB, and quantize.
-/

namespace Flean

/-- Round a real to an integer according to the IEEE rounding mode. -/
private noncomputable def roundToIntByMode (mode : RoundingMode) (x : ℝ) : ℤ :=
  match mode with
  | .roundTowardZero => ztrunc x
  | .roundTowardPositive => ⌈x⌉
  | .roundTowardNegative => ⌊x⌋
  | .roundNearestTiesToEven => roundNearestEven x
  | .roundNearestTiesAway => roundNearestAway x

/-- IEEE-style remainder.
    Default behavior uses nearest-integer quotient with ties to even. -/
noncomputable def FloatBits.remainderResult {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven) :
    OpResult (FloatBits spec) :=
  match a.classify, b.classify with
  | .nan, _ => binaryNaNResult a b
  | _, .nan => binaryNaNResult a b
  | .infinite, _ =>
      { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | _, .zero =>
      { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .zero, _ => { value := a }
  | _, .infinite => { value := a }
  | _, _ =>
      let q : ℤ := roundToIntByMode mode (a.toReal / b.toReal)
      let exact := a.toReal - (q : ℝ) * b.toReal
      { value := FloatBits.ofRealOrInfSigned spec exact a.isNeg }

/-- Value-only remainder wrapper. -/
noncomputable def FloatBits.remainder {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven) :
    FloatBits spec :=
  (a.remainderResult b mode).value

/-- Exponent returned by logB for finite nonzero values. -/
private def finiteLogBExponent {spec : BinarySpec} (f : FloatBits spec) : Int :=
  match f.classify with
  | .normal =>
      (f.expField.toNat : Int) - (spec.bias : Int)
  | .subnormal =>
      let k := Nat.log2 f.sigField.toNat
      (1 - (spec.bias : Int) - (spec.sigWidth : Int)) + (k : Int)
  | _ => 0

/-- IEEE-style logB on packed floats. -/
noncomputable def FloatBits.logBResult {spec : BinarySpec}
    (f : FloatBits spec) : OpResult (FloatBits spec) :=
  match f.classify with
  | .nan => unaryNaNResult f
  | .infinite => { value := FloatBits.posInf spec }
  | .zero => { value := FloatBits.negInf spec, flags := { divisionByZero := true } }
  | .normal | .subnormal =>
      let e := finiteLogBExponent f
      { value := FloatBits.ofRealOrInfSigned spec (e : ℝ) false }

/-- Value-only logB wrapper. -/
noncomputable def FloatBits.logB {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  (f.logBResult).value

/-- IEEE-style quantize to the quantum determined by `y`.
    For binary formats here, the quantum is `ULP(y)`. -/
noncomputable def FloatBits.quantizeResult {spec : BinarySpec}
    (x y : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven) :
    OpResult (FloatBits spec) :=
  match x.classify, y.classify with
  | .nan, _ => binaryNaNResult x y
  | _, .nan => binaryNaNResult x y
  | .infinite, .infinite => { value := x }
  | .infinite, _ =>
      { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | _, .infinite =>
      { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | _, _ =>
      let quantumExp := ulpExp spec y.expField.toNat
      let quantum : ℝ := (2 : ℝ) ^ quantumExp
      let scaled := x.toReal / quantum
      let q : ℤ := roundToIntByMode mode scaled
      let rounded := (q : ℝ) * quantum
      let flags := {
        inexact := inexactFlag x.toReal rounded
        overflow := overflowFlag spec.toFormat rounded
        underflow := underflowFlag spec.toFormat x.toReal rounded
      }
      { value := FloatBits.ofRealOrInfSigned spec rounded x.isNeg, flags := flags }

/-- Value-only quantize wrapper. -/
noncomputable def FloatBits.quantize {spec : BinarySpec}
    (x y : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven) :
    FloatBits spec :=
  (x.quantizeResult y mode).value

end Flean
