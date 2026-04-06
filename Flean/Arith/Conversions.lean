import Flean.Binary.Properties
import Flean.Arith.Spec
import Flean.Arith.Operations
import Flean.Arith.RoundingHelper

/-!
# Flean.Arith.Conversions (Extended for Mixed Precision)

Support for casting between different floating-point formats (e.g., f32 to f16).
Crucial for ML compiler mixed-precision analysis.
-/

namespace Flean

private def castNaNValue {srcSpec dstSpec : BinarySpec} (f : FloatBits srcSpec) : FloatBits dstSpec :=
  let quietMask := BitVec.ofNat dstSpec.sigWidth (1 <<< (dstSpec.sigWidth - 1))
  let payload := BitVec.ofNat dstSpec.sigWidth f.sigField.toNat
  FloatBits.fromFields f.signBit (BitVec.allOnes dstSpec.expWidth) (payload ||| quietMask)

/-- Generic cast between two different BinarySpecs.
    This is the core operation for mixed-precision ML compilers. -/
noncomputable def FloatBits.cast {srcSpec dstSpec : BinarySpec}
    (f : FloatBits srcSpec) (mode : RoundingMode) :
    OpResult (FloatBits dstSpec) :=
  match f.classify with
  | .nan =>
    { value := castNaNValue f,
      flags := { invalidOperation := f.isSignalingNaN } }
  | .infinite => { value := if f.isNeg then FloatBits.negInf dstSpec else FloatBits.posInf dstSpec }
  | .zero | .normal | .subnormal =>
    let exact := f.toReal
    let rounded := castSpec srcSpec.toFormat dstSpec.toFormat mode exact
    let flags := {
      inexact := inexactFlag exact rounded
      overflow := overflowFlag dstSpec.toFormat exact
      underflow := underflowFlag dstSpec.toFormat exact rounded
    }
    { value := FloatBits.ofRealOrInfSigned dstSpec rounded f.isNeg, flags := flags }

end Flean
