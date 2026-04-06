import Flean.Binary.Properties
import Flean.Arith.Spec
import Flean.Arith.Operations

/-!
# Flean.Arith.Sqrt

IEEE 754 square root semantics for `FloatBits`.
-/

namespace Flean

/-- Main square root function. -/
noncomputable def FloatBits.sqrt {spec : BinarySpec}
    (f : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven) :
    OpResult (FloatBits spec) :=
  match f.classify with
  | .nan => unaryNaNResult f
  | .infinite =>
      if f.isNeg then
        { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
      else
        { value := f }
  | .zero => { value := f }
  | .normal | .subnormal =>
      if f.isNeg then
        { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
      else
        let exact := Real.sqrt f.toReal
        let rounded := sqrtSpec spec.toFormat mode f.toReal
        let flags := {
          inexact := inexactFlag exact rounded
          overflow := overflowFlag spec.toFormat exact
          underflow := underflowFlag spec.toFormat exact rounded
        }
        { value := FloatBits.ofRealOrInfSigned spec rounded false, flags := flags }

end Flean
