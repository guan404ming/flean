import Flean.Arith.Operations

/-!
# Flean.Arith.FMA

IEEE 754 fused multiply-add semantics for `FloatBits`.
-/

namespace Flean

/-- Sign of an exact-zero FMA result. IEEE directed rounding selects `-0`
for roundTowardNegative; otherwise we use `+0`. -/
def fmaZeroSign (a b c : Bool) (mode : RoundingMode) : Bool :=
  let _ := a
  let _ := b
  let _ := c
  mode = .roundTowardNegative

/-- Main fused multiply-add function with explicit tininess-detection mode. -/
noncomputable def FloatBits.fmaWithTininess {spec : BinarySpec}
    (a b c : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven)
    (tininess : TininessDetectionMode := .beforeRounding) :
    OpResult (FloatBits spec) :=
  match a.classify, b.classify, c.classify with
  | .nan, _, _ => { value := a.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN } }
  | _, .nan, _ => { value := b.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN } }
  | _, _, .nan => { value := c.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN } }
  | .infinite, .zero, _ | .zero, .infinite, _ =>
      { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _, .infinite | _, .infinite, .infinite =>
      let prodNeg := mulZeroSign a b
      if prodNeg == c.isNeg then
        let result := if prodNeg then FloatBits.negInf spec else FloatBits.posInf spec
        { value := result }
      else
        { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _, _ | _, .infinite, _ =>
      let result := if mulZeroSign a b then FloatBits.negInf spec else FloatBits.posInf spec
      { value := result }
  | _, _, .infinite =>
      { value := c }
  | _, _, _ =>
      let exact := a.toReal * b.toReal + c.toReal
      let rounded := fmaSpec spec.toFormat mode a.toReal b.toReal c.toReal
      let flags := {
        inexact := inexactFlag exact rounded
        overflow := overflowFlag spec.toFormat exact
        underflow := underflowFlagWithTininess spec.toFormat tininess exact rounded
      }
      { value := FloatBits.ofRealOrInfSigned spec rounded (fmaZeroSign a.isNeg b.isNeg c.isNeg mode),
        flags := flags }

/-- Main fused multiply-add function. -/
noncomputable def FloatBits.fma {spec : BinarySpec}
    (a b c : FloatBits spec) (mode : RoundingMode := .roundNearestTiesToEven) :
    OpResult (FloatBits spec) :=
  match a.classify, b.classify, c.classify with
  | .nan, _, _ => { value := a.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN } }
  | _, .nan, _ => { value := b.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN } }
  | _, _, .nan => { value := c.quietedNaN, flags := { invalidOperation := a.isSignalingNaN || b.isSignalingNaN || c.isSignalingNaN } }
  | .infinite, .zero, _ | .zero, .infinite, _ =>
      { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _, .infinite | _, .infinite, .infinite =>
      let prodNeg := mulZeroSign a b
      if prodNeg == c.isNeg then
        let result := if prodNeg then FloatBits.negInf spec else FloatBits.posInf spec
        { value := result }
      else
        { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _, _ | _, .infinite, _ =>
      let result := if mulZeroSign a b then FloatBits.negInf spec else FloatBits.posInf spec
      { value := result }
  | _, _, .infinite =>
      { value := c }
  | _, _, _ =>
      let exact := a.toReal * b.toReal + c.toReal
      let rounded := fmaSpec spec.toFormat mode a.toReal b.toReal c.toReal
      let flags := {
        inexact := inexactFlag exact rounded
        overflow := overflowFlag spec.toFormat exact
        underflow := underflowFlag spec.toFormat exact rounded
      }
      { value := FloatBits.ofRealOrInfSigned spec rounded (fmaZeroSign a.isNeg b.isNeg c.isNeg mode),
        flags := flags }

end Flean
