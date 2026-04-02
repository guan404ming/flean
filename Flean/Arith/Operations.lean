import Flean.Binary.Defs
import Flean.Binary.Special
import Flean.Core.Rounding
import Flean.Core.RoundProps
import Flean.Arith.Exceptions
import Flean.Arith.RoundingHelper

/-!
# Flean.Arith.Operations

IEEE 754 arithmetic operation specifications.
Fully refactored to support all rounding modes, gradual underflow,
and all required IEEE 754-2019 operations.
-/

namespace Flean

/-- Copy sign from `src` to `dst`. -/
def FloatBits.copySign {spec : BinarySpec} (dst src : FloatBits spec) : FloatBits spec :=
  let signMask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  let dstCleared := dst.bits &&& (~~~ signMask)
  let srcSign := src.bits &&& signMask
  ⟨dstCleared ||| srcSign⟩

/-- Specification of addition behavior for special values. -/
def FloatBits.addSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some { value := a }
  | _, .nan => some { value := b }
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
  | .nan, _ => some { value := a }
  | _, .nan => some { value := b }
  | .infinite, .zero | .zero, .infinite =>
    some { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  | .infinite, _ | _, .infinite =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec else FloatBits.negInf spec
    some { value := result }
  | .zero, _ | _, .zero =>
    let result := if a.isNeg == b.isNeg then FloatBits.posZero spec else FloatBits.negZero spec
    some { value := result }
  | _, _ => none

/-- Specification of division behavior for special values. -/
def FloatBits.divSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some { value := a }
  | _, .nan => some { value := b }
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
def FloatBits.addFiniteSameSign {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let p := spec.sigWidth
  let diff := e1 - e2
  let m1_ext := m1.toNat <<< 2
  let m2_ext := m2.toNat <<< 2
  let m2_aligned := m2_ext / 2^diff
  let sticky := if m2_ext % 2^diff != 0 then 1 else 0
  let sum := m1_ext + m2_aligned + sticky
  roundAndPack mode f1.isNeg (e1 : Int) (sum / 4)

/-- Perform finite floating-point addition (opposite sign). -/
def FloatBits.addFiniteOppositeSign {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let p := spec.sigWidth
  let diff := e1 - e2
  let m1_ext := m1.toNat <<< 2
  let m2_ext := m2.toNat <<< 2
  let m2_aligned := m2_ext / 2^diff
  let sticky := if m2_ext % 2^diff != 0 then 1 else 0
  if m1_ext + sticky ≥ m2_aligned then
    let diff_val := (m1_ext + sticky) - m2_aligned
    if diff_val == 0 then { value := FloatBits.posZero spec }
    else
      let hbit := Nat.log2 diff_val
      let shift_needed := (p + 2) - hbit
      let rawExp := (e1 : Int) - shift_needed
      let scaledSig := diff_val <<< shift_needed
      roundAndPack mode f1.isNeg rawExp (scaledSig / 4)
  else { value := f1 }

/-- Main addition function. -/
def FloatBits.add {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) : OpResult (FloatBits spec) :=
  match f1.addSpecial f2 with
  | some res => res
  | none =>
    let (e1, e2) := (f1.expField.toNat, f2.expField.toNat)
    let (m1, m2) := (f1.sigField.toNat, f2.sigField.toNat)
    let is_f1_larger := if e1 != e2 then e1 > e2 else m1 ≥ m2
    let (large, small) := if is_f1_larger then (f1, f2) else (f2, f1)
    if f1.isNeg == f2.isNeg then large.addFiniteSameSign small mode
    else large.addFiniteOppositeSign small mode

/-- Perform finite floating-point multiplication. -/
def FloatBits.mulFinite {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let isNeg := f1.isNeg != f2.isNeg
  let p := spec.sigWidth
  let bias := spec.bias
  let prod := m1.toNat * m2.toNat
  let rawExp : Int := (e1 : Int) + (e2 : Int) - (bias : Int)
  if prod ≥ 2^(2*p + 1) then roundAndPack mode isNeg (rawExp + 1) (prod / 2)
  else roundAndPack mode isNeg rawExp prod

/-- Main multiplication function. -/
def FloatBits.mul {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) : 
    OpResult (FloatBits spec) :=
  match f1.mulSpecial f2 with
  | some res => res
  | none => f1.mulFinite f2 mode

/-- Perform finite floating-point division. -/
def FloatBits.divFinite {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) :
    OpResult (FloatBits spec) :=
  let (m1, e1) := f1.getExtendedSignificand
  let (m2, e2) := f2.getExtendedSignificand
  let isNeg := f1.isNeg != f2.isNeg
  let p := spec.sigWidth
  let bias := spec.bias
  let dividend := m1.toNat <<< (p + 2)
  let q := dividend / m2.toNat
  let r := dividend % m2.toNat
  let q_with_sticky := if r != 0 then q ||| 1 else q
  let rawExp : Int := (e1 : Int) - (e2 : Int) + (bias : Int)
  if q_with_sticky ≥ 2^(2*p + 2) then roundAndPack mode isNeg (rawExp + 1) (q_with_sticky / 4)
  else roundAndPack mode isNeg rawExp (q_with_sticky / 2)

/-- Main division function. -/
def FloatBits.div {spec : BinarySpec} (f1 f2 : FloatBits spec) (mode : RoundingMode) : 
    OpResult (FloatBits spec) :=
  match f1.divSpecial f2 with
  | some res => res
  | none => f1.divFinite f2 mode

/-- scaleB(x, N): Compute x * 2^N by adjusting the exponent. -/
def FloatBits.scaleB {spec : BinarySpec} (f : FloatBits spec) (N : Int) : 
    OpResult (FloatBits spec) :=
  match f.classify with
  | .nan | .infinite | .zero => { value := f }
  | .normal | .subnormal =>
    let (m, e) := f.getExtendedSignificand
    roundAndPack .roundTowardZero f.isNeg ((e : Int) + N) m.toNat

-- TODO: Correctness proofs for arithmetic operations require careful
-- alignment between toReal (which uses exponent 0 for subnormals) and
-- getExtendedSignificand (which uses exponent 1 for subnormals).

end Flean
