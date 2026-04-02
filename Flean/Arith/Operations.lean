import Flean.Binary.Defs
import Flean.Binary.Special
import Flean.Core.Rounding
import Flean.Arith.Exceptions

/-!
# Flean.Arith.Operations

IEEE 754 arithmetic operation specifications.
Defines the expected behavior of add, sub, mul, div, sqrt
including special-value handling and exception raising.
-/

namespace Flean

/-- Negate a FloatBits by flipping the sign bit. -/
def FloatBits.negate {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  let mask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  ⟨f.bits ^^^ mask⟩

/-- Absolute value: clear the sign bit. -/
def FloatBits.abs {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  let mask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  ⟨f.bits &&& (~~~ mask)⟩

/-- Is the sign bit set (negative)? -/
def FloatBits.isNeg {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.signBit != 0

/-- Copy sign from `src` to `dst`. -/
def FloatBits.copySign {spec : BinarySpec} (dst src : FloatBits spec) : FloatBits spec :=
  let signMask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  let dstCleared := dst.bits &&& (~~~ signMask)
  let srcSign := src.bits &&& signMask
  ⟨dstCleared ||| srcSign⟩

/-- Specification of addition behavior for special values.
    Returns `none` when both operands are finite (requires rounding). -/
def FloatBits.addSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  -- NaN propagation
  | .nan, _ => some { value := a }
  | _, .nan => some { value := b }
  -- inf + inf: same sign = inf, opposite sign = NaN
  | .infinite, .infinite =>
    if a.isNeg == b.isNeg then
      some { value := a }
    else
      some { value := FloatBits.quietNaN spec,
             flags := { invalidOperation := true } }
  -- inf + finite = inf
  | .infinite, _ => some { value := a }
  | _, .infinite => some { value := b }
  -- Both finite: delegate to rounding
  | _, _ => none

/-- Specification of multiplication behavior for special values. -/
def FloatBits.mulSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some { value := a }
  | _, .nan => some { value := b }
  -- inf * 0 = NaN (invalid)
  | .infinite, .zero | .zero, .infinite =>
    some { value := FloatBits.quietNaN spec,
           flags := { invalidOperation := true } }
  -- inf * nonzero = inf with XOR sign
  | .infinite, _ =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec
                  else FloatBits.negInf spec
    some { value := result }
  | _, .infinite =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec
                  else FloatBits.negInf spec
    some { value := result }
  -- 0 * finite = 0 with XOR sign
  | .zero, _ =>
    let result := if a.isNeg == b.isNeg then FloatBits.posZero spec
                  else FloatBits.negZero spec
    some { value := result }
  | _, .zero =>
    let result := if a.isNeg == b.isNeg then FloatBits.posZero spec
                  else FloatBits.negZero spec
    some { value := result }
  | _, _ => none

/-- Specification of division behavior for special values. -/
def FloatBits.divSpecial {spec : BinarySpec}
    (a b : FloatBits spec) : Option (OpResult (FloatBits spec)) :=
  match a.classify, b.classify with
  | .nan, _ => some { value := a }
  | _, .nan => some { value := b }
  -- inf / inf = NaN
  | .infinite, .infinite =>
    some { value := FloatBits.quietNaN spec,
           flags := { invalidOperation := true } }
  -- inf / finite = inf
  | .infinite, _ =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec
                  else FloatBits.negInf spec
    some { value := result }
  -- finite / inf = 0
  | _, .infinite =>
    let result := if a.isNeg == b.isNeg then FloatBits.posZero spec
                  else FloatBits.negZero spec
    some { value := result }
  -- 0 / 0 = NaN
  | .zero, .zero =>
    some { value := FloatBits.quietNaN spec,
           flags := { invalidOperation := true } }
  -- finite / 0 = inf (division by zero)
  | _, .zero =>
    let result := if a.isNeg == b.isNeg then FloatBits.posInf spec
                  else FloatBits.negInf spec
    some { value := result, flags := { divisionByZero := true } }
  -- 0 / finite = 0
  | .zero, _ =>
    let result := if a.isNeg == b.isNeg then FloatBits.posZero spec
                  else FloatBits.negZero spec
    some { value := result }
  | _, _ => none

end Flean
