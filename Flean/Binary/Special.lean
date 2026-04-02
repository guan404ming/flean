import Flean.Binary.Defs

/-!
# Flean.Binary.Special

Constructors and predicates for IEEE 754 special values:
positive/negative zero, positive/negative infinity, quiet NaN, signaling NaN.
-/

namespace Flean

/-- Positive zero: sign=0, exp=0, sig=0. -/
def FloatBits.posZero (spec : BinarySpec) : FloatBits spec :=
  ⟨0⟩

/-- Negative zero: sign=1, exp=0, sig=0. -/
def FloatBits.negZero (spec : BinarySpec) : FloatBits spec :=
  ⟨BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))⟩

/-- Positive infinity: sign=0, exp=all ones, sig=0. -/
def FloatBits.posInf (spec : BinarySpec) : FloatBits spec :=
  let expAllOnes := (2 ^ spec.expWidth - 1) <<< spec.sigWidth
  ⟨BitVec.ofNat spec.totalWidth expAllOnes⟩

/-- Negative infinity: sign=1, exp=all ones, sig=0. -/
def FloatBits.negInf (spec : BinarySpec) : FloatBits spec :=
  let signBit := 1 <<< (spec.expWidth + spec.sigWidth)
  let expAllOnes := (2 ^ spec.expWidth - 1) <<< spec.sigWidth
  ⟨BitVec.ofNat spec.totalWidth (signBit ||| expAllOnes)⟩

/-- Canonical quiet NaN: sign=0, exp=all ones, sig MSB=1, rest=0. -/
def FloatBits.quietNaN (spec : BinarySpec) : FloatBits spec :=
  let expAllOnes := (2 ^ spec.expWidth - 1) <<< spec.sigWidth
  let qBit := 1 <<< (spec.sigWidth - 1)
  ⟨BitVec.ofNat spec.totalWidth (expAllOnes ||| qBit)⟩

/-- Maximum finite positive value: sign=0, exp=max-1, sig=all ones. -/
def FloatBits.maxFinite (spec : BinarySpec) : FloatBits spec :=
  let expMaxMinus1 := (2 ^ spec.expWidth - 2) <<< spec.sigWidth
  let sigAllOnes := 2 ^ spec.sigWidth - 1
  ⟨BitVec.ofNat spec.totalWidth (expMaxMinus1 ||| sigAllOnes)⟩

end Flean
