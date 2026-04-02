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

/-- Predicate: is this value a NaN? -/
def FloatBits.isNaN {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .nan

/-- Predicate: is this value an infinity? -/
def FloatBits.isInfinite {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .infinite

/-- Predicate: is this value a zero (pos or neg)? -/
def FloatBits.isZero {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .zero

/-- Predicate: is this value subnormal? -/
def FloatBits.isSubnormal {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .subnormal

/-- Predicate: is this value finite (not NaN or infinity)? -/
def FloatBits.isFinite {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  match f.classify with
  | .nan | .infinite => false
  | _ => true

end Flean
