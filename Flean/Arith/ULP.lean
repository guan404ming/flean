import Flean.Binary.Defs

/-!
# Flean.Arith.ULP

Unit in the Last Place (ULP) for IEEE 754 floating-point numbers.
ULP measures the spacing between adjacent floating-point numbers.
-/

namespace Flean

/-- ULP weight as a power of 2 for a normal number with biased exponent `e`.
    For a normal number: ulpExp = e - bias - sigWidth
    For a subnormal: ulpExp = 1 - bias - sigWidth -/
def ulpExp (spec : BinarySpec) (biasedExp : Nat) : Int :=
  if biasedExp == 0 then
    1 - (spec.bias : Int) - (spec.sigWidth : Int)
  else
    (biasedExp : Int) - (spec.bias : Int) - (spec.sigWidth : Int)

/-- ULP as a natural number in terms of significand units.
    Always 1 when viewed at the significand level. -/
def ulpSignificand : Nat := 1

/-- Smallest positive subnormal value for the given format. -/
private def minSubnormalPos (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields 0 0 (BitVec.ofNat spec.sigWidth 1)

/-- Smallest negative subnormal value for the given format. -/
private def minSubnormalNeg (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields (BitVec.ofNat 1 1) 0 (BitVec.ofNat spec.sigWidth 1)

/-- Largest finite negative value for the given format. -/
private def maxFiniteNeg (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields (BitVec.ofNat 1 1)
    (BitVec.ofNat spec.expWidth (2 ^ spec.expWidth - 2))
    (BitVec.allOnes spec.sigWidth)

/-- IEEE 754 nextUp: least representable value strictly greater than `f`. -/
def FloatBits.nextUp {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  match f.classify with
  | .nan => f
  | .infinite => if f.isNeg then maxFiniteNeg spec else f
  | .zero => minSubnormalPos spec
  | .normal | .subnormal =>
      if f.isNeg then
        ⟨f.bits - 1⟩
      else
        ⟨f.bits + 1⟩

/-- IEEE 754 nextDown: greatest representable value strictly less than `f`. -/
def FloatBits.nextDown {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  match f.classify with
  | .nan => f
  | .infinite => if f.isNeg then f else FloatBits.maxFinite spec
  | .zero => minSubnormalNeg spec
  | .normal | .subnormal =>
      if f.isNeg then
        ⟨f.bits + 1⟩
      else
        ⟨f.bits - 1⟩

/-- The distance in ULPs between two FloatBits with the same sign,
    measured as the absolute difference of their raw bit representations. -/
def FloatBits.ulpDist {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  if a.bits.toNat ≥ b.bits.toNat then
    a.bits.toNat - b.bits.toNat
  else
    b.bits.toNat - a.bits.toNat

end Flean
