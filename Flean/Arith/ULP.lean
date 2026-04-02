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

/-- Successor of a finite positive FloatBits (increment raw bits by 1).
    This gives the next representable floating-point number. -/
def FloatBits.nextUp {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  ⟨f.bits + 1⟩

/-- Predecessor of a finite positive FloatBits (decrement raw bits by 1).
    This gives the previous representable floating-point number. -/
def FloatBits.nextDown {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  ⟨f.bits - 1⟩

/-- The distance in ULPs between two FloatBits with the same sign,
    measured as the absolute difference of their raw bit representations. -/
def FloatBits.ulpDist {spec : BinarySpec} (a b : FloatBits spec) : Nat :=
  if a.bits.toNat ≥ b.bits.toNat then
    a.bits.toNat - b.bits.toNat
  else
    b.bits.toNat - a.bits.toNat

end Flean
