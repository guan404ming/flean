import Flean.Binary.Defs

/-!
# Flean.Arith.Compare

IEEE 754 comparison operations for floating-point numbers.
Special handling for NaNs and signed zeros.
-/

namespace Flean

/-- IEEE 754 equality: -0 == +0, and any NaN comparison is false. -/
def FloatBits.eq {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  if f1.classify == .nan || f2.classify == .nan then
    false
  else if f1.classify == .zero && f2.classify == .zero then
    true
  else
    f1.bits == f2.bits

/-- IEEE 754 less-than comparison. -/
def FloatBits.lt {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  if f1.classify == .nan || f2.classify == .nan then
    false
  else
    let s1 := f1.isNeg
    let s2 := f2.isNeg
    match s1, s2 with
    | true, false => 
      -- f1 < 0, f2 >= 0: true unless both are zero
      !(f1.classify == .zero && f2.classify == .zero)
    | false, true => 
      -- f1 >= 0, f2 < 0: false
      false
    | true, true =>
      -- Both negative: larger magnitude means smaller value
      f1.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) > 
      f2.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth)
    | false, false =>
      -- Both positive: larger magnitude means larger value
      f1.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) < 
      f2.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth)

def FloatBits.le {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  f1.lt f2 || f1.eq f2

/-- minNum: returns the minimum of two numbers, preferring the non-NaN one. -/
def FloatBits.minNum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  if f1.classify == .nan then f2
  else if f2.classify == .nan then f1
  else if f1.lt f2 then f1 else f2

/-- maxNum: returns the maximum of two numbers, preferring the non-NaN one. -/
def FloatBits.maxNum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  if f1.classify == .nan then f2
  else if f2.classify == .nan then f1
  else if f2.lt f1 then f1 else f2

end Flean
