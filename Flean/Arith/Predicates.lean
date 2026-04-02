import Flean.Binary.Defs
import Flean.Binary.Special

/-!
# Flean.Arith.Predicates

IEEE 754 classification predicates and totalOrder.
Provides standard functions like isFinite, isNormal, and totalOrder.
-/

namespace Flean

/-- Is the number finite (normal, subnormal, or zero)? -/
def FloatBits.isFinite {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  match f.classify with
  | .normal | .subnormal | .zero => true
  | _ => false

/-- Is the number infinite? -/
def FloatBits.isInfinite {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .infinite

/-- Is the number a NaN? -/
def FloatBits.isNaN {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .nan

/-- Is the number a normal number? -/
def FloatBits.isNormal {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .normal

/-- Is the number a subnormal number? -/
def FloatBits.isSubnormal {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .subnormal

/-- Is the number zero? -/
def FloatBits.isZero {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .zero

/-- Is the sign bit set (negative)? -/
def FloatBits.isSignMinus {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.signBit != 0

/-- IEEE 754 totalOrder: A total ordering on all bit patterns.
    Rules:
    - negative NaN < negative infinity < negative finite < negative zero
    - negative zero < positive zero
    - positive zero < positive finite < positive infinity < positive NaN
    Within NaNs, the payload determines the order. -/
def FloatBits.totalOrder {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  let s1 := f1.isSignMinus
  let s2 := f2.isSignMinus
  if s1 != s2 then
    s1 -- Negative is always less than positive
  else
    -- Same sign: compare magnitudes
    let mag1 := f1.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth)
    let mag2 := f2.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth)
    if s1 then
      mag1 ≥ mag2 -- Negative: larger magnitude means smaller value
    else
      mag1 ≤ mag2 -- Positive: larger magnitude means larger value

-- TODO: totalOrderMag requires FloatBits.abs
-- def FloatBits.totalOrderMag {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
--   f1.abs.totalOrder f2.abs

/-! ## Consistency proofs: constructors match predicates -/

theorem FloatBits.classify_posInf (spec : BinarySpec) :
    (FloatBits.posInf spec).classify = .infinite := by
  unfold classify posInf isExpMax isExpZero sigField expField
  have h_exp : BitVec.extractLsb' spec.sigWidth spec.expWidth
      (BitVec.ofNat spec.totalWidth ((2 ^ spec.expWidth - 1) <<< spec.sigWidth))
      = BitVec.allOnes spec.expWidth := by
    ext i
    simp [BitVec.getLsbD_ofNat, Nat.testBit_shiftLeft,
      Nat.testBit_two_pow_sub_one, BinarySpec.totalWidth]
    omega
  have h_sig : BitVec.extractLsb' 0 spec.sigWidth
      (BitVec.ofNat spec.totalWidth ((2 ^ spec.expWidth - 1) <<< spec.sigWidth))
      = 0 := by
    ext i
    simp [BitVec.getLsbD_ofNat, Nat.testBit_shiftLeft, BinarySpec.totalWidth]
    omega
  simp [h_exp, h_sig]

theorem FloatBits.isInfinite_posInf (spec : BinarySpec) :
    (FloatBits.posInf spec).isInfinite = true := by
  simp [isInfinite, classify_posInf]

end Flean
