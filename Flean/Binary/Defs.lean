import Flean.Core.Format
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Flean.Binary.Defs

Bit-level representation of IEEE 754 floating-point numbers using Lean 4's `BitVec`.
Provides packing/unpacking between the triple (sign, exponent, significand) and raw bits.
-/

namespace Flean

/-- Bit-width specification for a concrete IEEE 754 binary format. -/
structure BinarySpec where
  /-- Width of the exponent field in bits. -/
  expWidth : Nat
  /-- Width of the trailing significand field in bits (excludes implicit bit). -/
  sigWidth : Nat
  /-- Exponent width must be at least 2 for IEEE 754 compatibility. -/
  hExp : expWidth ≥ 2
  /-- Significand width must be positive. -/
  hSig : sigWidth ≥ 1

/-- Total bit width: 1 (sign) + expWidth + sigWidth. -/
def BinarySpec.totalWidth (spec : BinarySpec) : Nat :=
  1 + spec.expWidth + spec.sigWidth

/-- Exponent bias: 2^(expWidth-1) - 1. -/
def BinarySpec.bias (spec : BinarySpec) : Nat :=
  2 ^ (spec.expWidth - 1) - 1

/-- binary16 spec: 5-bit exponent, 10-bit significand. -/
def binarySpec16 : BinarySpec where
  expWidth := 5
  sigWidth := 10
  hExp := by omega
  hSig := by omega

/-- binary32 spec: 8-bit exponent, 23-bit significand. -/
def binarySpec32 : BinarySpec where
  expWidth := 8
  sigWidth := 23
  hExp := by omega
  hSig := by omega

/-- binary64 spec: 11-bit exponent, 52-bit significand. -/
def binarySpec64 : BinarySpec where
  expWidth := 11
  sigWidth := 52
  hExp := by omega
  hSig := by omega

/-- binary128 spec: 15-bit exponent, 112-bit significand. -/
def binarySpec128 : BinarySpec where
  expWidth := 15
  sigWidth := 112
  hExp := by omega
  hSig := by omega

/-- OCP FP8 E4M3 spec: 4-bit exponent, 3-bit significand, bias 7.
    Note: the `.toFormat` view uses IEEE-style emax = bias = 7, which under-counts the
    OCP FN convention (emax = 8, max finite = 448) by one. Underflow analysis at the
    low end is unaffected: smallest representable = 2^(-9) = 1/512. -/
def binarySpec8_e4m3 : BinarySpec where
  expWidth := 4
  sigWidth := 3
  hExp := by omega
  hSig := by omega

/-- OCP FP8 E5M2 spec: 5-bit exponent, 2-bit significand, bias 15.
    IEEE-style semantics: emax = 15, max finite = 57344, smallest subnormal = 2^(-16). -/
def binarySpec8_e5m2 : BinarySpec where
  expWidth := 5
  sigWidth := 2
  hExp := by omega
  hSig := by omega

/-- FP4 E2M1 spec: 2-bit exponent, 1-bit significand, bias 1.
    Used by NVIDIA Blackwell / MXFP4 / OCP MX for low-precision attention and GEMM.
    IEEE-style `.toFormat` view: emin = -1, minNormal = 2^(-1), emax = 1. The OCP
    FN convention extends emax by one (max finite = 6 instead of 3); underflow
    analysis is identical. -/
def binarySpec4_e2m1 : BinarySpec where
  expWidth := 2
  sigWidth := 1
  hExp := by omega
  hSig := by omega

/-- A packed IEEE 754 floating-point value as a bit vector. -/
structure FloatBits (spec : BinarySpec) where
  /-- The raw bit representation. -/
  bits : BitVec spec.totalWidth

/-- Extract the sign bit (MSB). -/
def FloatBits.signBit {spec : BinarySpec} (f : FloatBits spec) : BitVec 1 :=
  f.bits.extractLsb' (spec.expWidth + spec.sigWidth) 1

/-- Extract the exponent field. -/
def FloatBits.expField {spec : BinarySpec} (f : FloatBits spec) : BitVec spec.expWidth :=
  f.bits.extractLsb' spec.sigWidth spec.expWidth

/-- Extract the trailing significand field. -/
def FloatBits.sigField {spec : BinarySpec} (f : FloatBits spec) : BitVec spec.sigWidth :=
  f.bits.extractLsb' 0 spec.sigWidth

/-- Check if the exponent field is all zeros. -/
def FloatBits.isExpZero {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.expField == 0

/-- Check if the exponent field is all ones. -/
def FloatBits.isExpMax {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.expField == BitVec.allOnes spec.expWidth

/-- Classify a floating-point bit pattern. -/
def FloatBits.classify {spec : BinarySpec} (f : FloatBits spec) : FloatClass :=
  if f.isExpMax then
    if f.sigField == 0 then .infinite else .nan
  else if f.isExpZero then
    if f.sigField == 0 then .zero else .subnormal
  else
    .normal

/-- Pack a triple into bits. -/
def FloatBits.fromFields {spec : BinarySpec} (s : BitVec 1) (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) : FloatBits spec where
  bits := s ++ e ++ m

/-- Get the sign as a Flean.Sign. -/
def FloatBits.sign {spec : BinarySpec} (f : FloatBits spec) : Sign :=
  if f.signBit == 0 then .pos else .neg

/-- Is the sign bit set (negative)? -/
def FloatBits.isNeg {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.signBit != 0

/-- Negate a FloatBits by flipping the sign bit. -/
def FloatBits.negate {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  let mask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  ⟨f.bits ^^^ mask⟩

/-- Absolute value: clear the sign bit. -/
def FloatBits.abs {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  let mask := BitVec.ofNat spec.totalWidth (1 <<< (spec.expWidth + spec.sigWidth))
  ⟨f.bits &&& (~~~ mask)⟩

/-- Extract the extended significand including the implicit bit. -/
def FloatBits.getExtendedSignificand {spec : BinarySpec} (f : FloatBits spec) :
    (BitVec (1 + spec.sigWidth)) × Nat :=
  if f.isExpZero then
    (BitVec.ofNat 1 0 ++ f.sigField, 1)
  else
    (BitVec.ofNat 1 1 ++ f.sigField, f.expField.toNat)

/-- Convert a specification to its corresponding core format. -/
def BinarySpec.toFormat (spec : BinarySpec) : FloatFormat where
  β := 2
  prec := spec.sigWidth + 1
  emin := 1 - (spec.bias : Int) - spec.sigWidth
  emax := (spec.bias : Int)
  hβ := by omega
  hprec := by omega
  hexp := by
    have he : 1 ≤ spec.expWidth - 1 := by have := spec.hExp; omega
    have hp : 2 ≤ 2 ^ (spec.expWidth - 1) :=
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (spec.expWidth - 1) := Nat.pow_le_pow_right (by omega : 0 < 2) he
    have hbias : 1 ≤ (spec.bias : Int) := by exact_mod_cast show 1 ≤ spec.bias from by unfold bias; omega
    have := spec.hSig
    omega

@[simp] theorem binarySpec4_e2m1_toFormat :
    binarySpec4_e2m1.toFormat = binary4_e2m1 := by
  rfl

/-- Decode a finite floating-point bit pattern into (sign, biased_exp, significand).
    For subnormals, IEEE 754 uses the minimum exponent (biased value 1),
    not the encoded exponent field value 0. -/
def FloatBits.toRepr {spec : BinarySpec} (f : FloatBits spec) : FloatRepr spec.toFormat where
  sign := f.sign
  exponent := if f.isExpZero then 1 else f.expField.toNat
  significand :=
    if f.isExpZero then
      f.sigField.toNat
    else
      f.sigField.toNat + 2^spec.sigWidth

/-- The value of a floating-point number as a real number (for finite values). -/
noncomputable def FloatBits.toReal {spec : BinarySpec} (f : FloatBits spec) : ℝ :=
  match f.classify with
  | .zero => 0
  | .infinite => 0
  | .nan => 0
  | .normal | .subnormal =>
      let repr := f.toRepr
      let s := repr.sign.toInt
      let e := (repr.exponent : Int) - (spec.bias : Int)
      let m := (repr.significand : Int)
      let p := (spec.sigWidth : Int)
      (s : ℝ) * (m : ℝ) * (2 : ℝ) ^ (e - p)

/-- A simple IEEE-style denotation that preserves NaN class, infinities, and the sign of zero. -/
inductive IEEEValue where
  | nan (sign : Sign) (signaling : Bool) (payload : Nat)
  | infinite (sign : Sign)
  | finite (x : ℝ) (zeroSign : Option Sign := none)

/-- Raw NaN payload bits. Returns `0` for non-NaN values. -/
def FloatBits.nanPayload {spec : BinarySpec} (f : FloatBits spec) : BitVec spec.sigWidth :=
  f.sigField

/-- The quiet/signaling discriminator bit within a NaN payload. -/
def FloatBits.nanQuietBit {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  if spec.sigWidth = 0 then
    false
  else
    f.sigField.getLsbD (spec.sigWidth - 1)

/-- Predicate for quiet NaNs. -/
def FloatBits.isQuietNaN {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .nan && f.nanQuietBit

/-- Predicate for signaling NaNs. -/
def FloatBits.isSignalingNaN {spec : BinarySpec} (f : FloatBits spec) : Bool :=
  f.classify == .nan && !f.nanQuietBit

/-- Canonicalize a NaN into its quiet form while preserving sign and payload bits. -/
def FloatBits.quietedNaN {spec : BinarySpec} (f : FloatBits spec) : FloatBits spec :=
  let quietMask := BitVec.ofNat spec.sigWidth (1 <<< (spec.sigWidth - 1))
  FloatBits.fromFields f.signBit (BitVec.allOnes spec.expWidth) (f.sigField ||| quietMask)

/-- Full IEEE-style denotation for a packed floating-point value. -/
noncomputable def FloatBits.toIEEEValue {spec : BinarySpec} (f : FloatBits spec) : IEEEValue :=
  match f.classify with
  | .nan => .nan f.sign f.isSignalingNaN f.nanPayload.toNat
  | .infinite => .infinite f.sign
  | .zero => .finite 0 (some f.sign)
  | .normal | .subnormal => .finite f.toReal

/-! ## Special value constructors -/

/-- Positive zero: sign=0, exp=0, sig=0. -/
def FloatBits.posZero (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields 0 0 0

/-- Negative zero: sign=1, exp=0, sig=0. -/
def FloatBits.negZero (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields (BitVec.ofNat 1 1) 0 0

/-- Positive infinity: sign=0, exp=all ones, sig=0. -/
def FloatBits.posInf (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields 0 (BitVec.allOnes spec.expWidth) 0

/-- Negative infinity: sign=1, exp=all ones, sig=0. -/
def FloatBits.negInf (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields (BitVec.ofNat 1 1) (BitVec.allOnes spec.expWidth) 0

/-- Canonical quiet NaN: sign=0, exp=all ones, sig MSB=1, rest=0. -/
def FloatBits.quietNaN (spec : BinarySpec) : FloatBits spec :=
  let qBit := BitVec.ofNat spec.sigWidth (1 <<< (spec.sigWidth - 1))
  FloatBits.fromFields 0 (BitVec.allOnes spec.expWidth) qBit

/-- Canonical signaling NaN: sign=0, exp=all ones, payload non-zero with quiet bit cleared. -/
def FloatBits.signalingNaN (spec : BinarySpec) : FloatBits spec :=
  let payload := BitVec.ofNat spec.sigWidth 1
  FloatBits.fromFields 0 (BitVec.allOnes spec.expWidth) payload

/-- Maximum finite positive value: sign=0, exp=max-1, sig=all ones. -/
def FloatBits.maxFinite (spec : BinarySpec) : FloatBits spec :=
  let expMaxMinus1 := BitVec.ofNat spec.expWidth (2 ^ spec.expWidth - 2)
  let sigAllOnes := BitVec.allOnes spec.sigWidth
  FloatBits.fromFields 0 expMaxMinus1 sigAllOnes

end Flean
