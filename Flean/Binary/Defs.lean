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
  emin := 1 - (spec.bias : Int)
  emax := (spec.bias : Int)
  hβ := by omega
  hprec := by omega
  hexp := by
    suffices h : 1 ≤ (spec.bias : Int) by linarith
    have he : 1 ≤ spec.expWidth - 1 := by have := spec.hExp; omega
    have hp : 2 ≤ 2 ^ (spec.expWidth - 1) :=
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (spec.expWidth - 1) := Nat.pow_le_pow_right (by omega : 0 < 2) he
    exact_mod_cast show 1 ≤ spec.bias from by unfold bias; omega

/-- Decode a finite floating-point bit pattern into (sign, biased_exp, significand). -/
def FloatBits.toRepr {spec : BinarySpec} (f : FloatBits spec) : FloatRepr spec.toFormat where
  sign := f.sign
  exponent := f.expField.toNat
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

end Flean
