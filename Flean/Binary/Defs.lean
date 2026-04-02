import Flean.Core.Format

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
  /-- Exponent width must be positive. -/
  hExp : expWidth ≥ 1
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

end Flean
