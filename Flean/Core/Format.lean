/-!
# Flean.Core.Format

Parameterized floating-point format definitions following IEEE 754.
A format is characterized by radix β, precision p, and exponent range [emin, emax].
-/

namespace Flean

/-- A floating-point format parameterized by precision and exponent bounds. -/
structure FloatFormat where
  /-- Radix (base), typically 2 for binary formats. -/
  β : Nat
  /-- Precision: number of significand digits (including implicit leading bit). -/
  prec : Nat
  /-- Minimum exponent. -/
  emin : Int
  /-- Maximum exponent. -/
  emax : Int
  /-- The radix must be at least 2. -/
  hβ : β ≥ 2
  /-- Precision must be positive. -/
  hprec : prec ≥ 1
  /-- Exponent range must be valid. -/
  hexp : emin ≤ emax

/-- IEEE 754 binary16 (half precision): 1 sign + 5 exponent + 10 significand bits. -/
def binary16 : FloatFormat where
  β := 2
  prec := 11
  emin := -14
  emax := 15
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- bfloat16 (brain floating point): 1 sign + 8 exponent + 7 significand bits. -/
def bfloat16 : FloatFormat where
  β := 2
  prec := 8
  emin := -126
  emax := 127
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- IEEE 754 binary32 (single precision): 1 sign + 8 exponent + 23 significand bits. -/
def binary32 : FloatFormat where
  β := 2
  prec := 24
  emin := -126
  emax := 127
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- IEEE 754 binary64 (double precision): 1 sign + 11 exponent + 52 significand bits. -/
def binary64 : FloatFormat where
  β := 2
  prec := 53
  emin := -1022
  emax := 1023
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- IEEE 754 binary128 (quad precision): 1 sign + 15 exponent + 112 significand bits. -/
def binary128 : FloatFormat where
  β := 2
  prec := 113
  emin := -16382
  emax := 16383
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- FP4 E2M1 in the IEEE-style view used by `BinarySpec.toFormat`:
    1 sign + 2 exponent + 1 significand bit, with `emin = -1` and `emax = 1`. -/
def binary4_e2m1 : FloatFormat where
  β := 2
  prec := 2
  emin := -1
  emax := 1
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- IEEE 754 decimal32: radix-10 with precision 7 and exponent range [-95, 96]. -/
def decimal32 : FloatFormat where
  β := 10
  prec := 7
  emin := -95
  emax := 96
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- IEEE 754 decimal64: radix-10 with precision 16 and exponent range [-383, 384]. -/
def decimal64 : FloatFormat where
  β := 10
  prec := 16
  emin := -383
  emax := 384
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- IEEE 754 decimal128: radix-10 with precision 34 and exponent range [-6143, 6144]. -/
def decimal128 : FloatFormat where
  β := 10
  prec := 34
  emin := -6143
  emax := 6144
  hβ := by omega
  hprec := by omega
  hexp := by omega

/-- Classification of floating-point number categories per IEEE 754. -/
inductive FloatClass where
  | normal
  | subnormal
  | zero
  | infinite
  | nan
  deriving DecidableEq, Repr

/-- Sign representation. -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

def Sign.toInt : Sign → Int
  | .pos => 1
  | .neg => -1

/-- A generic floating-point number in a given format.
    Represents the triple (sign, exponent, significand) before bit packing. -/
structure FloatRepr (fmt : FloatFormat) where
  /-- Sign bit. -/
  sign : Sign
  /-- Biased exponent as a natural number. -/
  exponent : Nat
  /-- Significand (mantissa) as a natural number. -/
  significand : Nat

end Flean
