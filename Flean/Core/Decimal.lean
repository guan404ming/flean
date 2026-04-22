import Flean.Core.RoundProps

/-!
# Flean.Core.Decimal

Decimal-oriented core abstractions layered on top of `FloatFormat`.
-/

namespace Flean

/-- Predicate: a `FloatFormat` is decimal (radix 10). -/
def isDecimalFormat (fmt : FloatFormat) : Prop :=
  fmt.β = 10

theorem decimal32_isDecimalFormat : isDecimalFormat decimal32 := by
  simp [isDecimalFormat, decimal32]

theorem decimal64_isDecimalFormat : isDecimalFormat decimal64 := by
  simp [isDecimalFormat, decimal64]

theorem decimal128_isDecimalFormat : isDecimalFormat decimal128 := by
  simp [isDecimalFormat, decimal128]

/-- Finite decimal scientific form constrained by a `FloatFormat`.
    `coeff` stores significand digits without a radix point. -/
structure DecimalFinite (fmt : FloatFormat) where
  sign : Sign
  coeff : Nat
  exp : Int
  hcoeff : coeff < 10 ^ fmt.prec
  hExpLo : fmt.emin ≤ exp
  hExpHi : exp ≤ fmt.emax

/-- Real denotation of a finite decimal value. -/
noncomputable def DecimalFinite.toReal {fmt : FloatFormat} (d : DecimalFinite fmt) : ℝ :=
  (d.sign.toInt : ℝ) * (d.coeff : ℝ) * (10 : ℝ) ^ d.exp

/-- Negation in decimal scientific form. -/
def DecimalFinite.negate {fmt : FloatFormat} (d : DecimalFinite fmt) : DecimalFinite fmt :=
  { d with sign := if d.sign = .pos then .neg else .pos }

/-- Absolute value in decimal scientific form. -/
def DecimalFinite.abs {fmt : FloatFormat} (d : DecimalFinite fmt) : DecimalFinite fmt :=
  { d with sign := .pos }

/-- Shift decimal exponent when new exponent bounds are provided. -/
def DecimalFinite.scaleExp {fmt : FloatFormat} (d : DecimalFinite fmt) (k : Int)
    (hLo : fmt.emin ≤ d.exp + k) (hHi : d.exp + k ≤ fmt.emax) : DecimalFinite fmt :=
  { sign := d.sign
    coeff := d.coeff
    exp := d.exp + k
    hcoeff := d.hcoeff
    hExpLo := hLo
    hExpHi := hHi }

/-- Round a real directly using decimal-format parameters. -/
noncomputable def roundToDecimal (fmt : FloatFormat) (mode : RoundingMode) (x : ℝ) : ℝ :=
  round fmt mode x

theorem roundToDecimal_eq_round (fmt : FloatFormat) (mode : RoundingMode) (x : ℝ) :
    roundToDecimal fmt mode x = round fmt mode x := rfl

end Flean
