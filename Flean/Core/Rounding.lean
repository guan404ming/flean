import Flean.Core.Format

/-!
# Flean.Core.Rounding

Definitions of IEEE 754 rounding modes and their abstract properties.
-/

namespace Flean

/-- The five IEEE 754 rounding modes. -/
inductive RoundingMode where
  /-- Round to nearest, ties to even (default). -/
  | roundNearestTiesToEven
  /-- Round to nearest, ties away from zero. -/
  | roundNearestTiesAway
  /-- Round toward positive infinity. -/
  | roundTowardPositive
  /-- Round toward negative infinity. -/
  | roundTowardNegative
  /-- Round toward zero (truncation). -/
  | roundTowardZero
  deriving DecidableEq, Repr

/-- Exponent bias for a given format: β^(p-1). -/
def FloatFormat.bias (fmt : FloatFormat) : Nat :=
  fmt.β ^ (fmt.prec - 1)

end Flean
