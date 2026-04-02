import Flean.Core.Format
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

/-!
# Flean.Core.Rounding

IEEE 754 rounding modes, rounding functions on ℝ, and their properties.
Now backed by Mathlib's real number library.
-/

namespace Flean

/-- The five IEEE 754 rounding modes. -/
inductive RoundingMode where
  | roundNearestTiesToEven
  | roundNearestTiesAway
  | roundTowardPositive
  | roundTowardNegative
  | roundTowardZero
  deriving DecidableEq, Repr

/-- The set of representable floating-point numbers in a given format.
    A real number x is representable if x = m * β^e where
    |m| < β^p and emin <= e. -/
def isRepresentable (fmt : FloatFormat) (x : ℝ) : Prop :=
  ∃ (m : ℤ) (e : ℤ),
    x = (m : ℝ) * (fmt.β : ℝ) ^ (e : ℤ) ∧
    |m| < (fmt.β ^ fmt.prec : ℤ) ∧
    fmt.emin ≤ e

/-- Machine epsilon: β^(1-p), the relative spacing at 1. -/
noncomputable def machineEpsilon (fmt : FloatFormat) : ℝ :=
  (fmt.β : ℝ) ^ (1 - (fmt.prec : ℤ))

/-- The smallest positive normal number: β^emin. -/
noncomputable def minNormal (fmt : FloatFormat) : ℝ :=
  (fmt.β : ℝ) ^ fmt.emin

/-- The largest finite representable number. -/
noncomputable def maxFinite (fmt : FloatFormat) : ℝ :=
  (fmt.β : ℝ) ^ fmt.emax * (2 - machineEpsilon fmt)

/-- A rounding function maps any real to a representable float. -/
structure RoundingFn (fmt : FloatFormat) where
  /-- The rounding function. -/
  round : ℝ → ℝ
  /-- The result is always representable. -/
  rounds_to_repr : ∀ (x : ℝ), isRepresentable fmt (round x)
  /-- Rounding is idempotent: R(R(x)) = R(x). -/
  idempotent : ∀ (x : ℝ), round (round x) = round x
  /-- Rounding is monotone. -/
  monotone : Monotone round

end Flean
