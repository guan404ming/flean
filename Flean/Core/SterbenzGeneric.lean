import Flean.Core.GenericFormat
import Flean.Core.ULP

/-!
# Flean.Core.SterbenzGeneric

Generic Sterbenz lemma: if y/2 ≤ x ≤ 2y for generic_format x, y ≥ 0,
then x - y is exactly representable (no rounding error) under any rounding mode.

The existing `sterbenz` in `ULP.lean` is stated for `roundTZ` and `isRepresentable`.
This version uses `generic_format` and proves the result for arbitrary `ZrndFn`,
since the conclusion is that `x - y` is itself in generic_format (hence representable),
making any rounding a no-op.

Corresponds to Flocq's `sterbenz` in `Flocq.Core.Sterbenz`.
-/

namespace Flean

/-- Generic Sterbenz lemma: if y/2 ≤ x ≤ 2y for representable x, y ≥ 0,
    then x - y is in generic_format (hence exactly representable). -/
theorem sterbenz_generic (fmt : FloatFormat) {x y : ℝ}
    (hx : generic_format fmt x) (hy : generic_format fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    generic_format fmt (x - y) := by
  rw [generic_format_iff_roundTZ_fixed]
  rw [generic_format_iff_repr] at hx hy
  exact sterbenz fmt hx hy hx0 hy0 hxy hyx

/-- Generic Sterbenz: any rounding of x - y equals x - y. -/
theorem sterbenz_round_exact (zr : ZrndFn) (fmt : FloatFormat) {x y : ℝ}
    (hx : generic_format fmt x) (hy : generic_format fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundGeneric zr fmt (x - y) = x - y :=
  generic_format_round_fixed zr fmt (sterbenz_generic fmt hx hy hx0 hy0 hxy hyx)

/-- Sterbenz for roundNNE specifically. -/
theorem sterbenz_roundNNE (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundNNE fmt (x - y) = x - y := by
  rw [roundNNE_eq_generic]
  exact sterbenz_round_exact zrndNNE.toZrndFn fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

/-- Sterbenz for roundNNA specifically. -/
theorem sterbenz_roundNNA (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundNNA fmt (x - y) = x - y := by
  rw [roundNNA_eq_generic]
  exact sterbenz_round_exact zrndNNA.toZrndFn fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

/-- Sterbenz for roundUP specifically. -/
theorem sterbenz_roundUP (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundUP fmt (x - y) = x - y := by
  rw [roundUP_eq_generic]
  exact sterbenz_round_exact zrndUP fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

/-- Sterbenz for roundDN specifically. -/
theorem sterbenz_roundDN (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hy : isRepresentable fmt y)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : y ≤ 2 * x) (hyx : x ≤ 2 * y) :
    roundDN fmt (x - y) = x - y := by
  rw [roundDN_eq_generic]
  exact sterbenz_round_exact zrndDN fmt
    (generic_format_of_repr fmt hx) (generic_format_of_repr fmt hy) hx0 hy0 hxy hyx

end Flean
