import Flean.Core.GenericFormat
import Flean.Core.DoubleRound

/-!
# Flean.Core.DoubleRoundGeneric

Additional double rounding theorems expressed via `roundGeneric`.

The core generic directed proofs (`double_roundGeneric_of_directedDN/UP`) and
their concrete specializations (`double_roundDN/UP/TZ`) live in `DoubleRound.lean`.
This file provides roundGeneric-stated variants and NNE specializations.
-/

namespace Flean

/-! ## Double rounding when intermediate is representable in coarse format -/

/-- If roundGeneric zr fmt2 x is representable in fmt1, then
    roundGeneric zr fmt1 (roundGeneric zr fmt2 x) = roundGeneric zr fmt2 x. -/
theorem double_round_repr_intermediate (zr : ZrndFn) {fmt1 fmt2 : FloatFormat}
    {x : ℝ} (h : isRepresentable fmt1 (roundGeneric zr fmt2 x)) :
    roundGeneric zr fmt1 (roundGeneric zr fmt2 x) = roundGeneric zr fmt2 x :=
  roundGeneric_repr_fixed zr fmt1 h

/-! ## roundGeneric-stated variants -/

theorem double_roundGeneric_DN {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundGeneric zrndDN fmt1 (roundGeneric zrndDN fmt2 x) = roundGeneric zrndDN fmt1 x := by
  simp only [← roundDN_eq_generic]; exact double_roundDN href x

theorem double_roundGeneric_UP {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundGeneric zrndUP fmt1 (roundGeneric zrndUP fmt2 x) = roundGeneric zrndUP fmt1 x := by
  simp only [← roundUP_eq_generic]; exact double_roundUP href x

theorem double_roundGeneric_TZ {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundGeneric zrndTZ fmt1 (roundGeneric zrndTZ fmt2 x) = roundGeneric zrndTZ fmt1 x := by
  simp only [← roundTZ_eq_generic]; exact double_roundTZ href x

/-! ## NNE specializations -/

theorem double_roundGeneric_NNE_same_cexp {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2) {x : ℝ}
    (hcexp : cexp fmt1 x = cexp fmt2 x) :
    roundGeneric zrndNNE.toZrndFn fmt1 (roundGeneric zrndNNE.toZrndFn fmt2 x) =
    roundGeneric zrndNNE.toZrndFn fmt1 x := by
  simp only [← roundNNE_eq_generic]; exact double_roundNNE_same_cexp href hcexp

theorem double_roundGeneric_NNE_of_repr {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2) {x : ℝ}
    (hx : isRepresentable fmt1 x) :
    roundGeneric zrndNNE.toZrndFn fmt1 (roundGeneric zrndNNE.toZrndFn fmt2 x) =
    roundGeneric zrndNNE.toZrndFn fmt1 x := by
  simp only [← roundNNE_eq_generic]; exact double_roundNNE_of_repr href hx

end Flean
