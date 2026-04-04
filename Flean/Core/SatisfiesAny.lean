import Flean.Core.Representable
import Flean.Core.DoubleRound

/-!
# Flean.Core.SatisfiesAny

The `satisfies_any` predicate: a format admits all valid rounding modes.
This means for any real x, there exist representable numbers both <= x and >= x.

Corresponds to Flocq's `satisfies_any` in `Flocq.Core.Round_pred`.
-/

namespace Flean

/-- A format satisfies_any if for every real x, there exist representable
    numbers below and above x. This is the precondition for all rounding
    functions to be well-defined. -/
def satisfies_any (fmt : FloatFormat) : Prop :=
  ∀ x : ℝ, (∃ z : ℝ, isRepresentable fmt z ∧ z ≤ x) ∧
            (∃ z : ℝ, isRepresentable fmt z ∧ x ≤ z)

/-- Every FloatFormat satisfies_any. This is because roundDN and roundUP
    always produce representable bounds. -/
theorem floatFormat_satisfies_any (fmt : FloatFormat) : satisfies_any fmt := by
  intro x
  exact ⟨⟨roundDN fmt x, roundDN_isRepresentable fmt x, roundDN_le fmt x⟩,
         ⟨roundUP fmt x, roundUP_isRepresentable fmt x, roundUP_ge fmt x⟩⟩

/-- satisfies_any implies roundDN is the greatest representable number <= x. -/
theorem roundDN_is_greatest_le (fmt : FloatFormat) {x z : ℝ}
    (hz : isRepresentable fmt z) (hzx : z ≤ x) :
    z ≤ roundDN fmt x :=
  repr_le_roundDN' hz hzx

/-- satisfies_any implies roundUP is the least representable number >= x. -/
theorem roundUP_is_least_ge (fmt : FloatFormat) {x z : ℝ}
    (hz : isRepresentable fmt z) (hxz : x ≤ z) :
    roundUP fmt x ≤ z :=
  roundUP_le_repr' hz hxz

/-- No representable number lies strictly between roundDN(x) and roundUP(x). -/
theorem no_repr_between_DN_UP (fmt : FloatFormat) {x z : ℝ}
    (hz : isRepresentable fmt z)
    (h1 : roundDN fmt x < z) (h2 : z < roundUP fmt x) :
    False := by
  have h3 : x < z := by
    by_contra h
    exact absurd (repr_le_roundDN' hz (not_lt.mp h)) (not_le.mpr h1)
  have h4 : z < x := by
    by_contra h
    exact absurd (roundUP_le_repr' hz (not_lt.mp h)) (not_le.mpr h2)
  linarith

end Flean
