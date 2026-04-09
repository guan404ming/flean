import Flean.Binary.Properties
import Flean.Core.NearestRound

/-!
# Flean.Bridge

Bridge between bit-level (FloatBits) and real-valued rounding models.

Key theorems: the real value of a finite FloatBits is a fixed point of
every rounding function on the corresponding FloatFormat.
-/

namespace Flean

/-! ## Fixed-point theorems: rounding fixes FloatBits.toReal -/

private theorem toReal_round_fixed_mode {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal)
    (mode : RoundingMode) :
    round spec.toFormat mode f.toReal = f.toReal := by
  have hrepr : isRepresentable spec.toFormat f.toReal := f.toReal_isRepresentable hfin
  unfold round
  cases mode with
  | roundTowardZero => exact roundTZ_repr_fixed spec.toFormat hrepr
  | roundTowardPositive => exact roundUP_repr_fixed spec.toFormat hrepr
  | roundTowardNegative => exact roundDN_repr_fixed spec.toFormat hrepr
  | roundNearestTiesToEven => exact roundNNE_repr_fixed spec.toFormat hrepr
  | roundNearestTiesAway => exact roundNNA_repr_fixed spec.toFormat hrepr

theorem toReal_roundTZ_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundTZ spec.toFormat f.toReal = f.toReal := by
  simpa using toReal_round_fixed_mode f hfin .roundTowardZero

theorem toReal_roundNNE_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundNNE spec.toFormat f.toReal = f.toReal := by
  simpa using toReal_round_fixed_mode f hfin .roundNearestTiesToEven

theorem toReal_roundDN_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundDN spec.toFormat f.toReal = f.toReal := by
  simpa using toReal_round_fixed_mode f hfin .roundTowardNegative

theorem toReal_roundUP_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundUP spec.toFormat f.toReal = f.toReal := by
  simpa using toReal_round_fixed_mode f hfin .roundTowardPositive

theorem toReal_roundNNA_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundNNA spec.toFormat f.toReal = f.toReal := by
  simpa using toReal_round_fixed_mode f hfin .roundNearestTiesAway

/-! ## Generic fixed-point via the round dispatcher -/

theorem toReal_round_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal)
    (mode : RoundingMode) :
    round spec.toFormat mode f.toReal = f.toReal :=
  toReal_round_fixed_mode f hfin mode

/-! ## Representability connection -/

theorem toReal_isRepresentable_format {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    isRepresentable spec.toFormat f.toReal :=
  f.toReal_isRepresentable hfin

end Flean
