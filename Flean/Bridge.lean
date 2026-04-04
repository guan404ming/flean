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

theorem toReal_roundTZ_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundTZ spec.toFormat f.toReal = f.toReal :=
  roundTZ_repr_fixed spec.toFormat (f.toReal_isRepresentable hfin)

theorem toReal_roundNNE_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundNNE spec.toFormat f.toReal = f.toReal :=
  roundNNE_repr_fixed spec.toFormat (f.toReal_isRepresentable hfin)

theorem toReal_roundDN_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundDN spec.toFormat f.toReal = f.toReal :=
  roundDN_repr_fixed spec.toFormat (f.toReal_isRepresentable hfin)

theorem toReal_roundUP_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundUP spec.toFormat f.toReal = f.toReal :=
  roundUP_repr_fixed spec.toFormat (f.toReal_isRepresentable hfin)

theorem toReal_roundNNA_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    roundNNA spec.toFormat f.toReal = f.toReal :=
  roundNNA_repr_fixed spec.toFormat (f.toReal_isRepresentable hfin)

/-! ## Generic fixed-point via the round dispatcher -/

theorem toReal_round_fixed {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal)
    (mode : RoundingMode) :
    round spec.toFormat mode f.toReal = f.toReal := by
  cases mode with
  | roundTowardZero => exact toReal_roundTZ_fixed f hfin
  | roundTowardPositive => exact toReal_roundUP_fixed f hfin
  | roundTowardNegative => exact toReal_roundDN_fixed f hfin
  | roundNearestTiesToEven => exact toReal_roundNNE_fixed f hfin
  | roundNearestTiesAway => exact toReal_roundNNA_fixed f hfin

/-! ## Representability connection -/

theorem toReal_isRepresentable_format {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    isRepresentable spec.toFormat f.toReal :=
  f.toReal_isRepresentable hfin

end Flean
