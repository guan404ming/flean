import Flean.Binary.Defs

namespace Flean

/-- A normal number always has a significand in the range [2^sigWidth, 2^(sigWidth+1) - 1]. -/
theorem FloatBits.normal_significand_range {spec : BinarySpec} (f : FloatBits spec)
    (h : f.classify = .normal) :
    2^spec.sigWidth ≤ f.toRepr.significand ∧ f.toRepr.significand < 2^(spec.sigWidth + 1) := by
  -- Since it's normal, isExpZero is false.
  have h_not_zero : f.isExpZero = false := by
    unfold classify at h
    split_ifs at h with h1 h2
    · cases h
    · rfl
    · cases h
  unfold toRepr; dsimp; rw [h_not_zero]; simp
  -- sigField.toNat < 2^sigWidth
  have h_sig_lt : f.sigField.toNat < 2^spec.sigWidth := f.sigField.toNat_lt
  omega

/-- A subnormal number always has a significand strictly less than 2^sigWidth. -/
theorem FloatBits.subnormal_significand_range {spec : BinarySpec} (f : FloatBits spec)
    (h : f.classify = .subnormal) :
    f.toRepr.significand < 2^spec.sigWidth := by
  have h_zero : f.isExpZero = true := by
    unfold classify at h
    split_ifs at h with h1 h2
    · cases h
    · exact h2
    · cases h
  unfold toRepr; dsimp; rw [h_zero]; simp
  exact f.sigField.toNat_lt

end Flean
