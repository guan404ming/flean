import Flean.Binary.Defs

namespace Flean

/-! ## fromFields round-trip lemmas -/

@[simp]
theorem FloatBits.fromFields_sigField {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) :
    (FloatBits.fromFields s e m).sigField = m := by
  unfold fromFields sigField
  exact BitVec.extractLsb'_append_eq_right

@[simp]
theorem FloatBits.fromFields_expField {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) :
    (FloatBits.fromFields s e m).expField = e := by
  unfold fromFields expField
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  change @BitVec.getLsbD (1 + spec.expWidth + spec.sigWidth) _ _ = _
  rw [@BitVec.getLsbD_append (1 + spec.expWidth) spec.sigWidth,
    if_neg (by omega : ¬(spec.sigWidth + i < spec.sigWidth)),
    show spec.sigWidth + i - spec.sigWidth = i from by omega,
    BitVec.getLsbD_append, if_pos hi]

@[simp]
theorem FloatBits.fromFields_signBit {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) :
    (FloatBits.fromFields s e m).signBit = s := by
  unfold fromFields signBit
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp only [BitVec.getLsbD_extractLsb', show (0 : Nat) < 1 from by omega,
    decide_true, Bool.true_and]
  change @BitVec.getLsbD (1 + spec.expWidth + spec.sigWidth) _ _ = _
  rw [@BitVec.getLsbD_append (1 + spec.expWidth) spec.sigWidth,
    if_neg (by omega : ¬(spec.expWidth + spec.sigWidth + 0 < spec.sigWidth)),
    show spec.expWidth + spec.sigWidth + 0 - spec.sigWidth = spec.expWidth from by omega,
    BitVec.getLsbD_append, if_neg (by omega : ¬(spec.expWidth < spec.expWidth)),
    show spec.expWidth - spec.expWidth = 0 from by omega]

@[simp]
theorem FloatBits.fromFields_isExpZero {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) :
    (FloatBits.fromFields s e m).isExpZero = (e == 0) := by
  simp [isExpZero]

@[simp]
theorem FloatBits.fromFields_isExpMax {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) :
    (FloatBits.fromFields s e m).isExpMax = (e == BitVec.allOnes spec.expWidth) := by
  simp [isExpMax]

@[simp]
theorem FloatBits.fromFields_isNeg {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth) :
    (FloatBits.fromFields s e m).isNeg = (s != 0) := by
  simp [isNeg]

theorem FloatBits.fromFields_classify_normal {spec : BinarySpec} (s : BitVec 1)
    (e : BitVec spec.expWidth) (m : BitVec spec.sigWidth)
    (he_nz : e ≠ 0) (he_nmax : e ≠ BitVec.allOnes spec.expWidth) :
    (FloatBits.fromFields s e m).classify = .normal := by
  unfold classify; simp only [fromFields_isExpMax, fromFields_isExpZero, fromFields_sigField]
  rw [show (e == BitVec.allOnes spec.expWidth) = false from beq_eq_false_iff_ne.mpr he_nmax,
      show (e == (0 : BitVec spec.expWidth)) = false from beq_eq_false_iff_ne.mpr he_nz]
  simp

/-! ## Significand range -/

theorem FloatBits.normal_significand_range {spec : BinarySpec} (f : FloatBits spec)
    (h : f.classify = .normal) :
    2^spec.sigWidth ≤ f.toRepr.significand ∧ f.toRepr.significand < 2^(spec.sigWidth + 1) := by
  have h_not_zero : f.isExpZero = false := by
    by_contra h_abs
    push Not at h_abs
    have : f.isExpZero = true := by
      rcases Bool.eq_false_or_eq_true f.isExpZero with h | h <;> simp_all
    unfold classify at h; simp [this] at h
    split_ifs at h
  unfold toRepr; dsimp; rw [h_not_zero]; simp
  have := f.sigField.isLt
  omega

theorem FloatBits.subnormal_significand_range {spec : BinarySpec} (f : FloatBits spec)
    (h : f.classify = .subnormal) :
    f.toRepr.significand < 2^spec.sigWidth := by
  have h_zero : f.isExpZero = true := by
    unfold classify at h
    split_ifs at h; all_goals simp_all
  unfold toRepr; dsimp; rw [h_zero]; simp
  exact f.sigField.isLt

end Flean
