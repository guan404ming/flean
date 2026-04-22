import Flean.Arith.Correctness.Core

namespace Flean

private theorem machineEpsilon_le_one (fmt : FloatFormat) : machineEpsilon fmt ≤ 1 := by
  unfold machineEpsilon
  have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
  have hle : 1 - (fmt.prec : ℤ) ≤ 0 := by omega
  calc (fmt.β : ℝ) ^ (1 - (fmt.prec : ℤ))
      ≤ (fmt.β : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ fmt.β_one_lt.le hle
    _ = 1 := zpow_zero _

private theorem maxFinite_nonneg (fmt : FloatFormat) : 0 ≤ maxFinite fmt := by
  unfold maxFinite
  have hpow : 0 ≤ (fmt.β : ℝ) ^ fmt.emax := by
    exact zpow_nonneg (show 0 ≤ (fmt.β : ℝ) by positivity) _
  have htail : 0 ≤ 2 - machineEpsilon fmt := by
    have heps : machineEpsilon fmt ≤ 1 := machineEpsilon_le_one fmt
    linarith
  exact mul_nonneg hpow htail

private theorem overflowFlag_zero_false (fmt : FloatFormat) :
    overflowFlag fmt 0 = false := by
  unfold overflowFlag
  classical
  have hnot : ¬ maxFinite fmt < |(0 : ℝ)| := by
    simpa [abs_zero] using not_lt_of_ge (maxFinite_nonneg fmt)
  exact decide_eq_false_iff_not.mpr hnot

theorem mulBitFlagEquiv_zero_right (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero)
    (hb : b.classify = .zero) :
    (a.mul b mode).flags = mulFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  have hb0 : b.toReal = 0 := by
    unfold FloatBits.toReal
    rw [hb]
  have himpl : (a.mul b mode).flags = {} := by
    rcases ha with ha | ha | ha <;> unfold FloatBits.mul <;> simp [FloatBits.mulSpecial, ha, hb]
  have hspec : mulFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
    rw [mulFlagsSpec_correct, roundedFlagsSpec_correct]
    simp [hb0, mulSpec, round_zero, inexactFlag, underflowFlag, overflowFlag_zero_false]
  simpa [hspec] using himpl

theorem mulBitFlagEquiv_zero_left (spec : BinarySpec) (mode : RoundingMode)
    (a b : FloatBits spec)
    (ha : a.classify = .zero)
    (hb : b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) :
    (a.mul b mode).flags = mulFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  have ha0 : a.toReal = 0 := by
    unfold FloatBits.toReal
    rw [ha]
  have himpl : (a.mul b mode).flags = {} := by
    rcases hb with hb | hb | hb <;> unfold FloatBits.mul <;> simp [FloatBits.mulSpecial, ha, hb]
  have hspec : mulFlagsSpec spec.toFormat mode a.toReal b.toReal = {} := by
    rw [mulFlagsSpec_correct, roundedFlagsSpec_correct]
    simp [ha0, mulSpec, round_zero, inexactFlag, underflowFlag, overflowFlag_zero_false]
  simpa [hspec] using himpl

theorem mulBitFlagEquiv_full (spec : BinarySpec) (mode : RoundingMode) :
    MulBitFlagEquivFinite spec mode →
    ∀ (a b : FloatBits spec),
      (a.classify = .normal ∨ a.classify = .subnormal ∨ a.classify = .zero) →
      (b.classify = .normal ∨ b.classify = .subnormal ∨ b.classify = .zero) →
      (a.mul b mode).flags = mulFlagsSpec spec.toFormat mode a.toReal b.toReal := by
  intro hfinite a b ha hb
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · exact hfinite a b (Or.inl ha) (Or.inl hb)
    · exact hfinite a b (Or.inl ha) (Or.inr hb)
    · exact mulBitFlagEquiv_zero_right spec mode a b (Or.inl ha) hb
  · rcases hb with hb | hb | hb
    · exact hfinite a b (Or.inr ha) (Or.inl hb)
    · exact hfinite a b (Or.inr ha) (Or.inr hb)
    · exact mulBitFlagEquiv_zero_right spec mode a b (Or.inr (Or.inl ha)) hb
  · exact mulBitFlagEquiv_zero_left spec mode a b ha hb

theorem mulBitFlagEquiv_of_mulFiniteFlagsToSpec (spec : BinarySpec) (mode : RoundingMode)
    (hfinite : MulFiniteFlagsToSpec spec mode) :
    MulBitFlagEquiv spec mode := by
  exact mulBitFlagEquiv_full spec mode
    (mulBitFlagEquivFinite_of_mulFiniteFlagsToSpec spec mode hfinite)

theorem mulBitFlagEquiv_of_mulFiniteBranchFlags (spec : BinarySpec) (mode : RoundingMode)
    (hhigh : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlow : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitFlagEquiv spec mode := by
  exact mulBitFlagEquiv_full spec mode
    (mulBitFlagEquivFinite_of_mulFiniteBranchFlags spec mode hhigh hlow)

theorem mulBitEquivAndFlagEquiv_of_mulFiniteObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hval : MulFiniteToSpec spec mode)
    (hflag : MulFiniteFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  exact ⟨
    mulBitEquiv_of_mulFiniteToSpec spec mode hval,
    mulBitFlagEquiv_of_mulFiniteFlagsToSpec spec mode hflag
  ⟩

theorem mulBitEquivAndFlagEquiv_of_mulFiniteExactAndFlagsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hexact : MulFiniteExact spec mode)
    (hflag : MulFiniteFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  have hfinite :=
    mulBitEquivAndFlagEquivFinite_of_mulFiniteExactAndFlagsToSpec
      spec mode hexact hflag
  exact ⟨hfinite.1, mulBitFlagEquiv_full spec mode hfinite.2⟩

theorem mulBitEquivAndFlagEquiv_of_mulFiniteExactAndFlags
    (spec : BinarySpec) (mode : RoundingMode)
    (h : MulFiniteExactAndFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  exact mulBitEquivAndFlagEquiv_of_mulFiniteExactAndFlagsToSpec
    spec mode h.1 h.2

theorem mulBitEquivAndFlagEquiv_of_mulFiniteBranchObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hhighVal : MulFiniteHighBranchToSpec spec mode)
    (hlowVal : MulFiniteLowBranchToSpec spec mode)
    (hhighFlag : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  exact ⟨
    mulBitEquiv_of_mulFiniteBranches spec mode hhighVal hlowVal,
    mulBitFlagEquiv_of_mulFiniteBranchFlags spec mode hhighFlag hlowFlag
  ⟩

theorem mulBitEquivAndFlagEquiv_of_mulFiniteBranchObligationsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (hbranch : MulFiniteBranchObligationsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  have hfinite := mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchObligationsToSpec
    spec mode hbranch
  exact ⟨hfinite.1, mulBitFlagEquiv_full spec mode hfinite.2⟩

theorem mulBitEquivAndFlagEquiv_of_mulFiniteBranchExactAndFlagObligations
    (spec : BinarySpec) (mode : RoundingMode)
    (hhighExact : MulFiniteHighBranchExact spec mode)
    (hlowExact : MulFiniteLowBranchExact spec mode)
    (hhighFlag : MulFiniteHighBranchFlagsToSpec spec mode)
    (hlowFlag : MulFiniteLowBranchFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  have hfinite :=
    mulBitEquivAndFlagEquivFinite_of_mulFiniteBranchExactAndFlagObligations
      spec mode hhighExact hlowExact hhighFlag hlowFlag
  exact ⟨hfinite.1, mulBitFlagEquiv_full spec mode hfinite.2⟩

theorem mulBitEquivAndFlagEquiv_of_mulFiniteExactAndFlags_viaBranchObligationsToSpec
    (spec : BinarySpec) (mode : RoundingMode)
    (h : MulFiniteExactAndFlagsToSpec spec mode) :
    MulBitEquiv spec mode ∧ MulBitFlagEquiv spec mode := by
  exact mulBitEquivAndFlagEquiv_of_mulFiniteBranchObligationsToSpec spec mode
    (mulFiniteBranchObligationsToSpec_of_mulFiniteExactAndFlags spec mode h)

theorem mulBitFlagEquiv (spec : BinarySpec) (mode : RoundingMode) :
    MulBitFlagEquivFinite spec mode →
    MulBitFlagEquiv spec mode :=
  mulBitFlagEquiv_full spec mode

end Flean
