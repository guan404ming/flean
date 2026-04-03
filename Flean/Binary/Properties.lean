import Flean.Binary.Defs
import Flean.Core.Rounding

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

/-! ## Bridge: toReal is representable -/

/-- The real value of any finite non-zero FloatBits is representable in its format. -/
theorem FloatBits.toReal_isRepresentable {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    isRepresentable spec.toFormat f.toReal := by
  set fmt := spec.toFormat
  -- Unfold toReal for normal/subnormal
  have htoReal : f.toReal = (f.toRepr.sign.toInt : ℝ) * (f.toRepr.significand : ℝ) *
      (2 : ℝ) ^ ((f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth) := by
    simp only [FloatBits.toReal]
    rcases hfin with h | h <;> (rw [h]; norm_cast)
  -- Set up the mantissa and exponent
  set s := f.toRepr.sign.toInt
  set sig := (f.toRepr.significand : ℤ)
  set e := (f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - (spec.sigWidth : ℤ)
  -- Rewrite as m * β^e
  have hval : f.toReal = (s * sig : ℤ) * (2 : ℝ) ^ e := by
    rw [htoReal]; push_cast; norm_cast
  -- Sign has absolute value 1
  have hs_abs : |s| = 1 := by
    simp only [s]; cases f.toRepr.sign <;> simp [Sign.toInt]
  -- |m| < β^prec = 2^(sigWidth + 1)
  have hm : |s * sig| < (fmt.β ^ fmt.prec : ℤ) := by
    show |s * sig| < (2 : ℤ) ^ (spec.sigWidth + 1)
    rw [abs_mul, hs_abs, one_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    rcases hfin with h | h
    · exact_mod_cast (f.normal_significand_range h).2
    · have h1 := f.subnormal_significand_range h
      have h2 := spec.hSig
      exact_mod_cast show f.toRepr.significand < 2 ^ (spec.sigWidth + 1) by omega
  -- emin ≤ e: need 1 ≤ biased exponent
  have he : fmt.emin ≤ e := by
    show (1 : ℤ) - (spec.bias : ℤ) - spec.sigWidth ≤
        (f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth
    suffices h : 1 ≤ (f.toRepr.exponent : ℤ) by omega
    rcases hfin with h | h
    · -- Normal: expField ≠ 0, so exponent = expField.toNat ≥ 1
      have h_nz : f.isExpZero = false := by
        by_contra hb
        simp only [Bool.not_eq_false] at hb
        unfold classify at h
        simp only [hb, ite_true] at h
        split_ifs at h
      unfold toRepr; simp [h_nz]
      have : f.expField ≠ 0 := by intro hab; simp [isExpZero, hab] at h_nz
      exact_mod_cast BitVec.toNat_pos_of_ne_zero this
    · -- Subnormal: exponent = 1 by definition
      have h_z : f.isExpZero = true := by
        unfold classify at h; split_ifs at h; simp_all
      unfold toRepr; simp [h_z]
  refine ⟨s * sig, e, ?_, hm, he⟩
  rw [hval]
  simp only [fmt, BinarySpec.toFormat]
  push_cast; rfl

/-! ## Bounded representability for bit-level bridge -/

/-- A real number is bit-representable in a BinarySpec if it has a decomposition
    with mantissa and exponent fitting in the bit encoding.
    This is `isRepresentable` plus an upper bound on the exponent. -/
def isBitRepresentable (spec : BinarySpec) (x : ℝ) : Prop :=
  ∃ (m : ℤ) (e : ℤ),
    x = (m : ℝ) * (2 : ℝ) ^ e ∧
    |m| < (2 : ℤ) ^ (spec.sigWidth + 1) ∧
    spec.toFormat.emin ≤ e ∧
    e ≤ (spec.bias : ℤ) - spec.sigWidth ∧
    ((2 : ℤ) ^ spec.sigWidth ≤ |m| ∨ e = spec.toFormat.emin)

theorem isBitRepresentable_isRepresentable {spec : BinarySpec} {x : ℝ}
    (hx : isBitRepresentable spec x) : isRepresentable spec.toFormat x := by
  obtain ⟨m, e, hval, hm, he_lo, _, _⟩ := hx
  refine ⟨m, e, ?_, hm, he_lo⟩
  rw [hval]; simp only [BinarySpec.toFormat]; push_cast; rfl

/-- Forward: toReal of a finite FloatBits is bit-representable. -/
theorem FloatBits.toReal_isBitRepresentable {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.classify = .normal ∨ f.classify = .subnormal) :
    isBitRepresentable spec f.toReal := by
  -- Directly construct the witness using the concrete exponent
  let m := f.toRepr.sign.toInt * (f.toRepr.significand : ℤ)
  let e := (f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - (spec.sigWidth : ℤ)
  refine ⟨m, e, ?_, ?_, ?_, ?_, ?_⟩
  · -- toReal = m * 2^e
    show f.toReal = (m : ℝ) * (2 : ℝ) ^ e
    simp only [FloatBits.toReal, m, e]
    rcases hfin with h | h <;> (rw [h]; push_cast; ring)
  · -- |m| < 2^(sigWidth+1)
    show |m| < (2 : ℤ) ^ (spec.sigWidth + 1)
    show |f.toRepr.sign.toInt * (f.toRepr.significand : ℤ)| <
      (2 : ℤ) ^ (spec.sigWidth + 1)
    have hs_abs : |f.toRepr.sign.toInt| = 1 := by
      cases f.toRepr.sign <;> simp [Sign.toInt]
    rw [abs_mul, hs_abs, one_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    rcases hfin with h | h
    · exact_mod_cast (f.normal_significand_range h).2
    · have h1 := f.subnormal_significand_range h
      exact_mod_cast show f.toRepr.significand < 2 ^ (spec.sigWidth + 1) by
        have := spec.hSig; omega
  · -- emin ≤ e
    show (1 : ℤ) - (spec.bias : ℤ) - spec.sigWidth ≤
      (f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth
    suffices h : 1 ≤ (f.toRepr.exponent : ℤ) by omega
    rcases hfin with h | h
    · have h_nz : f.isExpZero = false := by
        by_contra hb; simp only [Bool.not_eq_false] at hb
        unfold classify at h; simp only [hb, ite_true] at h; split_ifs at h
      unfold toRepr; simp [h_nz]
      have : f.expField ≠ 0 := by
        intro hab; simp [isExpZero, hab] at h_nz
      exact_mod_cast BitVec.toNat_pos_of_ne_zero this
    · have h_z : f.isExpZero = true := by
        unfold classify at h; split_ifs at h; simp_all
      unfold toRepr; simp [h_z]
  · -- e ≤ bias - sigWidth
    show (f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth ≤
      (spec.bias : ℤ) - spec.sigWidth
    suffices h : (f.toRepr.exponent : ℤ) ≤ 2 * (spec.bias : ℤ) by omega
    rcases hfin with h | h
    · have h_nz : f.isExpZero = false := by
        by_contra hb; simp only [Bool.not_eq_false] at hb
        unfold classify at h; simp only [hb, ite_true] at h; split_ifs at h
      have h_nmax : f.isExpMax = false := by
        by_contra hb; simp only [Bool.not_eq_false] at hb
        unfold classify at h; simp only [hb, ite_true] at h; split_ifs at h
      unfold toRepr; simp [h_nz]
      have hlt := f.expField.isLt
      have hne : f.expField ≠ BitVec.allOnes spec.expWidth := by
        intro hab; simp [isExpMax, hab] at h_nmax
      -- expField.toNat < 2^expWidth and ≠ allOnes (= 2^expWidth - 1)
      -- so expField.toNat ≤ 2^expWidth - 2
      -- bias = 2^(expWidth-1) - 1, so 2*bias = 2^expWidth - 2
      have hne_val : f.expField.toNat ≠ 2 ^ spec.expWidth - 1 := by
        intro hab
        apply hne
        apply BitVec.eq_of_toNat_eq
        rw [hab, BitVec.toNat_allOnes]
      have hle : f.expField.toNat ≤ 2 ^ spec.expWidth - 2 := by omega
      have hbias : spec.bias = 2 ^ (spec.expWidth - 1) - 1 := rfl
      have hpow : 2 ^ spec.expWidth = 2 * 2 ^ (spec.expWidth - 1) := by
        have := spec.hExp
        cases h : spec.expWidth with
        | zero => omega
        | succ m => simp [pow_succ, mul_comm]
      -- 2*bias = 2*(2^(ew-1)-1) = 2^ew - 2
      have : 2 * spec.bias = 2 ^ spec.expWidth - 2 := by omega
      omega
    · have h_z : f.isExpZero = true := by
        unfold classify at h; split_ifs at h; simp_all
      unfold toRepr; simp [h_z]
      have hbias : spec.bias = 2 ^ (spec.expWidth - 1) - 1 := rfl
      have : 2 ≤ 2 ^ (spec.expWidth - 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (spec.expWidth - 1) :=
            Nat.pow_le_pow_right (by omega) (by have := spec.hExp; omega)
      omega
  · -- Canonicality: |m| ≥ 2^sigWidth or e = emin
    rcases hfin with h | h
    · -- Normal: significand ≥ 2^sigWidth, so |m| ≥ 2^sigWidth
      left
      show (2 : ℤ) ^ spec.sigWidth ≤
        |f.toRepr.sign.toInt * (f.toRepr.significand : ℤ)|
      have hs_abs : |f.toRepr.sign.toInt| = 1 := by
        cases f.toRepr.sign <;> simp [Sign.toInt]
      rw [abs_mul, hs_abs, one_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast (f.normal_significand_range h).1
    · -- Subnormal: exponent = 1, so e = 1 - bias - sigWidth = emin
      right
      have h_z : f.isExpZero = true := by
        unfold classify at h; split_ifs at h; simp_all
      show (f.toRepr.exponent : ℤ) - (spec.bias : ℤ) - spec.sigWidth =
        (1 : ℤ) - (spec.bias : ℤ) - spec.sigWidth
      unfold toRepr; simp [h_z]

/-! ## Reverse bridge helpers -/

def FloatBits.zero (spec : BinarySpec) : FloatBits spec :=
  FloatBits.fromFields 0 0 0

theorem FloatBits.zero_classify {spec : BinarySpec} :
    (FloatBits.zero spec).classify = .zero := by
  unfold zero classify
  simp only [fromFields_isExpMax, fromFields_isExpZero, fromFields_sigField]
  have h0 : (0 : BitVec spec.expWidth) ≠ BitVec.allOnes spec.expWidth := by
    intro hab
    have h1 := congr_arg BitVec.toNat hab
    simp only [BitVec.toNat_allOnes] at h1
    have : 0 < 2 ^ spec.expWidth - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_two_pow_iff.mpr (by have := spec.hExp; omega))
    exact absurd h1.symm (ne_of_gt this)
  simp only [beq_iff_eq, h0, ite_false, ite_true]

theorem FloatBits.zero_toReal {spec : BinarySpec} :
    (FloatBits.zero spec).toReal = 0 := by
  unfold toReal; rw [zero_classify]

theorem FloatBits.fromFields_classify_subnormal
    {spec : BinarySpec} (s : BitVec 1)
    (m : BitVec spec.sigWidth) (hm : m ≠ 0) :
    (FloatBits.fromFields s 0 m).classify = .subnormal := by
  unfold classify
  simp only [fromFields_isExpMax, fromFields_isExpZero, fromFields_sigField]
  have h0 : (0 : BitVec spec.expWidth) ≠ BitVec.allOnes spec.expWidth := by
    intro hab
    have h1 := congr_arg BitVec.toNat hab
    simp only [BitVec.toNat_allOnes] at h1
    have : 0 < 2 ^ spec.expWidth - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_two_pow_iff.mpr (by have := spec.hExp; omega))
    exact absurd h1.symm (ne_of_gt this)
  have h1 : ((0 : BitVec spec.expWidth) == BitVec.allOnes spec.expWidth) = false :=
    beq_eq_false_iff_ne.mpr h0
  have h2 : (m == (0 : BitVec spec.sigWidth)) = false :=
    beq_eq_false_iff_ne.mpr hm
  simp only [h1, h2, ite_false, ite_true, Bool.false_eq_true, beq_iff_eq]

/-! ## Reverse bridge -/

/-- Every bit-representable real is the toReal of some finite FloatBits. -/
theorem FloatBits.exists_of_isBitRepresentable
    {spec : BinarySpec} {x : ℝ}
    (hx : isBitRepresentable spec x) :
    ∃ (f : FloatBits spec),
      (f.classify = .normal ∨ f.classify = .subnormal ∨ f.classify = .zero) ∧
      f.toReal = x := by
  obtain ⟨m, e, hval, hm_bound, he_lo, he_hi, hcanon⟩ := hx
  by_cases hm0 : m = 0
  · exact ⟨FloatBits.zero spec, Or.inr (Or.inr zero_classify),
      by rw [zero_toReal, hval, hm0]; simp⟩
  · -- m ≠ 0, construct FloatBits encoding m * 2^e
    have ham_bound : m.natAbs < 2 ^ (spec.sigWidth + 1) := by
      have key : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
      exact_mod_cast key ▸ hm_bound
    have hE_lo : 1 ≤ e + (spec.bias : ℤ) + (spec.sigWidth : ℤ) := by
      have : spec.toFormat.emin = 1 - (spec.bias : ℤ) - spec.sigWidth := rfl; omega
    have hE_hi : e + (spec.bias : ℤ) + spec.sigWidth ≤ 2 * (spec.bias : ℤ) := by omega
    -- Sign bit
    let s : BitVec 1 := if 0 < m then 0 else 1
    have hs_val : Sign.toInt (if s = 0 then .pos else .neg) = if 0 < m then 1 else -1 := by
      simp only [s]
      by_cases hm_pos : 0 < m
      · simp only [hm_pos, ite_true]; rfl
      · simp only [hm_pos, ite_false]
        have hne : (1 : BitVec 1) ≠ 0 := by decide
        simp only [hne, ite_false]; rfl
    -- m = sign * |m| (as integers, then cast)
    have hm_decomp : (m : ℝ) = ((if 0 < m then (1 : ℤ) else -1) * (m.natAbs : ℤ) : ℤ) := by
      rcases Int.lt_or_lt_of_ne hm0 with h | h
      · simp only [show ¬(0 < m) from not_lt.mpr h.le, ite_false,
          Int.natCast_natAbs, neg_one_mul, abs_of_neg h, neg_neg]
      · simp only [h, ite_true, Int.natCast_natAbs, one_mul, abs_of_pos h]
    by_cases ham_lo_dec : 2 ^ spec.sigWidth ≤ m.natAbs
    · -- Case: |m| ≥ 2^sigWidth (normal encoding)
      -- Biased exponent E
      set E := (e + (spec.bias : ℤ) + spec.sigWidth).toNat
      have hE_eq : (E : ℤ) = e + (spec.bias : ℤ) + spec.sigWidth := by
        exact Int.toNat_of_nonneg (by omega)
      -- E fits in expWidth bits and is not allOnes
      have hE_lt : E < 2 ^ spec.expWidth := by
        have hbias : spec.bias = 2 ^ (spec.expWidth - 1) - 1 := rfl
        have hpow : 2 ^ spec.expWidth = 2 * 2 ^ (spec.expWidth - 1) := by
          have := spec.hExp
          cases h : spec.expWidth with
          | zero => omega
          | succ n => simp [pow_succ, mul_comm]
        omega
      have hE_pos : 0 < E := by omega
      have hE_ne_max : E ≠ 2 ^ spec.expWidth - 1 := by
        have hbias : spec.bias = 2 ^ (spec.expWidth - 1) - 1 := rfl
        have hpow : 2 ^ spec.expWidth = 2 * 2 ^ (spec.expWidth - 1) := by
          have := spec.hExp
          cases h : spec.expWidth with
          | zero => omega
          | succ n => simp [pow_succ, mul_comm]
        omega
      -- Trailing significand
      have hsig_lt : m.natAbs - 2 ^ spec.sigWidth < 2 ^ spec.sigWidth := by omega
      -- Construct the FloatBits
      let expBV : BitVec spec.expWidth := BitVec.ofNat spec.expWidth E
      let sigBV : BitVec spec.sigWidth := BitVec.ofNat spec.sigWidth (m.natAbs - 2 ^ spec.sigWidth)
      have hexpBV_toNat : expBV.toNat = E := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE_lt]
      have hsigBV_toNat : sigBV.toNat = m.natAbs - 2 ^ spec.sigWidth :=
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hexpBV_ne_zero : expBV ≠ 0 := by
        intro h; have := congr_arg BitVec.toNat h
        simp [hexpBV_toNat] at this; omega
      have hexpBV_ne_max : expBV ≠ BitVec.allOnes spec.expWidth := by
        intro h; have := congr_arg BitVec.toNat h
        simp [hexpBV_toNat, BitVec.toNat_allOnes] at this; omega
      refine ⟨FloatBits.fromFields s expBV sigBV, Or.inl
          (fromFields_classify_normal s expBV sigBV hexpBV_ne_zero hexpBV_ne_max), ?_⟩
      -- Prove sign.toInt = if 0 < m then 1 else -1
      have hs_sign : (if (s == (0 : BitVec 1)) = true then Sign.pos else Sign.neg).toInt =
          if 0 < m then 1 else -1 := by
        simp only [s]
        by_cases hm_pos : 0 < m
        · simp only [hm_pos, ite_true, beq_self_eq_true, ite_true]; rfl
        · simp only [hm_pos, ite_false]
          have hne : (1 : BitVec 1) ≠ 0 := by decide
          have hbeq : ((1 : BitVec 1) == (0 : BitVec 1)) = false := beq_eq_false_iff_ne.mpr hne
          simp only [hbeq]; rfl
      -- Compute toReal directly
      have hsig_add : m.natAbs - 2 ^ spec.sigWidth + 2 ^ spec.sigWidth = m.natAbs := by omega
      simp only [FloatBits.toReal,
        fromFields_classify_normal s expBV sigBV hexpBV_ne_zero hexpBV_ne_max,
        FloatBits.toRepr, FloatBits.sign,
        fromFields_isExpZero, beq_eq_false_iff_ne.mpr hexpBV_ne_zero,
        Bool.false_eq_true, ↓reduceIte,
        fromFields_expField, fromFields_sigField, fromFields_signBit,
        hexpBV_toNat, hsigBV_toNat, show m.natAbs - 2 ^ spec.sigWidth + 2 ^ spec.sigWidth
          = m.natAbs from hsig_add, hs_sign]
      rw [hval, hm_decomp, hE_eq]
      push_cast
      rcases Int.lt_or_lt_of_ne hm0 with hm_neg | hm_pos
      · simp only [show ¬0 < m from not_lt.mpr hm_neg.le, ite_false]; ring_nf
      · simp only [hm_pos, ite_true]; ring_nf
    · -- Case: |m| < 2^sigWidth (subnormal encoding)
      push Not at ham_lo_dec
      have ham_sub : m.natAbs < 2 ^ spec.sigWidth := ham_lo_dec
      -- Canonicality forces e = emin
      have hcanon_sub : e = spec.toFormat.emin := by
        rcases hcanon with h | h
        · exfalso
          have habs : |m| = (m.natAbs : ℤ) := (Int.natCast_natAbs m).symm
          rw [habs] at h
          exact absurd (Int.ofNat_lt.mpr ham_sub) (not_lt.mpr h)
        · exact h
      -- expField = 0, sigField = m.natAbs
      let sigBV : BitVec spec.sigWidth := BitVec.ofNat spec.sigWidth m.natAbs
      have hsigBV_toNat : sigBV.toNat = m.natAbs := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ham_sub]
      have hsigBV_ne_zero : sigBV ≠ 0 := by
        intro h; have := congr_arg BitVec.toNat h
        simp [hsigBV_toNat] at this
        exact hm0 (Int.natAbs_eq_zero.mp (by omega))
      have hs_sign : (if (s == (0 : BitVec 1)) = true then Sign.pos else Sign.neg).toInt =
          if 0 < m then 1 else -1 := by
        simp only [s]
        by_cases hm_pos : 0 < m
        · simp only [hm_pos, ite_true, beq_self_eq_true, ite_true]; rfl
        · simp only [hm_pos, ite_false]
          have hne : (1 : BitVec 1) ≠ 0 := by decide
          have hbeq : ((1 : BitVec 1) == (0 : BitVec 1)) = false := beq_eq_false_iff_ne.mpr hne
          simp only [hbeq]; rfl
      refine ⟨FloatBits.fromFields s 0 sigBV, Or.inr (Or.inl
          (fromFields_classify_subnormal s sigBV hsigBV_ne_zero)), ?_⟩
      simp only [FloatBits.toReal, fromFields_classify_subnormal s sigBV hsigBV_ne_zero,
        FloatBits.toRepr, FloatBits.sign, fromFields_isExpZero, beq_self_eq_true, ↓reduceIte,
        fromFields_sigField, fromFields_signBit, hsigBV_toNat, hs_sign]
      rw [hval, hm_decomp, hcanon_sub]
      simp only [BinarySpec.toFormat]
      push_cast
      rcases Int.lt_or_lt_of_ne hm0 with hm_neg | hm_pos
      · simp only [show ¬0 < m from not_lt.mpr hm_neg.le, ite_false]
      · simp only [hm_pos, ite_true]

end Flean
