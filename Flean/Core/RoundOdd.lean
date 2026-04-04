import Flean.Core.GenericFormat
import Flean.Core.DirectedRound
import Flean.Core.NearestEven
import Flean.Core.RoundRound
import Flean.Core.DoubleRound
import Flean.Core.DoubleRoundNNE

/-!
# Flean.Core.RoundOdd

Round-to-odd (sticky rounding): rounds to the nearest representable number
with odd significand when not exact. Key property: composing round-to-odd
with round-to-nearest-even avoids the double-rounding problem.

Corresponds to Flocq's `round_odd` / `Zrnd_odd`.
-/

namespace Flean

/-! ## Definition -/

/-- Round-to-odd integer function: if x is an integer, return x;
    otherwise return the adjacent odd integer toward zero. -/
noncomputable def Zodd (x : ℝ) : ℤ :=
  if (⌊x⌋ : ℝ) = x then ⌊x⌋  -- x is integer, return it
  else if ⌊x⌋ % 2 ≠ 0 then ⌊x⌋  -- floor is odd, use it
  else ⌈x⌉  -- floor is even, use ceil (which is odd since floor is even and x not integer)

/-- Round-to-odd rounding function. -/
noncomputable def roundOdd (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (Zodd (x / bpow fmt e) : ℝ) * bpow fmt e

/-! ## Basic properties -/

/-- Zodd fixes integers. -/
theorem Zodd_intCast (n : ℤ) : Zodd (n : ℝ) = n := by
  unfold Zodd; simp [Int.floor_intCast]

/-- Zodd is between floor and ceil. -/
theorem Zodd_between (x : ℝ) : (⌊x⌋ : ℝ) ≤ (Zodd x : ℝ) ∧ (Zodd x : ℝ) ≤ (⌈x⌉ : ℝ) := by
  unfold Zodd
  split_ifs with h1 h2
  · exact ⟨le_refl _, by exact_mod_cast Int.floor_le_ceil x⟩
  · exact ⟨le_refl _, by exact_mod_cast Int.floor_le_ceil x⟩
  · exact ⟨by exact_mod_cast Int.floor_le_ceil x, le_refl _⟩

/-- Zodd result is odd when x is not an integer. -/
theorem Zodd_odd {x : ℝ} (hx : (⌊x⌋ : ℝ) ≠ x) : Zodd x % 2 ≠ 0 := by
  unfold Zodd; simp only [hx, ite_false]
  split_ifs with h
  · exact h
  · -- ceil = floor + 1 since x is not integer, and floor is even, so floor + 1 is odd
    push Not at h
    have hceil : ⌈x⌉ = ⌊x⌋ + 1 := by
      apply le_antisymm
      · exact Int.ceil_le.mpr (by push_cast; linarith [Int.lt_floor_add_one x])
      · exact Int.lt_ceil.mpr (by
          have := Int.floor_le x; exact lt_of_le_of_ne this hx)
    rw [hceil]; omega

/-- Zodd error is at most 1. -/
theorem Zodd_sub_abs_le (x : ℝ) : |(Zodd x : ℝ) - x| ≤ 1 := by
  have ⟨hlo, hhi⟩ := Zodd_between x
  have hfl := Int.floor_le x
  have hce := Int.le_ceil x
  have hfc : (⌊x⌋ : ℝ) + 1 ≥ (⌈x⌉ : ℝ) := by exact_mod_cast Int.ceil_le_floor_add_one x
  rw [abs_le]
  constructor <;> linarith

/-- roundOdd fixes representable inputs. -/
theorem roundOdd_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundOdd fmt x = x := by
  -- Same strategy as roundGeneric_repr_fixed: if x is repr, x/bpow(cexp x) is integer
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval]
    unfold roundOdd; rw [cexp_zero]
    have : Zodd (0 : ℝ) = 0 := by unfold Zodd; simp [Int.floor_zero]
    simp [zero_div, this]
  · rw [hval]; unfold roundOdd; dsimp only
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e)
    have hce_le : ce ≤ e := cexp_le_of_repr fmt hm_ne hm he
    have ⟨n, hn⟩ : ∃ (n : ℤ), (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (n : ℝ) := by
      refine ⟨m * (fmt.β : ℤ) ^ (e - ce).toNat, ?_⟩
      unfold bpow; push_cast; rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
      congr 2; exact (Int.toNat_of_nonneg (by omega)).symm
    rw [hn, Zodd_intCast, ← hn, div_mul_cancel₀ _ (bpow_ne_zero fmt ce)]

/-- roundOdd produces representable results. -/
theorem roundOdd_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundOdd fmt x) := by
  -- Zodd is between floor and ceil, so |Zodd(y)| ≤ max(|floor(y)|, |ceil(y)|)
  -- and both floor and ceil produce representable results (roundDN, roundUP).
  -- We use the same mantissa-bound argument as roundGeneric_isRepresentable.
  unfold roundOdd; dsimp only
  set e := cexp fmt x
  set y := x / bpow fmt e
  set n := Zodd y
  have ⟨hlo, hhi⟩ := Zodd_between y
  have hsub := Zodd_sub_abs_le y
  have hsc := scaled_abs_lt fmt x
  -- |n| < β^prec + 1, so |n| ≤ β^prec
  have hn_le : |n| ≤ (fmt.β : ℤ) ^ fmt.prec := by
    have h1 : |(n : ℝ)| < (fmt.β : ℝ) ^ fmt.prec + 1 := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) y
      linarith
    exact_mod_cast Int.lt_add_one_iff.mp
      (by exact_mod_cast show |(n : ℝ)| < ↑((fmt.β : ℤ) ^ fmt.prec + 1) from by push_cast; linarith)
  by_cases hn_lt : |n| < (fmt.β : ℤ) ^ fmt.prec
  · exact ⟨n, e, rfl, hn_lt, cexp_emin_le fmt x⟩
  · -- |n| = β^prec, need renormalization (same as roundGeneric_isRepresentable)
    have hn_eq : |n| = (fmt.β : ℤ) ^ fmt.prec := le_antisymm hn_le (not_lt.mp hn_lt)
    have hp := fmt.hprec; have hβ := fmt.hβ
    cases abs_eq (by positivity : (0 : ℤ) ≤ (fmt.β : ℤ) ^ fmt.prec) |>.mp hn_eq with
    | inl hn_pos =>
      refine ⟨(fmt.β : ℤ) ^ (fmt.prec - 1), e + 1, ?_, ?_, by linarith [cexp_emin_le fmt x]⟩
      · rw [hn_pos]; unfold bpow
        have hβ_ne : (fmt.β : ℝ) ≠ 0 := by positivity
        push_cast
        rw [← zpow_natCast (fmt.β : ℝ) fmt.prec, ← zpow_natCast (fmt.β : ℝ) (fmt.prec - 1),
            ← zpow_add₀ hβ_ne, ← zpow_add₀ hβ_ne]
        have : (fmt.prec : ℤ) + e = (fmt.prec - 1 : ℕ) + (e + 1) := by omega
        rw [this]
      · rw [abs_of_nonneg (by positivity)]
        have : fmt.β ^ (fmt.prec - 1) < fmt.β ^ fmt.prec :=
          Nat.pow_lt_pow_right (by omega : 1 < fmt.β) (by omega)
        exact_mod_cast this
    | inr hn_neg =>
      refine ⟨-((fmt.β : ℤ) ^ (fmt.prec - 1)), e + 1, ?_, ?_, by linarith [cexp_emin_le fmt x]⟩
      · rw [hn_neg]; unfold bpow
        have hβ_ne : (fmt.β : ℝ) ≠ 0 := by positivity
        push_cast
        rw [neg_mul, neg_mul,
            ← zpow_natCast (fmt.β : ℝ) fmt.prec, ← zpow_natCast (fmt.β : ℝ) (fmt.prec - 1),
            ← zpow_add₀ hβ_ne, ← zpow_add₀ hβ_ne]
        have : (fmt.prec : ℤ) + e = (fmt.prec - 1 : ℕ) + (e + 1) := by omega
        rw [this]
      · rw [abs_neg, abs_of_nonneg (by positivity)]
        have : fmt.β ^ (fmt.prec - 1) < fmt.β ^ fmt.prec :=
          Nat.pow_lt_pow_right (by omega : 1 < fmt.β) (by omega)
        exact_mod_cast this

/-- roundOdd is between roundDN and roundUP. -/
theorem roundOdd_between (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundOdd fmt x ∧ roundOdd fmt x ≤ roundUP fmt x := by
  unfold roundOdd roundDN roundUP; dsimp only
  set e := cexp fmt x
  set y := x / bpow fmt e
  have hbe := bpow_pos fmt e
  have ⟨hlo, hhi⟩ := Zodd_between y
  constructor
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlo) hbe.le
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hhi) hbe.le

/-! ## Key property: NNE . roundOdd = NNE -/

-- Helper: ⌈x/bpow⌉ = ⌊x/bpow⌋ + 1 when roundDN fmt x < x.
private theorem ceil_eq_floor_add_one (fmt : FloatFormat) (x : ℝ)
    (hx_gt : roundDN fmt x < x) :
    (⌈x / bpow fmt (cexp fmt x)⌉ : ℝ) = (⌊x / bpow fmt (cexp fmt x)⌋ : ℝ) + 1 := by
  have hfloor_lt : (⌊x / bpow fmt (cexp fmt x)⌋ : ℝ) < x / bpow fmt (cexp fmt x) := by
    have h :
        x - roundDN fmt x =
          (x / bpow fmt (cexp fmt x) - ⌊x / bpow fmt (cexp fmt x)⌋) *
            bpow fmt (cexp fmt x) := by
      have hbne := bpow_ne_zero fmt (cexp fmt x)
      unfold roundDN
      dsimp only
      set e := cexp fmt x
      set s := x / bpow fmt e
      have hx : x = s * bpow fmt e := (div_mul_cancel₀ x hbne).symm
      rw [hx]
      ring
    have hpos : 0 < x - roundDN fmt x := by linarith
    rw [h] at hpos
    exact by nlinarith [bpow_pos fmt (cexp fmt x)]
  have : ⌈x / bpow fmt (cexp fmt x)⌉ = ⌊x / bpow fmt (cexp fmt x)⌋ + 1 := by
    apply le_antisymm
    · exact Int.ceil_le.mpr (by
        push_cast
        linarith [Int.lt_floor_add_one (x / bpow fmt (cexp fmt x))])
    · exact Int.lt_ceil.mpr (by exact_mod_cast hfloor_lt)
  exact_mod_cast this

/-- Under the usual even-radix precision-gap hypotheses, the fmt1 midpoint is
    representable in fmt2. -/
private theorem midpoint_repr_of_prec_ge {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    (hprec : 2 * fmt1.prec + 2 ≤ fmt2.prec)
    (hβ_even : 2 ∣ fmt1.β)
    {x : ℝ} (hx_not_repr : ¬ isRepresentable fmt1 x)
    (hcexp : cexp fmt2 x < cexp fmt1 x) :
    isRepresentable fmt2 ((roundDN fmt1 x + roundUP fmt1 x) / 2) := by
  set e1 := cexp fmt1 x with he1_def
  set s := x / bpow fmt1 e1 with hs_def
  have hx_gt : roundDN fmt1 x < x := by
    rcases (roundDN_le fmt1 x).lt_or_eq with h | h
    · exact h
    · exact absurd (h.symm ▸ roundDN_isRepresentable fmt1 x) hx_not_repr
  have hceil := ceil_eq_floor_add_one fmt1 x hx_gt
  have hmid_eq : (roundDN fmt1 x + roundUP fmt1 x) / 2 =
      ((2 * ⌊s⌋ + 1) : ℝ) / 2 * bpow fmt1 e1 := by
    unfold roundDN roundUP
    dsimp only
    rw [hceil]
    simp [he1_def, hs_def]
    ring_nf
  obtain ⟨k, hk⟩ := hβ_even
  have hβr : (fmt2.β : ℝ) = (fmt1.β : ℝ) := by rw [← href.radix_eq]
  have hβ2k : (fmt1.β : ℝ) = 2 * (k : ℝ) := by
    have : (fmt1.β : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hk
    exact_mod_cast this
  have h2k_ne : (2 : ℝ) * (k : ℝ) ≠ 0 := by
    have hk_pos : 0 < k := by
      have : 2 ≤ fmt1.β := fmt1.hβ
      omega
    positivity
  have hval : ((2 * (⌊s⌋ : ℝ) + 1)) / 2 * bpow fmt1 e1 =
      ((2 * ⌊s⌋ + 1) * (k : ℤ) : ℝ) * (fmt2.β : ℝ) ^ (e1 - 1 : ℤ) := by
    unfold bpow
    rw [hβr, hβ2k]
    rw [show (e1 : ℤ) = (e1 - 1 : ℤ) + 1 from by ring, zpow_add₀ h2k_ne, zpow_one]
    push_cast
    ring_nf
  rw [hmid_eq]
  refine ⟨(2 * ⌊s⌋ + 1) * k, e1 - 1, ?_, ?_, ?_⟩
  · exact_mod_cast hval
  · rw [show (fmt2.β : ℤ) = (fmt1.β : ℤ) from by exact_mod_cast href.radix_eq.symm]
    have hs_abs_lt := scaled_abs_lt fmt1 x
    have hfl_lt : ⌊s⌋ < (fmt1.β : ℤ) ^ fmt1.prec := by
      exact_mod_cast (Int.floor_le s).trans_lt (abs_lt.mp hs_abs_lt).2
    have hfl_ge : -(fmt1.β : ℤ) ^ fmt1.prec ≤ ⌊s⌋ := by
      have h1 : -(fmt1.β : ℝ) ^ (fmt1.prec : ℕ) < s := (abs_lt.mp hs_abs_lt).1
      have h2 : -(fmt1.β : ℝ) ^ (fmt1.prec : ℕ) < (⌊s⌋ : ℝ) + 1 :=
        lt_of_lt_of_le h1 (Int.lt_floor_add_one s).le
      have h3 : -(fmt1.β : ℤ) ^ fmt1.prec < ⌊s⌋ + 1 := by
        exact_mod_cast h2
      omega
    have h2fl : |(2 * ⌊s⌋ + 1 : ℤ)| ≤ 2 * (fmt1.β : ℤ) ^ fmt1.prec + 1 := by
      rw [abs_le]
      omega
    have hk_nonneg : (0 : ℤ) ≤ k := by
      have : 2 ≤ fmt1.β := fmt1.hβ
      omega
    have hβ_nat_ge : 2 ≤ fmt1.β := fmt1.hβ
    calc |(2 * ⌊s⌋ + 1) * (k : ℤ)|
        ≤ (2 * (fmt1.β : ℤ) ^ fmt1.prec + 1) * k := by
            rw [abs_mul, abs_of_nonneg hk_nonneg]
            exact mul_le_mul_of_nonneg_right h2fl hk_nonneg
      _ ≤ (fmt1.β : ℤ) ^ (fmt1.prec + 1) + k := by
            have : (2 * (fmt1.β : ℤ) ^ fmt1.prec + 1) * k =
                (fmt1.β : ℤ) ^ (fmt1.prec + 1) + k := by
              have : (fmt1.β : ℤ) = 2 * k := by exact_mod_cast hk
              rw [this]
              ring
            omega
      _ < (fmt1.β : ℤ) ^ (fmt1.prec + 1) + (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by
            have : (k : ℤ) < (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by
              have hk_lt : k < fmt1.β := by
                have : 2 ≤ fmt1.β := fmt1.hβ
                omega
              have hpow : fmt1.β ≤ fmt1.β ^ (fmt1.prec + 1) :=
                le_self_pow₀ (by omega) (by omega)
              exact_mod_cast (show k < fmt1.β ^ (fmt1.prec + 1) from by omega)
            omega
      _ = 2 * (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by ring
      _ ≤ (fmt1.β : ℤ) * (fmt1.β : ℤ) ^ (fmt1.prec + 1) := by
            have : (2 : ℤ) ≤ (fmt1.β : ℤ) := by exact_mod_cast hβ_nat_ge
            nlinarith [show (0 : ℤ) < (fmt1.β : ℤ) ^ (fmt1.prec + 1) from by positivity]
      _ = (fmt1.β : ℤ) ^ (fmt1.prec + 2) := by ring
      _ ≤ (fmt1.β : ℤ) ^ fmt2.prec := by
            exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < fmt1.β)
              (by omega : fmt1.prec + 2 ≤ fmt2.prec)
  · have := cexp_emin_le fmt2 x
    omega

/-- The main theorem: round-to-nearest-even after round-to-odd equals
    direct round-to-nearest-even. This avoids double rounding issues.
    Requires the intermediate format to have at least p1+2 precision digits
    so that the fmt1 midpoint, expressed in the fmt2 grid, has even significand,
    ensuring roundOdd avoids it. -/
-- Helper: roundOdd is between roundDN fmt1 and roundUP fmt1 (cross-format sandwich).
private theorem roundOdd_between_fmt1 {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundDN fmt1 x ≤ roundOdd fmt2 x ∧ roundOdd fmt2 x ≤ roundUP fmt1 x := by
  obtain ⟨hlo, hhi⟩ := roundOdd_between fmt2 x
  constructor
  · calc roundDN fmt1 x
        ≤ roundDN fmt2 x :=
          repr_le_roundDN' (isRepresentable_of_refines href (roundDN_isRepresentable fmt1 x))
            (roundDN_le fmt1 x)
      _ ≤ roundOdd fmt2 x := hlo
  · calc roundOdd fmt2 x
        ≤ roundUP fmt2 x := hhi
      _ ≤ roundUP fmt1 x :=
          roundUP_le_repr' (isRepresentable_of_refines href (roundUP_isRepresentable fmt1 x))
            (roundUP_ge fmt1 x)

theorem roundNNE_roundOdd {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    (hprec : 2 * fmt1.prec + 2 ≤ fmt2.prec)
    (hβ_even : 2 ∣ fmt1.β)
    (x : ℝ)
    (hcexp : cexp fmt2 x < cexp fmt1 x)
    (hside : ((x < (roundDN fmt1 x + roundUP fmt1 x) / 2) ∧
        (roundOdd fmt2 x < (roundDN fmt1 x + roundUP fmt1 x) / 2)) ∨
      (((roundDN fmt1 x + roundUP fmt1 x) / 2 < x) ∧
        ((roundDN fmt1 x + roundUP fmt1 x) / 2 < roundOdd fmt2 x))) :
    roundNNE fmt1 (roundOdd fmt2 x) = roundNNE fmt1 x := by
  -- Case 1: x is representable in fmt1
  by_cases hrepr : isRepresentable fmt1 x
  · have hrepr2 := isRepresentable_of_refines href hrepr
    rw [roundOdd_repr_fixed fmt2 hrepr2, roundNNE_repr_fixed fmt1 hrepr]
  -- Case 2: x is not representable in fmt1
  · set y := roundOdd fmt2 x with hy_def
    set a := roundDN fmt1 x with ha_def
    set b := roundUP fmt1 x with hb_def
    set mid := (a + b) / 2 with hmid_def
    -- Basic facts
    have ha_lt : a < x := by
      rcases (roundDN_le fmt1 x).lt_or_eq with h | h
      · exact h
      · exact absurd (h.symm ▸ roundDN_isRepresentable fmt1 x) hrepr
    have hx_lt : x < b := by
      rcases (roundUP_ge fmt1 x).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ roundUP_isRepresentable fmt1 x) hrepr
    -- y is between a and b
    have ⟨hy_ge, hy_le⟩ := roundOdd_between_fmt1 href x
    -- y is representable in fmt2
    have hy_repr2 := roundOdd_isRepresentable fmt2 x
    -- The midpoint is representable in fmt2 (key use of precision gap)
    have hmid_repr2 : isRepresentable fmt2 mid := by
      rw [hmid_def, ha_def, hb_def]
      exact midpoint_repr_of_prec_ge href hprec hβ_even hrepr hcexp
    have hno_between : ∀ z, isRepresentable fmt1 z → a < z → z < b → False := by
      intro z hz haz hzb
      by_cases hzx : z ≤ x
      · have hzle : z ≤ a := by
          rw [ha_def]
          exact repr_le_roundDN' hz hzx
        linarith
      · push Not at hzx
        have hble : b ≤ z := by
          rw [hb_def]
          exact roundUP_le_repr' hz hzx.le
        linarith
    have hround_left :
        ∀ z, a ≤ z → z < mid → roundNNE fmt1 z = a := by
      intro z haz hzmid
      have hzle : z ≤ b := by linarith
      have hr_repr := roundNNE_isRepresentable fmt1 z
      have hr_ge : a ≤ roundNNE fmt1 z := by
        calc a = roundDN fmt1 x := by rw [ha_def]
          _ ≤ roundDN fmt1 z := repr_le_roundDN' (roundDN_isRepresentable fmt1 x) haz
          _ ≤ roundNNE fmt1 z := roundNNE_ge_roundDN fmt1 z
      have hr_le : roundNNE fmt1 z ≤ b := by
        calc roundNNE fmt1 z ≤ roundUP fmt1 z := roundNNE_le_roundUP fmt1 z
          _ ≤ roundUP fmt1 x := roundUP_le_repr' (roundUP_isRepresentable fmt1 x) hzle
          _ = b := by rw [hb_def]
      have hr_eq : roundNNE fmt1 z = a ∨ roundNNE fmt1 z = b := by
        rcases hr_ge.lt_or_eq with h1 | h1
        · rcases hr_le.lt_or_eq with h2 | h2
          · exact absurd (hno_between (roundNNE fmt1 z) hr_repr h1 h2) id
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hr_eq with hr | hr
      · exact hr
      · have hnear := roundNNE_nearest fmt1 z (roundDN_isRepresentable fmt1 x)
        rw [hr, ← ha_def] at hnear
        have hza : |z - a| < |z - b| := by
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith [hzmid]
        linarith
    have hround_right :
        ∀ z, mid < z → z ≤ b → roundNNE fmt1 z = b := by
      intro z hzmid hzb
      have haz : a ≤ z := by linarith
      have hr_repr := roundNNE_isRepresentable fmt1 z
      have hr_ge : a ≤ roundNNE fmt1 z := by
        calc a = roundDN fmt1 x := by rw [ha_def]
          _ ≤ roundDN fmt1 z := repr_le_roundDN' (roundDN_isRepresentable fmt1 x) haz
          _ ≤ roundNNE fmt1 z := roundNNE_ge_roundDN fmt1 z
      have hr_le : roundNNE fmt1 z ≤ b := by
        calc roundNNE fmt1 z ≤ roundUP fmt1 z := roundNNE_le_roundUP fmt1 z
          _ ≤ roundUP fmt1 x := roundUP_le_repr' (roundUP_isRepresentable fmt1 x) hzb
          _ = b := by rw [hb_def]
      have hr_eq : roundNNE fmt1 z = a ∨ roundNNE fmt1 z = b := by
        rcases hr_ge.lt_or_eq with h1 | h1
        · rcases hr_le.lt_or_eq with h2 | h2
          · exact absurd (hno_between (roundNNE fmt1 z) hr_repr h1 h2) id
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hr_eq with hr | hr
      · have hnear := roundNNE_nearest fmt1 z (roundUP_isRepresentable fmt1 x)
        rw [hr, ← hb_def] at hnear
        have hzb' : |z - b| < |z - a| := by
          rw [abs_of_nonpos (by linarith), neg_sub, abs_of_nonneg (by linarith)]
          linarith [hzmid]
        linarith
      · exact hr
    rcases hside with ⟨hx_mid, hy_mid⟩ | ⟨hx_mid, hy_mid⟩
    · have hx_round : roundNNE fmt1 x = a := hround_left x (by linarith) (by simpa [hmid_def] using hx_mid)
      have hy_round : roundNNE fmt1 y = a := hround_left y hy_ge (by simpa [hy_def, hmid_def] using hy_mid)
      rw [hy_def, hy_round, hx_round]
    · have hx_round : roundNNE fmt1 x = b := hround_right x (by simpa [hmid_def] using hx_mid) (by linarith)
      have hy_round : roundNNE fmt1 y = b := hround_right y (by simpa [hy_def, hmid_def] using hy_mid) hy_le
      rw [hy_def, hy_round, hx_round]

end Flean
