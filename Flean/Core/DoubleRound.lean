import Flean.Core.NearestEven

/-!
# Flean.Core.DoubleRound

Double rounding theorem: rounding in two steps (first to a finer format,
then to a coarser format) yields the same result as rounding directly
to the coarser format.

For directed rounding modes (roundDN, roundUP, roundTZ), the only condition
is that fmt2 refines fmt1 (same radix, at least as much precision, at least
as small emin). The proof uses only monotonicity and idempotence.

This follows Flocq's `round_round` family of theorems.
-/

namespace Flean

/-! ## Format refinement -/

/-- fmt2 refines fmt1: same radix, at least as much precision, at least as small emin. -/
structure FormatRefines (fmt1 fmt2 : FloatFormat) : Prop where
  radix_eq : fmt1.β = fmt2.β
  prec_le : fmt1.prec ≤ fmt2.prec
  emin_le : fmt2.emin ≤ fmt1.emin

/-- Every fmt1-representable number is also fmt2-representable. -/
theorem isRepresentable_of_refines {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) : isRepresentable fmt2 x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  refine ⟨m, e, ?_, ?_, le_trans href.emin_le he⟩
  · rw [hval, href.radix_eq]
  · calc |m| < (fmt1.β ^ fmt1.prec : ℤ) := hm
      _ ≤ (fmt2.β ^ fmt2.prec : ℤ) := by
          rw [← href.radix_eq]
          exact_mod_cast Nat.pow_le_pow_right (by have := fmt1.hβ; omega) href.prec_le

/-! ## Double rounding for directed modes -/

/-- Double rounding for roundDN. -/
theorem double_roundDN {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundDN fmt1 (roundDN fmt2 x) = roundDN fmt1 x := by
  have h_fixed : roundDN fmt2 (roundDN fmt1 x) = roundDN fmt1 x :=
    roundDN_repr_fixed fmt2 (isRepresentable_of_refines href (roundDN_isRepresentable fmt1 x))
  have h_le : roundDN fmt1 x ≤ roundDN fmt2 x :=
    h_fixed ▸ roundDN_monotone fmt2 (roundDN_le fmt1 x)
  have h1 : roundDN fmt1 (roundDN fmt2 x) ≤ roundDN fmt1 x :=
    roundDN_monotone fmt1 (roundDN_le fmt2 x)
  have h2 : roundDN fmt1 x ≤ roundDN fmt1 (roundDN fmt2 x) := by
    calc roundDN fmt1 x
        = roundDN fmt1 (roundDN fmt1 x) := (roundDN_idempotent fmt1 x).symm
      _ ≤ roundDN fmt1 (roundDN fmt2 x) := roundDN_monotone fmt1 h_le
  linarith

/-- Double rounding for roundUP. -/
theorem double_roundUP {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundUP fmt1 (roundUP fmt2 x) = roundUP fmt1 x := by
  have h_fixed : roundUP fmt2 (roundUP fmt1 x) = roundUP fmt1 x :=
    roundUP_repr_fixed fmt2 (isRepresentable_of_refines href (roundUP_isRepresentable fmt1 x))
  have h_le : roundUP fmt2 x ≤ roundUP fmt1 x :=
    le_of_le_of_eq (roundUP_monotone fmt2 (roundUP_ge fmt1 x)) h_fixed
  have h1 : roundUP fmt1 (roundUP fmt2 x) ≤ roundUP fmt1 x := by
    calc roundUP fmt1 (roundUP fmt2 x)
        ≤ roundUP fmt1 (roundUP fmt1 x) := roundUP_monotone fmt1 h_le
      _ = roundUP fmt1 x := roundUP_idempotent fmt1 x
  have h2 : roundUP fmt1 x ≤ roundUP fmt1 (roundUP fmt2 x) :=
    roundUP_monotone fmt1 (roundUP_ge fmt2 x)
  linarith

/-- Double rounding for roundTZ. Reduces to roundDN via sign analysis. -/
theorem double_roundTZ {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundTZ fmt1 (roundTZ fmt2 x) = roundTZ fmt1 x := by
  by_cases hx : 0 ≤ x
  · rw [← roundDN_eq_roundTZ_nonneg fmt1 (roundTZ_nonneg fmt2 hx),
        ← roundDN_eq_roundTZ_nonneg fmt2 hx,
        ← roundDN_eq_roundTZ_nonneg fmt1 hx]
    exact double_roundDN href x
  · push Not at hx
    -- For x < 0: roundTZ fmt2 x ≤ 0, so we work with -x > 0
    have hx_neg : x < 0 := hx
    -- roundTZ fmt2 x = -roundTZ fmt2 (-x), and roundTZ fmt2 (-x) ≥ 0
    have h0 : 0 ≤ -x := by linarith
    have h1 : roundTZ fmt2 x = -(roundTZ fmt2 (-x)) := by
      linarith [roundTZ_neg fmt2 x]
    have h2 : roundTZ fmt1 x = -(roundTZ fmt1 (-x)) := by
      linarith [roundTZ_neg fmt1 x]
    rw [h1, h2]
    have h3 : roundTZ fmt1 (-(roundTZ fmt2 (-x))) = -(roundTZ fmt1 (roundTZ fmt2 (-x))) :=
      roundTZ_neg fmt1 _
    rw [h3]
    congr 1
    rw [← roundDN_eq_roundTZ_nonneg fmt1 (roundTZ_nonneg fmt2 h0),
        ← roundDN_eq_roundTZ_nonneg fmt2 h0,
        ← roundDN_eq_roundTZ_nonneg fmt1 h0]
    exact double_roundDN href (-x)

/-! ## Sandwich lemma for roundNNE -/

/-- The intermediate roundNNE fmt2 result lies in [roundDN fmt1 x, roundUP fmt1 x]. -/
theorem roundNNE_between_DN_UP {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundDN fmt1 x ≤ roundNNE fmt2 x ∧ roundNNE fmt2 x ≤ roundUP fmt1 x := by
  constructor
  · calc roundDN fmt1 x
        = roundDN fmt1 (roundDN fmt2 x) := (double_roundDN href x).symm
      _ ≤ roundDN fmt1 (roundNNE fmt2 x) :=
          roundDN_monotone fmt1 (roundNNE_ge_roundDN fmt2 x)
      _ ≤ roundNNE fmt2 x := roundDN_le fmt1 _
  · calc roundNNE fmt2 x
        ≤ roundUP fmt1 (roundNNE fmt2 x) := roundUP_ge fmt1 _
      _ ≤ roundUP fmt1 (roundUP fmt2 x) :=
          roundUP_monotone fmt1 (roundNNE_le_roundUP fmt2 x)
      _ = roundUP fmt1 x := double_roundUP href x

/-! ## Canonical exponent relationship -/

/-- The fine-format cexp is at most the coarse-format cexp. -/
theorem cexp_refines_le {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    cexp fmt2 x ≤ cexp fmt1 x := by
  unfold cexp
  by_cases hx : x = 0
  · simp [hx]; exact href.emin_le
  · simp only [hx, ite_false]; rw [href.radix_eq]
    apply max_le
    · exact le_trans href.emin_le (le_max_left _ _)
    · apply le_max_of_le_right
      have hp : (fmt1.prec : ℤ) ≤ fmt2.prec := by exact_mod_cast href.prec_le
      linarith

/-- Fine-format grid spacing is at most coarse-format grid spacing. -/
theorem bpow_cexp_refines_le {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    bpow fmt2 (cexp fmt2 x) ≤ bpow fmt1 (cexp fmt1 x) := by
  unfold bpow; rw [href.radix_eq]
  exact zpow_le_zpow_right₀
    (by exact_mod_cast (show 1 ≤ fmt2.β from by have := fmt2.hβ; omega))
    (cexp_refines_le href x)

end Flean
