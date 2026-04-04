import Flean.Core.NearestEven

/-!
# Flean.Core.DoubleRound

Double rounding theorem: rounding in two steps (first to a finer format,
then to a coarser format) yields the same result as rounding directly
to the coarser format.

## Directed modes (roundDN, roundUP, roundTZ)
Only require that fmt2 refines fmt1. Proof uses monotonicity and idempotence.

## Round-to-nearest-even (roundNNE)
Proved for two cases:
1. Same canonical exponent (subnormal range with equal emin).
2. Input already representable in fmt1.

The general NNE + NNE double rounding fails for arbitrary real inputs.
Counterexample: β=2, p1=2, p2=5, x=2.51 gives roundNNE_p1(roundNNE_p2(2.51))
= 2 ≠ 3 = roundNNE_p1(2.51). The intermediate rounding lands on the midpoint
2.5, causing a spurious tie-break. For bounded-precision IEEE 754 inputs
(precision ≤ 2*p1), this is avoided when p2 ≥ 2*p1.
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

/-! ## Generic double rounding for directed modes -/

/-- A ZrndFn is "directed downward" if zrnd y ≤ y for all y (like floor). -/
def ZrndFn.isDirectedDN (zr : ZrndFn) : Prop :=
  ∀ y : ℝ, (zr.zrnd y : ℝ) ≤ y

/-- A ZrndFn is "directed upward" if y ≤ zrnd y for all y (like ceil). -/
def ZrndFn.isDirectedUP (zr : ZrndFn) : Prop :=
  ∀ y : ℝ, y ≤ (zr.zrnd y : ℝ)

/-- Double rounding for directed-downward modes. -/
theorem double_roundGeneric_of_directedDN (zr : ZrndFn) {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    (hdir : zr.isDirectedDN)
    (hmon : Monotone (roundGeneric zr fmt1))
    (x : ℝ) :
    roundGeneric zr fmt1 (roundGeneric zr fmt2 x) = roundGeneric zr fmt1 x := by
  set y := roundGeneric zr fmt2 x
  have hy_le : y ≤ x := by
    show roundGeneric zr fmt2 x ≤ x
    show (zr.zrnd (x / bpow fmt2 (cexp fmt2 x)) : ℝ) * bpow fmt2 (cexp fmt2 x) ≤ x
    calc (zr.zrnd (x / bpow fmt2 (cexp fmt2 x)) : ℝ) * bpow fmt2 (cexp fmt2 x)
        ≤ (x / bpow fmt2 (cexp fmt2 x)) * bpow fmt2 (cexp fmt2 x) :=
          mul_le_mul_of_nonneg_right (hdir _) (bpow_pos fmt2 _).le
      _ = x := div_mul_cancel₀ x (bpow_ne_zero fmt2 _)
  have h1 : roundGeneric zr fmt1 y ≤ roundGeneric zr fmt1 x := hmon hy_le
  have h_r1_repr2 : isRepresentable fmt2 (roundGeneric zr fmt1 x) :=
    isRepresentable_of_refines href (roundGeneric_isRepresentable zr fmt1 x)
  have h_fixed : roundGeneric zr fmt2 (roundGeneric zr fmt1 x) = roundGeneric zr fmt1 x :=
    roundGeneric_repr_fixed zr fmt2 h_r1_repr2
  have h_r1_le : roundGeneric zr fmt1 x ≤ x := by
    show (zr.zrnd (x / bpow fmt1 (cexp fmt1 x)) : ℝ) * bpow fmt1 (cexp fmt1 x) ≤ x
    calc (zr.zrnd (x / bpow fmt1 (cexp fmt1 x)) : ℝ) * bpow fmt1 (cexp fmt1 x)
        ≤ (x / bpow fmt1 (cexp fmt1 x)) * bpow fmt1 (cexp fmt1 x) :=
          mul_le_mul_of_nonneg_right (hdir _) (bpow_pos fmt1 _).le
      _ = x := div_mul_cancel₀ x (bpow_ne_zero fmt1 _)
  have h2 : roundGeneric zr fmt1 x ≤ y :=
    h_fixed ▸ roundGeneric_monotone zr fmt2 h_r1_le
  have h3 : roundGeneric zr fmt1 x ≤ roundGeneric zr fmt1 y :=
    (roundGeneric_repr_fixed zr fmt1 (roundGeneric_isRepresentable zr fmt1 x)) ▸ hmon h2
  exact le_antisymm h1 h3

/-- Double rounding for directed-upward modes. -/
theorem double_roundGeneric_of_directedUP (zr : ZrndFn) {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2)
    (hdir : zr.isDirectedUP)
    (hmon : Monotone (roundGeneric zr fmt1))
    (x : ℝ) :
    roundGeneric zr fmt1 (roundGeneric zr fmt2 x) = roundGeneric zr fmt1 x := by
  set y := roundGeneric zr fmt2 x
  have hy_ge : x ≤ y := by
    show x ≤ roundGeneric zr fmt2 x
    show x ≤ (zr.zrnd (x / bpow fmt2 (cexp fmt2 x)) : ℝ) * bpow fmt2 (cexp fmt2 x)
    calc x = (x / bpow fmt2 (cexp fmt2 x)) * bpow fmt2 (cexp fmt2 x) :=
          (div_mul_cancel₀ x (bpow_ne_zero fmt2 _)).symm
      _ ≤ (zr.zrnd (x / bpow fmt2 (cexp fmt2 x)) : ℝ) * bpow fmt2 (cexp fmt2 x) :=
          mul_le_mul_of_nonneg_right (hdir _) (bpow_pos fmt2 _).le
  have h1 : roundGeneric zr fmt1 x ≤ roundGeneric zr fmt1 y := hmon hy_ge
  have h_r1_repr2 : isRepresentable fmt2 (roundGeneric zr fmt1 x) :=
    isRepresentable_of_refines href (roundGeneric_isRepresentable zr fmt1 x)
  have h_fixed : roundGeneric zr fmt2 (roundGeneric zr fmt1 x) = roundGeneric zr fmt1 x :=
    roundGeneric_repr_fixed zr fmt2 h_r1_repr2
  have h_r1_ge : x ≤ roundGeneric zr fmt1 x := by
    show x ≤ (zr.zrnd (x / bpow fmt1 (cexp fmt1 x)) : ℝ) * bpow fmt1 (cexp fmt1 x)
    calc x = (x / bpow fmt1 (cexp fmt1 x)) * bpow fmt1 (cexp fmt1 x) :=
          (div_mul_cancel₀ x (bpow_ne_zero fmt1 _)).symm
      _ ≤ (zr.zrnd (x / bpow fmt1 (cexp fmt1 x)) : ℝ) * bpow fmt1 (cexp fmt1 x) :=
          mul_le_mul_of_nonneg_right (hdir _) (bpow_pos fmt1 _).le
  have h2 : y ≤ roundGeneric zr fmt1 x :=
    h_fixed ▸ roundGeneric_monotone zr fmt2 h_r1_ge
  have h3 : roundGeneric zr fmt1 y ≤ roundGeneric zr fmt1 x :=
    (roundGeneric_repr_fixed zr fmt1 (roundGeneric_isRepresentable zr fmt1 x)) ▸ hmon h2
  exact le_antisymm h3 h1

/-! ## Double rounding for concrete directed modes -/

private theorem zrndDN_isDirectedDN : zrndDN.isDirectedDN :=
  fun y => by exact_mod_cast Int.floor_le y

private theorem zrndUP_isDirectedUP : zrndUP.isDirectedUP :=
  fun y => by exact_mod_cast Int.le_ceil y

/-- Double rounding for roundDN. -/
theorem double_roundDN {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundDN fmt1 (roundDN fmt2 x) = roundDN fmt1 x := by
  have := double_roundGeneric_of_directedDN zrndDN href zrndDN_isDirectedDN
    (roundGeneric_monotone zrndDN fmt1) x
  simp only [← roundDN_eq_generic] at this; exact this

/-- Double rounding for roundUP. -/
theorem double_roundUP {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundUP fmt1 (roundUP fmt2 x) = roundUP fmt1 x := by
  have := double_roundGeneric_of_directedUP zrndUP href zrndUP_isDirectedUP
    (roundGeneric_monotone zrndUP fmt1) x
  simp only [← roundUP_eq_generic] at this; exact this

/-- Double rounding for roundTZ. -/
theorem double_roundTZ {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundTZ fmt1 (roundTZ fmt2 x) = roundTZ fmt1 x := by
  by_cases hx : 0 ≤ x
  · rw [← roundDN_eq_roundTZ_nonneg fmt1 (roundTZ_nonneg fmt2 hx),
        ← roundDN_eq_roundTZ_nonneg fmt2 hx,
        ← roundDN_eq_roundTZ_nonneg fmt1 hx]
    exact double_roundDN href x
  · push Not at hx
    have h0 : 0 ≤ -x := by linarith
    have h1 : roundTZ fmt2 x = -(roundTZ fmt2 (-x)) := by linarith [roundTZ_neg fmt2 x]
    have h2 : roundTZ fmt1 x = -(roundTZ fmt1 (-x)) := by linarith [roundTZ_neg fmt1 x]
    rw [h1, h2, roundTZ_neg fmt1]; congr 1
    rw [← roundDN_eq_roundTZ_nonneg fmt1 (roundTZ_nonneg fmt2 h0),
        ← roundDN_eq_roundTZ_nonneg fmt2 h0,
        ← roundDN_eq_roundTZ_nonneg fmt1 h0]
    exact double_roundDN href (-x)

/-! ## Sandwich and cexp lemmas -/

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

/-! ## Double rounding for roundNNE -/

/-- When both formats share the same cexp, roundNNE coincides. -/
theorem roundNNE_eq_of_same_cexp {fmt1 fmt2 : FloatFormat} (hβ : fmt1.β = fmt2.β)
    {x : ℝ} (hcexp : cexp fmt1 x = cexp fmt2 x) :
    roundNNE fmt1 x = roundNNE fmt2 x := by
  unfold roundNNE bpow; dsimp only; rw [hcexp, hβ]

/-- Double rounding for roundNNE when cexp fmt1 x = cexp fmt2 x.
    Covers the subnormal range when both formats share the same emin. -/
theorem double_roundNNE_same_cexp {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hcexp : cexp fmt1 x = cexp fmt2 x) :
    roundNNE fmt1 (roundNNE fmt2 x) = roundNNE fmt1 x := by
  rw [← roundNNE_eq_of_same_cexp href.radix_eq hcexp]
  exact roundNNE_idempotent fmt1 x

/-- Double rounding for roundNNE when x is representable in fmt1. -/
theorem double_roundNNE_of_repr {fmt1 fmt2 : FloatFormat} (href : FormatRefines fmt1 fmt2)
    {x : ℝ} (hx : isRepresentable fmt1 x) :
    roundNNE fmt1 (roundNNE fmt2 x) = roundNNE fmt1 x := by
  have : roundNNE fmt2 x = x := roundNNE_repr_fixed fmt2 (isRepresentable_of_refines href hx)
  rw [this, roundNNE_repr_fixed fmt1 hx]

/-! ## Auxiliary lemmas for representable numbers -/

/-- Any representable z ≤ x satisfies z ≤ roundDN x. -/
theorem repr_le_roundDN' {fmt : FloatFormat} {z x : ℝ}
    (hz : isRepresentable fmt z) (hzx : z ≤ x) :
    z ≤ roundDN fmt x :=
  (roundDN_repr_fixed fmt hz) ▸ roundDN_monotone fmt hzx

/-- roundUP x ≤ any representable z ≥ x. -/
theorem roundUP_le_repr' {fmt : FloatFormat} {z x : ℝ}
    (hz : isRepresentable fmt z) (hxz : x ≤ z) :
    roundUP fmt x ≤ z :=
  (roundUP_repr_fixed fmt hz) ▸ roundUP_monotone fmt hxz

end Flean
