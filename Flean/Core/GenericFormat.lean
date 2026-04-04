import Flean.Core.GenericRound

/-!
# Flean.Core.GenericFormat

The `generic_format` predicate: a canonical characterization of representable numbers.
More flexible than `isRepresentable` for generic proofs, since it works directly
with `cexp` and `scaledMantissa` rather than existential witnesses.

Corresponds to Flocq's `generic_format` in `Flocq.Core.Generic_fmt`.
-/

namespace Flean

/-! ## Definition -/

/-- A real number is in generic format when its scaled mantissa is already an integer,
    i.e., truncation is a no-op. Equivalent to `isRepresentable` but stated canonically
    via `cexp` and `scaledMantissa`. -/
def generic_format (fmt : FloatFormat) (x : ℝ) : Prop :=
  x = (ztrunc (scaledMantissa fmt x) : ℝ) * bpow fmt (cexp fmt x)

/-! ## Basic properties -/

theorem generic_format_zero (fmt : FloatFormat) : generic_format fmt 0 := by
  unfold generic_format scaledMantissa
  rw [cexp_zero, zero_div, ztrunc_zero, Int.cast_zero, zero_mul]

/-! ## Equivalence with isRepresentable -/

/-- Every representable number is in generic format. -/
theorem generic_format_of_repr (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : generic_format fmt x := by
  unfold generic_format scaledMantissa
  have h := roundTZ_repr_fixed fmt hx
  unfold roundTZ at h; dsimp only at h
  exact h.symm

/-- Every generic_format number is representable. -/
theorem repr_of_generic_format (fmt : FloatFormat) {x : ℝ}
    (hx : generic_format fmt x) : isRepresentable fmt x := by
  unfold generic_format scaledMantissa at hx
  rw [hx]
  exact roundTZ_isRepresentable fmt x

/-- generic_format and isRepresentable are equivalent. -/
theorem generic_format_iff_repr (fmt : FloatFormat) (x : ℝ) :
    generic_format fmt x ↔ isRepresentable fmt x :=
  ⟨repr_of_generic_format fmt, generic_format_of_repr fmt⟩

/-- generic_format is equivalent to being a fixed point of roundTZ. -/
theorem generic_format_iff_roundTZ_fixed (fmt : FloatFormat) (x : ℝ) :
    generic_format fmt x ↔ roundTZ fmt x = x := by
  rw [generic_format_iff_repr]
  exact ⟨roundTZ_repr_fixed fmt, fun h => h ▸ roundTZ_isRepresentable fmt x⟩

/-! ## Closure properties -/

theorem generic_format_neg (fmt : FloatFormat) {x : ℝ}
    (hx : generic_format fmt x) : generic_format fmt (-x) := by
  rw [generic_format_iff_repr] at hx ⊢
  exact neg_isRepresentable hx

/-- Any generic rounding produces a generic_format output. -/
theorem roundGeneric_generic_format (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    generic_format fmt (roundGeneric zr fmt x) := by
  rw [generic_format_iff_repr]
  exact roundGeneric_isRepresentable zr fmt x

/-- generic_format inputs are fixed by any generic rounding. -/
theorem generic_format_round_fixed (zr : ZrndFn) (fmt : FloatFormat) {x : ℝ}
    (hx : generic_format fmt x) : roundGeneric zr fmt x = x :=
  roundGeneric_repr_fixed zr fmt (repr_of_generic_format fmt hx)

/-! ## Powers of β -/

/-- β^e is in generic format when emin ≤ e and e < emin + prec (normal range). -/
theorem generic_format_bpow (fmt : FloatFormat) {e : ℤ}
    (he_lo : fmt.emin ≤ e) (he_hi : e < fmt.emin + (fmt.prec : ℤ)) :
    generic_format fmt (bpow fmt e) := by
  rw [generic_format_iff_repr]
  refine ⟨(fmt.β : ℤ) ^ (e - fmt.emin).toNat, fmt.emin, ?_, ?_, le_refl _⟩
  · unfold bpow; push_cast
    rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]
    congr 1; rw [Int.toNat_of_nonneg (by omega)]; omega
  · rw [abs_of_nonneg (by positivity)]
    have hβ := fmt.hβ
    exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)

end Flean
