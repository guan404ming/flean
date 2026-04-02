import Flean.Core.RoundProps

/-!
# Flean.Core.Models

Abstract floating-point models following Flocq's layered approach:
- FLX: unbounded exponent (pure precision model)
- FLT: bounded minimum exponent (gradual underflow)
- FTZ: flush-to-zero (no subnormals)
-/

namespace Flean

/-! ## FLX: Floating-point with unbounded exponent -/

/-- A real number is FLX-representable with precision p and radix β
    if x = m * β^e with |m| < β^p, with no bound on e. -/
def isFLX (β : ℕ) (prec : ℕ) (x : ℝ) : Prop :=
  ∃ (m : ℤ) (e : ℤ),
    x = (m : ℝ) * (β : ℝ) ^ e ∧
    |m| < (β ^ prec : ℤ)

theorem zero_isFLX (β : ℕ) (prec : ℕ) (hβ : β ≥ 2) : isFLX β prec 0 := by
  refine ⟨0, 0, by simp, ?_⟩
  simp; exact_mod_cast pow_pos (show 0 < β from by omega) prec

theorem neg_isFLX {β : ℕ} {prec : ℕ} {x : ℝ} (hx : isFLX β prec x) :
    isFLX β prec (-x) := by
  obtain ⟨m, e, hval, hm⟩ := hx
  exact ⟨-m, e, by rw [hval]; push_cast; ring, by rwa [abs_neg]⟩

/-- FLX is a relaxation of FLT: any representable number in a format is FLX-representable. -/
theorem isRepresentable_isFLX (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : isFLX fmt.β fmt.prec x := by
  obtain ⟨m, e, hval, hm, _⟩ := hx
  exact ⟨m, e, hval, hm⟩

/-! ## FLT: Floating-point with bounded minimum exponent (gradual underflow) -/

/-- FLT representability: same as isRepresentable, just an alias for clarity. -/
abbrev isFLT (fmt : FloatFormat) := isRepresentable fmt

/-! ## FTZ: Flush-to-zero model (no subnormals) -/

/-- A real number is FTZ-representable if it is either zero or
    representable with a "canonical" significand |m| ≥ β^(p-1). -/
def isFTZ (fmt : FloatFormat) (x : ℝ) : Prop :=
  x = 0 ∨ ∃ (m : ℤ) (e : ℤ),
    x = (m : ℝ) * (fmt.β : ℝ) ^ e ∧
    (fmt.β ^ (fmt.prec - 1) : ℤ) ≤ |m| ∧
    |m| < (fmt.β ^ fmt.prec : ℤ) ∧
    fmt.emin ≤ e

theorem zero_isFTZ (fmt : FloatFormat) : isFTZ fmt 0 := Or.inl rfl

/-- Every FTZ-representable number is also FLT-representable. -/
theorem isFTZ_isRepresentable {fmt : FloatFormat} {x : ℝ}
    (hx : isFTZ fmt x) : isRepresentable fmt x := by
  cases hx with
  | inl h => rw [h]; exact zero_isRepresentable fmt
  | inr h =>
    obtain ⟨m, e, hval, _, hm_lt, he⟩ := h
    exact ⟨m, e, hval, hm_lt, he⟩

end Flean
