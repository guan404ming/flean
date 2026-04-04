import Flean.Core.GenericFormat
import Flean.Core.DirectedRound
import Flean.Core.NearestEven
import Flean.Core.RoundRound
import Flean.Core.DoubleRound

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

/-- The main theorem: round-to-nearest-even after round-to-odd equals
    direct round-to-nearest-even. This avoids double rounding issues. -/
theorem roundNNE_roundOdd {fmt1 fmt2 : FloatFormat}
    (href : FormatRefines fmt1 fmt2) (x : ℝ) :
    roundNNE fmt1 (roundOdd fmt2 x) = roundNNE fmt1 x := by
  sorry

end Flean
