import Flean.Core.RoundProps

/-!
# Flean.Core.GenericRound

Generic rounding framework inspired by Flocq's `round_generic`.

All concrete rounding functions (roundTZ, roundDN, roundUP, roundNNE, roundNNA) share
the pattern `(Zrnd (x / bpow e)) * bpow e` where `e = cexp fmt x` and `Zrnd` is an
integer rounding function. This module abstracts over `Zrnd` and derives shared
properties once.

## Key definitions

- `ZrndFn`: axioms for an integer rounding function
- `roundGeneric`: the generic rounding function
- Unified proofs of error bounds, idempotence, representability

## Comparison with Flocq

This corresponds to Flocq's `Zrnd` record and `round_generic` function in
`Flocq.Core.Generic_fmt`. Properties proved once here replace per-mode proofs
in RoundProps, DirectedRound, NearestEven, and NearestAway.
-/

namespace Flean

/-! ## Integer rounding function axioms -/

/-- An integer rounding function: maps ℝ → ℤ satisfying key properties.
    Corresponds to Flocq's `Zrnd` record. -/
structure ZrndFn where
  /-- The integer rounding function. -/
  zrnd : ℝ → ℤ
  /-- Rounding an integer is the identity. -/
  zrnd_intCast : ∀ (n : ℤ), zrnd (n : ℝ) = n
  /-- The rounded value is within 1 of the input. -/
  zrnd_sub_abs_le : ∀ (x : ℝ), |(zrnd x : ℝ) - x| ≤ 1
  /-- Monotonicity. -/
  zrnd_monotone : Monotone (fun x : ℝ => zrnd x)

/-- A nearest-type integer rounding function: the error is at most 1/2. -/
structure ZrndNearest extends ZrndFn where
  /-- The rounding error is at most 1/2. -/
  zrnd_half : ∀ (x : ℝ), |(zrnd x : ℝ) - x| ≤ 1 / 2

/-! ## Instances for concrete rounding modes -/

private theorem ztrunc_monotone : Monotone (fun x : ℝ => ztrunc x) := by
  intro a b hab
  simp only [ztrunc]
  split_ifs with ha hb
  · exact Int.floor_le_floor hab
  · exact absurd (le_trans ha hab) hb
  · have ha' : a < 0 := not_le.mp ha
    have h1 : ⌈a⌉ ≤ 0 := Int.ceil_le.mpr (by exact_mod_cast ha'.le)
    have h2 : (0 : ℤ) ≤ ⌊b⌋ := Int.floor_nonneg.mpr (by linarith)
    linarith
  · exact Int.ceil_le_ceil hab

/-- ztrunc is a valid ZrndFn. -/
noncomputable def zrndTZ : ZrndFn where
  zrnd := ztrunc
  zrnd_intCast := ztrunc_intCast
  zrnd_sub_abs_le := fun x => (ztrunc_sub_lt_one x).le
  zrnd_monotone := ztrunc_monotone

/-- ⌊·⌋ (floor) is a valid ZrndFn. -/
noncomputable def zrndDN : ZrndFn where
  zrnd := fun x => ⌊x⌋
  zrnd_intCast := Int.floor_intCast
  zrnd_sub_abs_le := fun x => by
    have h := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    rw [abs_le]; constructor <;> linarith
  zrnd_monotone := fun _ _ h => Int.floor_le_floor h

/-- ⌈·⌉ (ceil) is a valid ZrndFn. -/
noncomputable def zrndUP : ZrndFn where
  zrnd := fun x => ⌈x⌉
  zrnd_intCast := Int.ceil_intCast
  zrnd_sub_abs_le := fun x => by
    have h := Int.le_ceil x
    have h2 := Int.ceil_lt_add_one x
    rw [abs_le]; constructor <;> linarith
  zrnd_monotone := fun _ _ h => Int.ceil_le_ceil h

private theorem nearest_monotone (f : ℝ → ℤ) (hf : ∀ x, |x - (f x : ℝ)| ≤ 1 / 2) :
    Monotone (fun x : ℝ => f x) := by
  intro a b hab
  by_contra h
  push Not at h
  have ha := hf a
  have hb := hf b
  have hfba : (f b : ℝ) + 1 ≤ (f a : ℝ) := by exact_mod_cast h
  have ⟨ha1, ha2⟩ := abs_le.mp ha
  have ⟨hb1, hb2⟩ := abs_le.mp hb
  -- From hb2: b - 1/2 ≤ f b, hfba: f b + 1 ≤ f a, ha1: -(1/2) ≤ a - f a (i.e. f a ≤ a + 1/2)
  -- Chain: b + 1/2 ≤ f b + 1 ≤ f a ≤ a + 1/2, so b ≤ a; combined with a ≤ b gives a = b,
  -- but then f a = f b since f is a function, contradicting f b + 1 ≤ f a.
  have hab_eq : a = b := le_antisymm hab (by linarith)
  have hfab : f a = f b := congr_arg f hab_eq
  linarith [show (f a : ℝ) = f b from by exact_mod_cast hfab]

/-- roundNearestEven is a valid ZrndNearest. -/
noncomputable def zrndNNE : ZrndNearest where
  zrnd := roundNearestEven
  zrnd_intCast := roundNearestEven_intCast
  zrnd_sub_abs_le := fun x => by
    have := roundNearestEven_sub_abs x; rw [abs_sub_comm] at this; linarith
  zrnd_monotone := nearest_monotone _ roundNearestEven_sub_abs
  zrnd_half := fun x => by have := roundNearestEven_sub_abs x; rwa [abs_sub_comm]

/-- roundNearestAway is a valid ZrndNearest. -/
noncomputable def zrndNNA : ZrndNearest where
  zrnd := roundNearestAway
  zrnd_intCast := roundNearestAway_intCast
  zrnd_sub_abs_le := fun x => by
    have := roundNearestAway_sub_abs x; rw [abs_sub_comm] at this; linarith
  zrnd_monotone := nearest_monotone _ roundNearestAway_sub_abs
  zrnd_half := fun x => by have := roundNearestAway_sub_abs x; rwa [abs_sub_comm]

/-! ## Generic rounding function -/

/-- Generic rounding: apply integer rounding to the scaled value. -/
noncomputable def roundGeneric (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) : ℝ :=
  (zr.zrnd (x / bpow fmt (cexp fmt x)) : ℝ) * bpow fmt (cexp fmt x)

/-! ## Connecting concrete modes to roundGeneric -/

theorem roundTZ_eq_generic (fmt : FloatFormat) (x : ℝ) :
    roundTZ fmt x = roundGeneric zrndTZ fmt x := rfl

theorem roundDN_eq_generic (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x = roundGeneric zrndDN fmt x := rfl

theorem roundUP_eq_generic (fmt : FloatFormat) (x : ℝ) :
    roundUP fmt x = roundGeneric zrndUP fmt x := rfl

theorem roundNNE_eq_generic (fmt : FloatFormat) (x : ℝ) :
    roundNNE fmt x = roundGeneric zrndNNE.toZrndFn fmt x := rfl

theorem roundNNA_eq_generic (fmt : FloatFormat) (x : ℝ) :
    roundNNA fmt x = roundGeneric zrndNNA.toZrndFn fmt x := rfl

/-! ## Generic properties -/

/-- Generic rounding fixes representable inputs. -/
theorem roundGeneric_repr_fixed (zr : ZrndFn) (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundGeneric zr fmt x = x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval]
    unfold roundGeneric; rw [cexp_zero]
    have : zr.zrnd 0 = 0 := by have := zr.zrnd_intCast 0; simp at this; exact this
    simp [this]
  · rw [hval]; unfold roundGeneric
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e)
    have hce_le : ce ≤ e := cexp_le_of_repr fmt hm_ne hm he
    have ⟨n, hn⟩ : ∃ (n : ℤ), (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (n : ℝ) := by
      refine ⟨m * (fmt.β : ℤ) ^ (e - ce).toNat, ?_⟩
      unfold bpow; push_cast; rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
      congr 2; exact (Int.toNat_of_nonneg (by omega)).symm
    rw [hn, zr.zrnd_intCast, ← hn, div_mul_cancel₀ _ (bpow_ne_zero fmt ce)]

/-- Error bound for generic rounding: |round(x) - x| ≤ bpow(cexp x). -/
theorem roundGeneric_sub_abs_le (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    |roundGeneric zr fmt x - x| ≤ bpow fmt (cexp fmt x) := by
  unfold roundGeneric
  set e := cexp fmt x
  set n := zr.zrnd (x / bpow fmt e)
  have hbe := bpow_pos fmt e
  have hsub := zr.zrnd_sub_abs_le (x / bpow fmt e)
  calc |(n : ℝ) * bpow fmt e - x|
      = |(n : ℝ) - x / bpow fmt e| * bpow fmt e := by
        rw [show (n : ℝ) * bpow fmt e - x = ((n : ℝ) - x / bpow fmt e) * bpow fmt e from by
          rw [sub_mul, div_mul_cancel₀ _ (bpow_ne_zero fmt e)]]
        rw [abs_mul, abs_of_pos hbe]
    _ ≤ 1 * bpow fmt e := by
        apply mul_le_mul_of_nonneg_right hsub hbe.le
    _ = bpow fmt e := one_mul _

/-- Generic rounding produces representable results. -/
theorem roundGeneric_isRepresentable (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundGeneric zr fmt x) := by
  -- roundGeneric is fixed on representable inputs, so round(round(x)) = round(x),
  -- meaning round(x) is representable. We prove this by direct mantissa bound.
  unfold roundGeneric
  set e := cexp fmt x
  set n := zr.zrnd (x / bpow fmt e)
  have hsub := zr.zrnd_sub_abs_le (x / bpow fmt e)
  have hsc := scaled_abs_lt fmt x
  -- From |n - y| ≤ 1 and |y| < β^prec, we get |n| < β^prec + 1.
  -- Since n is an integer and β^prec is a positive integer, |n| ≤ β^prec.
  have hn_le : |n| ≤ (fmt.β : ℤ) ^ fmt.prec := by
    have h1 : |(n : ℝ)| < (fmt.β : ℝ) ^ fmt.prec + 1 := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) (x / bpow fmt e)
      linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast show |(n : ℝ)| < ↑((fmt.β : ℤ) ^ fmt.prec + 1) from by push_cast; linarith)
  by_cases hn_lt : |n| < (fmt.β : ℤ) ^ fmt.prec
  · exact ⟨n, e, rfl, hn_lt, cexp_emin_le fmt x⟩
  · -- |n| = β^prec, need renormalization
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

/-- Generic rounding is idempotent. -/
theorem roundGeneric_idempotent (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    roundGeneric zr fmt (roundGeneric zr fmt x) = roundGeneric zr fmt x :=
  roundGeneric_repr_fixed zr fmt (roundGeneric_isRepresentable zr fmt x)

/-- Error bound for nearest-type rounding: |round(x) - x| ≤ bpow(cexp x) / 2. -/
theorem roundGenericNearest_sub_abs_le (zr : ZrndNearest) (fmt : FloatFormat) (x : ℝ) :
    |roundGeneric zr.toZrndFn fmt x - x| ≤ bpow fmt (cexp fmt x) / 2 := by
  unfold roundGeneric
  set e := cexp fmt x
  set n := zr.zrnd (x / bpow fmt e)
  have hbe := bpow_pos fmt e
  calc |(n : ℝ) * bpow fmt e - x|
      = |(n : ℝ) - x / bpow fmt e| * bpow fmt e := by
        rw [show (n : ℝ) * bpow fmt e - x = ((n : ℝ) - x / bpow fmt e) * bpow fmt e from by
          rw [sub_mul, div_mul_cancel₀ _ (bpow_ne_zero fmt e)]]
        rw [abs_mul, abs_of_pos hbe]
    _ ≤ 1 / 2 * bpow fmt e := by
        apply mul_le_mul_of_nonneg_right _ hbe.le
        exact zr.zrnd_half (x / bpow fmt e)
    _ = bpow fmt (cexp fmt x) / 2 := by ring

/-- Relative error for nearest-type generic rounding. -/
theorem roundGenericNearest_error_rel (zr : ZrndNearest) (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundGeneric zr.toZrndFn fmt x - x| ≤ machineEpsilon fmt / 2 * |x| := by
  calc |roundGeneric zr.toZrndFn fmt x - x|
      ≤ bpow fmt (cexp fmt x) / 2 := roundGenericNearest_sub_abs_le zr fmt x
    _ ≤ machineEpsilon fmt / 2 * |x| := by
        have h := bpow_cexp_le_machineEpsilon_mul_abs fmt hx; linarith

/-- Any ZrndFn satisfies zrnd y ≤ ⌈y⌉: follows from monotonicity + integer fixing. -/
private theorem zrnd_le_ceil (zr : ZrndFn) (y : ℝ) : zr.zrnd y ≤ ⌈y⌉ := by
  have h := zr.zrnd_monotone (Int.le_ceil y)
  simp only [zr.zrnd_intCast] at h; exact h

/-- Any ZrndFn satisfies ⌊y⌋ ≤ zrnd y: follows from monotonicity + integer fixing. -/
private theorem floor_le_zrnd (zr : ZrndFn) (y : ℝ) : ⌊y⌋ ≤ zr.zrnd y := by
  have h := zr.zrnd_monotone (Int.floor_le y)
  simp only [zr.zrnd_intCast] at h; exact h

/-- Generic rounding is bounded above by roundUP. -/
theorem roundGeneric_le_roundUP (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    roundGeneric zr fmt x ≤ roundUP fmt x := by
  unfold roundGeneric roundUP; dsimp only
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast zrnd_le_ceil zr (x / bpow fmt (cexp fmt x))

/-- Generic rounding is bounded below by roundDN. -/
theorem roundGeneric_ge_roundDN (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt x ≤ roundGeneric zr fmt x := by
  unfold roundGeneric roundDN; dsimp only
  apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt _).le
  exact_mod_cast floor_le_zrnd zr (x / bpow fmt (cexp fmt x))

/-- Generic rounding to a RoundingFn. -/
noncomputable def roundGenericFn (zr : ZrndFn) (fmt : FloatFormat)
    (hmon : Monotone (roundGeneric zr fmt)) : RoundingFn fmt where
  round := roundGeneric zr fmt
  rounds_to_repr := roundGeneric_isRepresentable zr fmt
  idempotent := roundGeneric_idempotent zr fmt
  monotone := hmon

/-! ## Scaled mantissa -/

/-- The scaled mantissa: x divided by β^(cexp x). Corresponds to Flocq's `scaled_mantissa`. -/
noncomputable def scaledMantissa (fmt : FloatFormat) (x : ℝ) : ℝ :=
  x / bpow fmt (cexp fmt x)

theorem scaledMantissa_abs_lt (fmt : FloatFormat) (x : ℝ) :
    |scaledMantissa fmt x| < (fmt.β : ℝ) ^ fmt.prec :=
  scaled_abs_lt fmt x

theorem roundGeneric_eq_scaledMantissa (zr : ZrndFn) (fmt : FloatFormat) (x : ℝ) :
    roundGeneric zr fmt x = (zr.zrnd (scaledMantissa fmt x) : ℝ) * bpow fmt (cexp fmt x) := rfl

/-! ## Sandwich bounds (round_DN_or_UP) -/

/-- Any ZrndFn rounds above the floor. -/
theorem ZrndFn.zrnd_ge_floor (zr : ZrndFn) (x : ℝ) : ⌊x⌋ ≤ zr.zrnd x :=
  floor_le_zrnd zr x

/-- Any ZrndFn rounds below the ceiling. -/
theorem ZrndFn.zrnd_le_ceil' (zr : ZrndFn) (x : ℝ) : zr.zrnd x ≤ ⌈x⌉ :=
  zrnd_le_ceil zr x

/-! ## Nonzero preservation -/

/-- If |x| ≥ bpow(cexp x), then roundGeneric x ≠ 0. -/
theorem roundGeneric_ne_zero (zr : ZrndFn) (fmt : FloatFormat) {x : ℝ}
    (hx : bpow fmt (cexp fmt x) ≤ |x|) : roundGeneric zr fmt x ≠ 0 := by
  unfold roundGeneric
  apply mul_ne_zero _ (bpow_ne_zero fmt _)
  -- Show the integer part is nonzero.
  set y := x / bpow fmt (cexp fmt x)
  have hbp := bpow_pos fmt (cexp fmt x)
  -- |y| ≥ 1
  have hy_abs : 1 ≤ |y| := by
    rw [abs_div, abs_of_pos hbp]
    rwa [le_div_iff₀ hbp, one_mul]
  intro h
  have hzero : zr.zrnd y = 0 := by exact_mod_cast h
  by_cases hpos : 0 ≤ y
  · -- y ≥ 0, so y ≥ 1
    have hy1 : 1 ≤ y := by rwa [abs_of_nonneg hpos] at hy_abs
    have hge : (1 : ℤ) ≤ zr.zrnd y := by
      have h1 : zr.zrnd ((1 : ℤ) : ℝ) ≤ zr.zrnd y := zr.zrnd_monotone (by exact_mod_cast hy1)
      rwa [zr.zrnd_intCast] at h1
    omega
  · -- y < 0, so y ≤ -1
    have hneg : y < 0 := not_le.mp hpos
    have hy1 : y ≤ -1 := by
      have := abs_of_neg hneg; rw [this] at hy_abs; linarith
    have hle : zr.zrnd y ≤ -1 := by
      have h1 : zr.zrnd y ≤ zr.zrnd ((-1 : ℤ) : ℝ) := zr.zrnd_monotone (by exact_mod_cast hy1)
      rwa [zr.zrnd_intCast] at h1
    omega

end Flean
