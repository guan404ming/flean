import Flean.Core.Rounding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Flean.Core.RoundProps

Concrete rounding functions and proofs of their properties.
-/

namespace Flean

/-! ## Helper lemmas about the radix β -/

theorem FloatFormat.β_pos (fmt : FloatFormat) : (0 : ℝ) < (fmt.β : ℝ) := by
  have h := fmt.hβ; exact Nat.cast_pos.mpr (by omega)

theorem FloatFormat.β_ne_zero (fmt : FloatFormat) : (fmt.β : ℝ) ≠ 0 :=
  ne_of_gt fmt.β_pos

theorem FloatFormat.β_one_lt (fmt : FloatFormat) : (1 : ℝ) < (fmt.β : ℝ) := by
  have : 1 < fmt.β := by have := fmt.hβ; omega
  exact_mod_cast this

/-! ## Representability lemmas -/

theorem zero_isRepresentable (fmt : FloatFormat) : isRepresentable fmt 0 := by
  refine ⟨0, fmt.emin, by simp, ?_, le_refl _⟩
  simp; exact_mod_cast pow_pos (show 0 < fmt.β from by have := fmt.hβ; omega) fmt.prec

theorem neg_isRepresentable {fmt : FloatFormat} {x : ℝ}
    (hx : isRepresentable fmt x) : isRepresentable fmt (-x) := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  exact ⟨-m, e, by rw [hval]; push_cast; ring, by rwa [abs_neg], he⟩

/-! ## Power of β -/

noncomputable def bpow (fmt : FloatFormat) (e : ℤ) : ℝ :=
  (fmt.β : ℝ) ^ e

theorem bpow_pos (fmt : FloatFormat) (e : ℤ) : 0 < bpow fmt e :=
  zpow_pos fmt.β_pos e

theorem bpow_ne_zero (fmt : FloatFormat) (e : ℤ) : bpow fmt e ≠ 0 :=
  ne_of_gt (bpow_pos fmt e)

/-! ## Truncation toward zero -/

noncomputable def ztrunc (x : ℝ) : ℤ :=
  if x ≥ 0 then ⌊x⌋ else ⌈x⌉

theorem ztrunc_zero : ztrunc 0 = 0 := by
  simp [ztrunc, Int.floor_zero]

theorem ztrunc_cast_abs_le (y : ℝ) : |(ztrunc y : ℝ)| ≤ |y| := by
  unfold ztrunc
  split_ifs with hy
  · have hf_nn : (0 : ℤ) ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy
    rw [abs_of_nonneg (by exact_mod_cast hf_nn : (0 : ℝ) ≤ (⌊y⌋ : ℝ)),
        abs_of_nonneg hy]
    exact Int.floor_le y
  · have hy' : y < 0 := lt_of_not_ge hy
    have hc_np : ⌈y⌉ ≤ 0 := Int.ceil_le.mpr (by exact_mod_cast le_of_lt hy')
    rw [abs_of_nonpos (by exact_mod_cast hc_np : (⌈y⌉ : ℝ) ≤ (0 : ℝ)),
        abs_of_neg hy']
    linarith [Int.le_ceil y]

/-- ztrunc of an integer is itself. -/
theorem ztrunc_intCast (n : ℤ) : ztrunc (n : ℝ) = n := by
  unfold ztrunc
  split_ifs with h
  · exact Int.floor_intCast n
  · exact Int.ceil_intCast n

theorem ztrunc_nonneg {y : ℝ} (hy : 0 ≤ y) : (0 : ℤ) ≤ ztrunc y := by
  unfold ztrunc; rw [if_pos hy]; exact Int.floor_nonneg.mpr hy

theorem ztrunc_neg (y : ℝ) : ztrunc (-y) = -ztrunc y := by
  unfold ztrunc
  by_cases hy : 0 ≤ y
  · by_cases hy0 : y = 0
    · subst hy0; simp
    · have : ¬(0 ≤ -y) := by linarith [lt_of_le_of_ne hy (Ne.symm hy0)]
      rw [if_pos hy, if_neg this]; exact Int.ceil_neg
  · have : 0 ≤ -y := by linarith [not_le.mp hy]
    rw [if_neg hy, if_pos this]; exact Int.floor_neg

/-! ## Canonical exponent -/

noncomputable def cexp (fmt : FloatFormat) (x : ℝ) : ℤ :=
  if x = 0 then fmt.emin
  else max fmt.emin (⌊Real.log |x| / Real.log (fmt.β : ℝ)⌋ - (fmt.prec : ℤ) + 1)

theorem cexp_zero (fmt : FloatFormat) : cexp fmt 0 = fmt.emin := by
  simp [cexp]

theorem cexp_emin_le (fmt : FloatFormat) (x : ℝ) : fmt.emin ≤ cexp fmt x := by
  unfold cexp; split
  · exact le_refl _
  · exact le_max_left _ _

theorem cexp_le_cexp_of_abs_le (fmt : FloatFormat) {x y : ℝ} (hxy : |x| ≤ |y|) :
    cexp fmt x ≤ cexp fmt y := by
  unfold cexp
  by_cases hx : x = 0
  · simp [hx]; split
    · exact le_refl _
    · exact le_max_left _ _
  · by_cases hy : y = 0
    · have : |x| = 0 := le_antisymm (by rwa [hy, abs_zero] at hxy) (abs_nonneg x)
      exact absurd (abs_eq_zero.mp this) hx
    · simp only [hx, hy, ite_false]
      apply max_le_max_left
      have hlogβ : 0 < Real.log ↑fmt.β := Real.log_pos fmt.β_one_lt
      have : Real.log |x| ≤ Real.log |y| :=
        Real.log_le_log (abs_pos.mpr hx) hxy
      have : Real.log |x| / Real.log ↑fmt.β ≤ Real.log |y| / Real.log ↑fmt.β :=
        div_le_div_of_nonneg_right this hlogβ.le
      linarith [Int.floor_le_floor this]

/-! ## Rounding Logic -/

/-- Truncate to zero -/
noncomputable def roundTZ (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e

/-- Round toward positive infinity -/
noncomputable def roundUP (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (⌈x / bpow fmt e⌉ : ℝ) * bpow fmt e

/-- Round toward negative infinity -/
noncomputable def roundDN (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (⌊x / bpow fmt e⌋ : ℝ) * bpow fmt e

/-- Round to nearest integer with ties to even. -/
noncomputable def roundNearestEven (x : ℝ) : ℤ :=
  let floor_x := ⌊x⌋
  let rem := x - floor_x
  if rem < 1/2 then floor_x
  else if rem > 1/2 then floor_x + 1
  else -- Tie: rem = 1/2
    if floor_x % 2 == 0 then floor_x else floor_x + 1

/-- Round to nearest ties to even -/
noncomputable def roundNNE (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (roundNearestEven (x / bpow fmt e) : ℝ) * bpow fmt e

/-- Round to nearest integer with ties away from zero. -/
noncomputable def roundNearestAway (x : ℝ) : ℤ :=
  if x ≥ 0 then ⌊x + 1/2⌋ else ⌈x - 1/2⌉

/-- Round to nearest ties away from zero -/
noncomputable def roundNNA (fmt : FloatFormat) (x : ℝ) : ℝ :=
  let e := cexp fmt x
  (roundNearestAway (x / bpow fmt e) : ℝ) * bpow fmt e

/-- Generic rounding based on mode -/
noncomputable def round (fmt : FloatFormat) (mode : RoundingMode) (x : ℝ) : ℝ :=
  match mode with
  | .roundTowardZero => roundTZ fmt x
  | .roundTowardPositive => roundUP fmt x
  | .roundTowardNegative => roundDN fmt x
  | .roundNearestTiesToEven => roundNNE fmt x
  | .roundNearestTiesAway => roundNNA fmt x

/-! ## Properties -/

theorem roundTZ_zero (fmt : FloatFormat) : roundTZ fmt 0 = 0 := by
  simp [roundTZ, cexp_zero, ztrunc_zero, bpow]

theorem scaled_abs_lt (fmt : FloatFormat) (x : ℝ) :
    |x / bpow fmt (cexp fmt x)| < (fmt.β : ℝ) ^ fmt.prec := by
  by_cases hx : x = 0
  · subst hx; simp [bpow, cexp_zero]; exact pow_pos fmt.β_pos _
  · have hx_pos : 0 < |x| := abs_pos.mpr hx
    have hlogβ : 0 < Real.log (fmt.β : ℝ) := Real.log_pos fmt.β_one_lt
    set e := cexp fmt x
    have he_ge : (⌊Real.log |x| / Real.log ↑fmt.β⌋ - (fmt.prec : ℤ) + 1) ≤ e := by
      show _ ≤ cexp fmt x; unfold cexp; rw [if_neg hx]; exact le_max_right _ _
    have hlogbx_lt : Real.log |x| / Real.log ↑fmt.β < (e : ℝ) + (fmt.prec : ℝ) := by
      have h1 := Int.lt_floor_add_one (Real.log |x| / Real.log ↑fmt.β)
      have h2 : (⌊Real.log |x| / Real.log ↑fmt.β⌋ : ℝ) + 1 ≤ (e : ℝ) + (fmt.prec : ℝ) := by
        norm_cast; have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
        omega
      linarith
    have h_log : Real.log |x| < ((e : ℝ) + (fmt.prec : ℝ)) * Real.log ↑fmt.β :=
      (div_lt_iff₀ hlogβ).mp hlogbx_lt
    have hβep_pos : (0 : ℝ) < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := zpow_pos fmt.β_pos _
    have hx_lt : |x| < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
      rw [← Real.log_lt_log_iff hx_pos hβep_pos, Real.log_zpow]
      convert h_log using 1; push_cast; ring
    rw [abs_div, abs_of_pos (bpow_pos fmt e), div_lt_iff₀ (bpow_pos fmt e)]
    calc |x| < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := hx_lt
      _ = (fmt.β : ℝ) ^ fmt.prec * bpow fmt e := by
          unfold bpow; rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]; congr 1; ring

theorem roundTZ_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundTZ fmt x) := by
  unfold roundTZ
  refine ⟨ztrunc (x / bpow fmt (cexp fmt x)), cexp fmt x, rfl, ?_, cexp_emin_le fmt x⟩
  have h := lt_of_le_of_lt (ztrunc_cast_abs_le _) (scaled_abs_lt fmt x)
  exact_mod_cast h

theorem roundTZ_le_abs (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x| ≤ |x| := by
  unfold roundTZ; set e := cexp fmt x
  calc |(ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e|
      = |(ztrunc (x / bpow fmt e) : ℝ)| * |bpow fmt e| := abs_mul _ _
    _ = |(ztrunc (x / bpow fmt e) : ℝ)| * bpow fmt e := by rw [abs_of_pos (bpow_pos fmt e)]
    _ ≤ |x / bpow fmt e| * bpow fmt e := mul_le_mul_of_nonneg_right (ztrunc_cast_abs_le _) (bpow_pos fmt e).le
    _ = |x| := by rw [abs_div, abs_of_pos (bpow_pos fmt e)]; exact div_mul_cancel₀ _ (bpow_ne_zero fmt e)

theorem cexp_le_of_repr (fmt : FloatFormat) {m : ℤ} {e : ℤ}
    (hm_ne : m ≠ 0) (hm : |m| < (fmt.β ^ fmt.prec : ℤ)) (he : fmt.emin ≤ e) :
    cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e) ≤ e := by
  have hx_ne : (m : ℝ) * (fmt.β : ℝ) ^ e ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hm_ne) (zpow_ne_zero _ fmt.β_ne_zero)
  unfold cexp; rw [if_neg hx_ne]
  refine max_le he ?_
  have hlogβ : 0 < Real.log (fmt.β : ℝ) := Real.log_pos fmt.β_one_lt
  have hx_pos : 0 < |(m : ℝ) * (fmt.β : ℝ) ^ e| := abs_pos.mpr hx_ne
  have hx_lt : |(m : ℝ) * (fmt.β : ℝ) ^ e| < (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
    rw [abs_mul, abs_of_pos (zpow_pos fmt.β_pos e)]
    calc |(m : ℝ)| * (fmt.β : ℝ) ^ e
        < (fmt.β : ℝ) ^ (fmt.prec : ℤ) * (fmt.β : ℝ) ^ e :=
          mul_lt_mul_of_pos_right (by exact_mod_cast hm) (zpow_pos fmt.β_pos e)
      _ = (fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec) := by
          rw [← zpow_add₀ fmt.β_ne_zero]; ring_nf
  have h_logb : Real.log |(m : ℝ) * (fmt.β : ℝ) ^ e| / Real.log ↑fmt.β <
      (e : ℝ) + (fmt.prec : ℝ) := by
    rw [div_lt_iff₀ hlogβ]
    calc Real.log |(m : ℝ) * (fmt.β : ℝ) ^ e|
        < Real.log ((fmt.β : ℝ) ^ ((e : ℤ) + ↑fmt.prec)) := Real.log_lt_log hx_pos hx_lt
      _ = ((e : ℝ) + ↑fmt.prec) * Real.log ↑fmt.β := by
          rw [Real.log_zpow]; push_cast; ring
  have : ⌊Real.log |(m : ℝ) * (fmt.β : ℝ) ^ e| / Real.log ↑fmt.β⌋ < e + (fmt.prec : ℤ) := by
    apply Int.floor_lt.mpr; exact_mod_cast h_logb
  omega

theorem roundTZ_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundTZ fmt x = x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval]; exact roundTZ_zero fmt
  · rw [hval]; unfold roundTZ; dsimp only
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e)
    have hce_le : ce ≤ e := cexp_le_of_repr fmt hm_ne hm he
    have ⟨n, hn⟩ : ∃ (n : ℤ), (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (n : ℝ) := by
      refine ⟨m * (fmt.β : ℤ) ^ (e - ce).toNat, ?_⟩
      unfold bpow; push_cast; rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
      congr 2; exact (Int.toNat_of_nonneg (by omega)).symm
    rw [hn, ztrunc_intCast, ← hn, div_mul_cancel₀ _ (bpow_ne_zero fmt ce)]

theorem roundTZ_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundTZ fmt (roundTZ fmt x) = roundTZ fmt x :=
  roundTZ_repr_fixed fmt (roundTZ_isRepresentable fmt x)

theorem roundTZ_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ roundTZ fmt x := by
  unfold roundTZ; dsimp only
  exact mul_nonneg (by exact_mod_cast ztrunc_nonneg (div_nonneg hx (bpow_pos fmt _).le)) (bpow_pos fmt _).le

theorem roundTZ_neg (fmt : FloatFormat) (x : ℝ) :
    roundTZ fmt (-x) = -roundTZ fmt x := by
  unfold roundTZ; dsimp only
  have : cexp fmt (-x) = cexp fmt x := by unfold cexp; simp [abs_neg]
  rw [this, neg_div, ztrunc_neg, Int.cast_neg, neg_mul]

theorem ztrunc_nonpos {y : ℝ} (hy : y ≤ 0) : ztrunc y ≤ 0 := by
  unfold ztrunc
  by_cases h : y ≥ 0
  · have : y = 0 := le_antisymm hy h
    rw [if_pos h, this]; simp
  · rw [if_neg h]; exact Int.ceil_le.mpr (by exact_mod_cast hy)

theorem roundTZ_nonpos (fmt : FloatFormat) {x : ℝ} (hx : x ≤ 0) :
    roundTZ fmt x ≤ 0 := by
  unfold roundTZ; dsimp only
  exact mul_nonpos_of_nonpos_of_nonneg
    (by exact_mod_cast ztrunc_nonpos (div_nonpos_of_nonpos_of_nonneg hx (bpow_pos fmt _).le))
    (bpow_pos fmt _).le

theorem ztrunc_sub_lt_one (y : ℝ) : |(ztrunc y : ℝ) - y| < 1 := by
  unfold ztrunc
  split_ifs with hy
  · rw [abs_of_nonpos (by linarith [Int.floor_le y])]; linarith [Int.lt_floor_add_one y]
  · rw [abs_of_nonneg (by linarith [Int.le_ceil y])]; linarith [Int.ceil_lt_add_one y]

theorem roundTZ_error_abs (fmt : FloatFormat) (x : ℝ) :
    |roundTZ fmt x - x| < bpow fmt (cexp fmt x) := by
  unfold roundTZ; dsimp only; set e := cexp fmt x
  have h1 : (ztrunc (x / bpow fmt e) : ℝ) * bpow fmt e - x =
      ((ztrunc (x / bpow fmt e) : ℝ) - x / bpow fmt e) * bpow fmt e := by
    rw [sub_mul, div_mul_cancel₀ x (bpow_ne_zero fmt e)]
  rw [h1, abs_mul, abs_of_pos (bpow_pos fmt e)]
  calc |(ztrunc (x / bpow fmt e) : ℝ) - x / bpow fmt e| * bpow fmt e
      < 1 * bpow fmt e := mul_lt_mul_of_pos_right (ztrunc_sub_lt_one _) (bpow_pos fmt e)
    _ = bpow fmt e := one_mul _

theorem cexp_neg (fmt : FloatFormat) (x : ℝ) : cexp fmt (-x) = cexp fmt x := by
  unfold cexp; simp [abs_neg, neg_eq_zero]

theorem repr_le_roundTZ_nonneg (fmt : FloatFormat) {r y : ℝ}
    (hr : isRepresentable fmt r) (hr0 : 0 ≤ r) (hry : r ≤ y) :
    r ≤ roundTZ fmt y := by
  obtain ⟨m, f, hval, hm, hf⟩ := hr
  have hy0 : 0 ≤ y := le_trans hr0 hry
  set e := cexp fmt y
  by_cases hfe : e ≤ f
  · -- Case f ≥ e: r is a multiple of bpow fmt e
    set n := m * (fmt.β : ℤ) ^ (f - e).toNat
    have hr_eq : r = (n : ℝ) * bpow fmt e := by
      simp only [n]; rw [hval]; unfold bpow
      push_cast; rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]
      have hfe' : (0 : ℤ) ≤ f - e := Int.sub_nonneg.mpr hfe
      congr 1; rw [Int.toNat_of_nonneg hfe']; ring_nf
    unfold roundTZ; dsimp only
    rw [show ztrunc (y / bpow fmt e) = ⌊y / bpow fmt e⌋ from by
      unfold ztrunc; exact if_pos (div_nonneg hy0 (bpow_pos fmt e).le)]
    rw [hr_eq]; apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt e).le
    exact_mod_cast Int.le_floor.mpr ((le_div_iff₀ (bpow_pos fmt e)).mpr (hr_eq.symm ▸ hry))
  · -- Case f < e: r has smaller exponent, show r ≤ ⌊y/β^e⌋ * β^e
    push Not at hfe
    have hy_ne : y ≠ 0 := by
      intro h; subst h
      have : (e : ℤ) = fmt.emin := cexp_zero fmt; linarith
    have hy_pos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy_ne)
    -- Since emin ≤ f < e, e > emin, so cexp took the floor branch
    have he_gt_emin : fmt.emin < e := lt_of_le_of_lt hf hfe
    have he_max : e = max fmt.emin (⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) := by
      show cexp fmt y = _; unfold cexp; rw [if_neg hy_ne]
    have he_floor : (e : ℤ) = ⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1 := by
      rw [he_max]
      cases max_choice fmt.emin (⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) with
      | inl h => rw [h] at he_max; linarith
      | inr h => exact h
    have hlogβ : 0 < Real.log ↑fmt.β := Real.log_pos fmt.β_one_lt
    have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
    -- β^e ≤ y
    have hbpow_le : bpow fmt e ≤ y := by
      have h1 : (e : ℝ) ≤ Real.log |y| / Real.log ↑fmt.β := by
        calc (e : ℝ) ≤ (e : ℝ) + ((fmt.prec : ℝ) - 1) := by
              linarith [show (1 : ℝ) ≤ (fmt.prec : ℝ) from by exact_mod_cast hp]
          _ = (⌊Real.log |y| / Real.log ↑fmt.β⌋ : ℝ) := by rw [he_floor]; push_cast; ring
          _ ≤ Real.log |y| / Real.log ↑fmt.β := Int.floor_le _
      rw [abs_of_pos hy_pos] at h1
      calc bpow fmt e = (fmt.β : ℝ) ^ e := rfl
        _ ≤ y := by
          rw [← Real.log_le_log_iff (zpow_pos fmt.β_pos _) hy_pos, Real.log_zpow]
          exact_mod_cast (le_div_iff₀ hlogβ).mp h1
    -- Strategy: r < β^(e+p-1) ≤ ⌊y/β^e⌋ * β^e = roundTZ y
    have hm0 : 0 ≤ m := by
      by_contra h; push Not at h
      have : r < 0 := by
        rw [hval]; exact mul_neg_of_neg_of_pos (by exact_mod_cast h) (bpow_pos fmt f)
      linarith
    have hm_lt : m < (fmt.β : ℤ) ^ fmt.prec := by rwa [abs_of_nonneg hm0] at hm
    have hfe1 : f ≤ e - 1 := Int.le_sub_one_of_lt hfe
    -- r < β^(e + p - 1)
    have hm_real : (m : ℝ) < bpow fmt ↑fmt.prec := by
      unfold bpow; push_cast [zpow_natCast]; exact_mod_cast hm_lt
    have hf_le : bpow fmt f ≤ bpow fmt (e - 1) := by
      unfold bpow; gcongr
      exact_mod_cast fmt.β_one_lt.le
    have hr_lt : r < bpow fmt (e + ↑fmt.prec - 1) := by
      rw [hval]; show (m : ℝ) * bpow fmt f < bpow fmt (e + ↑fmt.prec - 1)
      calc (m : ℝ) * bpow fmt f
          < bpow fmt ↑fmt.prec * bpow fmt f :=
            mul_lt_mul_of_pos_right hm_real (bpow_pos fmt f)
        _ ≤ bpow fmt ↑fmt.prec * bpow fmt (e - 1) :=
            mul_le_mul_of_nonneg_left hf_le (bpow_pos fmt ↑fmt.prec).le
        _ = bpow fmt (e + ↑fmt.prec - 1) := by
            unfold bpow; rw [← zpow_add₀ fmt.β_ne_zero]; congr 1; omega
    -- β^(e + p - 1) ≤ y
    have hbpow_le' : bpow fmt (e + ↑fmt.prec - 1) ≤ y := by
      have h1 : (↑(e + ↑fmt.prec - 1) : ℝ) ≤ Real.log |y| / Real.log ↑fmt.β := by
        calc (↑(e + ↑fmt.prec - 1) : ℝ)
            = (⌊Real.log |y| / Real.log ↑fmt.β⌋ : ℝ) := by
              rw [he_floor]; push_cast; ring
          _ ≤ Real.log |y| / Real.log ↑fmt.β := Int.floor_le _
      rw [abs_of_pos hy_pos] at h1
      show bpow fmt (e + ↑fmt.prec - 1) ≤ y
      calc bpow fmt (e + ↑fmt.prec - 1) = (fmt.β : ℝ) ^ (e + ↑fmt.prec - 1 : ℤ) := rfl
        _ ≤ y := by
          rw [← Real.log_le_log_iff (zpow_pos fmt.β_pos _) hy_pos, Real.log_zpow]
          exact_mod_cast (le_div_iff₀ hlogβ).mp h1
    -- roundTZ y ≥ β^(e + p - 1)
    unfold roundTZ; dsimp only
    rw [show ztrunc (y / bpow fmt e) = ⌊y / bpow fmt e⌋ from by
      unfold ztrunc; exact if_pos (div_nonneg hy0 (bpow_pos fmt e).le)]
    -- β^(p-1) ≤ ⌊y/β^e⌋ since y/β^e ≥ β^(p-1) and β^(p-1) is an integer
    have hbpow_split : bpow fmt (e + ↑fmt.prec - 1) = bpow fmt (↑fmt.prec - 1) * bpow fmt e := by
      unfold bpow; rw [← zpow_add₀ fmt.β_ne_zero]; congr 1; ring
    have hyd : bpow fmt (↑fmt.prec - 1) ≤ y / bpow fmt e := by
      rw [le_div_iff₀ (bpow_pos fmt e)]; linarith [hbpow_split]
    suffices h : bpow fmt (e + ↑fmt.prec - 1) ≤ (⌊y / bpow fmt e⌋ : ℝ) * bpow fmt e by linarith
    rw [hbpow_split]
    apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt e).le
    have hprec_sub : (↑fmt.prec - 1 : ℤ) = ↑(fmt.prec - 1 : ℕ) := by omega
    have hbpow_int : bpow fmt (↑fmt.prec - 1) = ↑((fmt.β : ℤ) ^ (fmt.prec - 1 : ℕ)) := by
      unfold bpow; rw [hprec_sub]; simp [zpow_natCast]
    rw [hbpow_int]
    exact_mod_cast Int.le_floor.mpr (hbpow_int ▸ hyd)

theorem roundTZ_monotone (fmt : FloatFormat) : Monotone (roundTZ fmt) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · -- 0 ≤ x ≤ y
    have hy : 0 ≤ y := le_trans hx hxy
    have hle : roundTZ fmt x ≤ x := by
      have := roundTZ_le_abs fmt x; rwa [abs_of_nonneg hx, abs_of_nonneg (roundTZ_nonneg fmt hx)] at this
    exact repr_le_roundTZ_nonneg fmt (roundTZ_isRepresentable fmt x)
      (roundTZ_nonneg fmt hx) (le_trans hle hxy)
  · by_cases hy : y ≤ 0
    · -- x ≤ y ≤ 0: use negation and the nonneg case
      have hny : 0 ≤ -y := by linarith
      have hnx_le : -y ≤ -x := neg_le_neg hxy
      have hle_neg : roundTZ fmt (-y) ≤ roundTZ fmt (-x) := by
        have hle' : roundTZ fmt (-y) ≤ -y := by
          have := roundTZ_le_abs fmt (-y)
          rwa [abs_of_nonneg hny, abs_of_nonneg (roundTZ_nonneg fmt hny)] at this
        exact repr_le_roundTZ_nonneg fmt (roundTZ_isRepresentable fmt (-y))
          (roundTZ_nonneg fmt hny) (le_trans hle' hnx_le)
      rw [roundTZ_neg, roundTZ_neg] at hle_neg; linarith
    · -- x < 0 < y
      exact le_trans (roundTZ_nonpos fmt (le_of_not_ge hx))
        (roundTZ_nonneg fmt (not_le.mp hy).le)

theorem roundTZ_error (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundTZ fmt x - x| ≤ machineEpsilon fmt * |x| := by
  set e := cexp fmt x
  have h_abs_err := roundTZ_error_abs fmt x
  have hx_ne : x ≠ 0 := by
    intro h; subst h; simp at hx; exact not_le.mpr (zpow_pos fmt.β_pos _) hx
  have hlogβ : 0 < Real.log ↑fmt.β := Real.log_pos fmt.β_one_lt
  have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
  -- β^(e+p-1) ≤ |x| from cexp definition
  have h_epow_le : (fmt.β : ℝ) ^ (e + (fmt.prec : ℤ) - 1) ≤ |x| := by
    have he_le : e + (fmt.prec : ℤ) - 1 ≤ ⌊Real.log |x| / Real.log ↑fmt.β⌋ := by
      have he_emin := cexp_emin_le fmt x
      by_cases hx0 : x = 0
      · exact absurd hx0 hx_ne
      · have : e = max fmt.emin (⌊Real.log |x| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) := by
          show cexp fmt x = _; unfold cexp; rw [if_neg hx0]
        cases max_choice fmt.emin (⌊Real.log |x| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) with
        | inl h =>
            rw [this, h]
            -- Need: emin + p - 1 ≤ ⌊log_β|x|⌋
            have hx_pos : 0 < |x| := abs_pos.mpr hx0
            have h_log : (fmt.emin + (fmt.prec : ℤ) - 1 : ℤ) ≤
                ⌊Real.log |x| / Real.log ↑fmt.β⌋ := by
              apply Int.le_floor.mpr
              rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one,
                  le_div_iff₀ hlogβ]
              calc ((fmt.emin : ℝ) + (fmt.prec : ℝ) - 1) * Real.log ↑fmt.β
                  = Real.log ((fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1)) := by
                    rw [Real.log_zpow]; push_cast; ring
                _ ≤ Real.log |x| :=
                    Real.log_le_log (zpow_pos fmt.β_pos _) hx
            exact h_log
        | inr h => rw [this, h]; omega
    have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
    calc (fmt.β : ℝ) ^ (e + (fmt.prec : ℤ) - 1)
        ≤ (fmt.β : ℝ) ^ ⌊Real.log |x| / Real.log ↑fmt.β⌋ :=
          zpow_le_zpow_right₀ fmt.β_one_lt.le he_le
      _ ≤ |x| := by
          rw [← Real.log_le_log_iff (zpow_pos fmt.β_pos _) hx_pos, Real.log_zpow]
          exact_mod_cast (le_div_iff₀ hlogβ).mp (Int.floor_le _)
  -- β^e = β^(1-p) * β^(e+p-1) ≤ ε * |x|
  have h_le : bpow fmt e ≤ machineEpsilon fmt * |x| := by
    unfold machineEpsilon bpow
    calc (fmt.β : ℝ) ^ e
        = (fmt.β : ℝ) ^ (1 - (fmt.prec : ℤ)) * (fmt.β : ℝ) ^ (e + (fmt.prec : ℤ) - 1) := by
          rw [← zpow_add₀ fmt.β_ne_zero]; congr 1; ring
      _ ≤ (fmt.β : ℝ) ^ (1 - (fmt.prec : ℤ)) * |x| :=
          mul_le_mul_of_nonneg_left h_epow_le (zpow_pos fmt.β_pos _).le
  linarith [h_abs_err]

noncomputable def roundTowardZeroFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundTZ fmt
  rounds_to_repr := roundTZ_isRepresentable fmt
  idempotent := roundTZ_idempotent fmt
  monotone := roundTZ_monotone fmt
  sign_preservation := roundTZ_neg fmt

end Flean
