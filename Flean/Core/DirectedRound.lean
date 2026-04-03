import Flean.Core.RoundProps

/-!
# Flean.Core.DirectedRound

Properties of directed rounding modes: roundDN (toward -∞) and roundUP (toward +∞).
-/

namespace Flean

/-! ## Basic bounds -/

theorem roundDN_le (fmt : FloatFormat) (x : ℝ) : roundDN fmt x ≤ x := by
  unfold roundDN; dsimp only; set e := cexp fmt x
  calc (⌊x / bpow fmt e⌋ : ℝ) * bpow fmt e
      ≤ x / bpow fmt e * bpow fmt e :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Int.floor_le _) (bpow_pos fmt e).le
    _ = x := div_mul_cancel₀ _ (bpow_ne_zero fmt e)

theorem roundUP_ge (fmt : FloatFormat) (x : ℝ) : x ≤ roundUP fmt x := by
  unfold roundUP; dsimp only; set e := cexp fmt x
  calc x = x / bpow fmt e * bpow fmt e := (div_mul_cancel₀ _ (bpow_ne_zero fmt e)).symm
    _ ≤ (⌈x / bpow fmt e⌉ : ℝ) * bpow fmt e :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Int.le_ceil _) (bpow_pos fmt e).le

theorem roundDN_zero (fmt : FloatFormat) : roundDN fmt 0 = 0 := by
  simp [roundDN, cexp_zero, bpow]

theorem roundUP_zero (fmt : FloatFormat) : roundUP fmt 0 = 0 := by
  simp [roundUP, cexp_zero, bpow]

/-! ## Duality -/

theorem roundDN_neg (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt (-x) = -roundUP fmt x := by
  unfold roundDN roundUP; dsimp only
  rw [cexp_neg, neg_div, Int.floor_neg, Int.cast_neg, neg_mul]

theorem roundUP_neg (fmt : FloatFormat) (x : ℝ) :
    roundUP fmt (-x) = -roundDN fmt x := by
  have h := roundDN_neg fmt (-x); simp only [neg_neg] at h; linarith

/-! ## Agreement with roundTZ -/

theorem roundDN_eq_roundTZ_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    roundDN fmt x = roundTZ fmt x := by
  unfold roundDN roundTZ ztrunc; dsimp only; congr 1; push_cast
  rw [if_pos (div_nonneg hx (bpow_pos fmt _).le)]

/-! ## Representability -/

theorem roundDN_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundDN fmt x) := by
  by_cases hx : 0 ≤ x
  · rw [roundDN_eq_roundTZ_nonneg fmt hx]; exact roundTZ_isRepresentable fmt x
  · -- x < 0: use duality with roundUP on -x > 0
    push Not at hx
    -- roundDN(x) = -roundUP(-x) = -(roundTZ(-x) or roundTZ(-x) + β^e)
    -- Since -x > 0, roundTZ(-x) is repr. roundDN(x) = -roundUP(-x).
    -- We need roundUP(-x) is repr for -x > 0.
    -- roundUP(-x) = ⌈(-x)/β^e⌉ * β^e where e = cexp(-x).
    -- ⌈(-x)/β^e⌉ ≤ ⌈β^p⌉ = β^p (since (-x)/β^e < β^p and β^p is integer).
    -- If ⌈(-x)/β^e⌉ < β^p: repr at e.
    -- If ⌈(-x)/β^e⌉ = β^p: repr at e+1 (renormalize).
    -- This is the roundUP edge case for positive inputs.
    -- Alternatively: -roundUP(-x) = roundDN(x), and we can show roundDN(x) is repr
    -- by showing ⌊x/β^e⌋ has |·| ≤ β^p.
    -- For x < 0: ⌊x/β^e⌋ ∈ [-β^p, -1].
    -- If > -β^p: |·| < β^p, repr at e.
    -- If = -β^p: repr at e+1.
    -- Just use: roundDN(x) = -roundUP(-x), and -x > 0, roundTZ(-x) is nonneg repr.
    -- roundUP(-x) = roundTZ(-x) + correction (0 or β^e).
    -- If correction = 0: roundUP(-x) = roundTZ(-x), repr.
    -- If correction = β^e: roundUP(-x) = roundTZ(-x) + β^e = (ztrunc((-x)/β^e) + 1) * β^e.
    --   ztrunc((-x)/β^e) < β^p, so ztrunc + 1 ≤ β^p.
    --   If < β^p: repr. If = β^p: renormalize.
    -- This is getting complex. Let me just show roundUP is repr for nonneg inputs directly.
    suffices h : isRepresentable fmt (roundUP fmt (-x)) by
      rw [show roundDN fmt x = -(roundUP fmt (-x)) from by rw [← roundDN_neg]; ring_nf]
      exact neg_isRepresentable h
    -- roundUP(-x) for -x > 0
    have hpos : 0 < -x := by linarith
    unfold roundUP; dsimp only; set e := cexp fmt (-x)
    set n := ⌈(-x) / bpow fmt e⌉
    have hn0 : 0 < n := by
      exact_mod_cast Int.ceil_pos.mpr (div_pos hpos (bpow_pos fmt e))
    have habs := scaled_abs_lt fmt (-x)
    have hn_le : n ≤ (fmt.β : ℤ) ^ fmt.prec := by
      have h1 : (-x) / bpow fmt e < (fmt.β : ℝ) ^ fmt.prec := by
        calc (-x) / bpow fmt e ≤ |(-x) / bpow fmt e| := le_abs_self _
          _ < _ := habs
      have : (n : ℝ) ≤ (-x) / bpow fmt e + 1 := by linarith [Int.ceil_lt_add_one ((-x) / bpow fmt e)]
      exact_mod_cast show n ≤ (fmt.β : ℤ) ^ fmt.prec from by
        have : (n : ℝ) < (fmt.β : ℝ) ^ fmt.prec + 1 := by linarith
        exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
    by_cases hn_lt : n < (fmt.β : ℤ) ^ fmt.prec
    · exact ⟨n, e, rfl, by rwa [abs_of_nonneg hn0.le], cexp_emin_le fmt (-x)⟩
    · -- n = β^p: renormalize
      have hn_eq : n = (fmt.β : ℤ) ^ fmt.prec := le_antisymm hn_le (not_lt.mp hn_lt)
      refine ⟨(fmt.β : ℤ) ^ (fmt.prec - 1), e + 1, ?_, ?_, by linarith [cexp_emin_le fmt (-x)]⟩
      · unfold bpow; rw [hn_eq]; push_cast [zpow_natCast]
        have hp := fmt.hprec
        conv_lhs => rw [show fmt.prec = (fmt.prec - 1) + 1 from by omega, pow_succ]
        rw [zpow_add₀ (FloatFormat.β_ne_zero fmt), zpow_one]
        ring
      · rw [abs_of_nonneg (by positivity)]
        have hp := fmt.hprec; have hβ := fmt.hβ
        exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)

theorem roundUP_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundUP fmt x) := by
  rw [show roundUP fmt x = -roundDN fmt (-x) from by rw [roundDN_neg]; ring]
  exact neg_isRepresentable (roundDN_isRepresentable fmt (-x))

/-! ## Idempotence -/

theorem roundDN_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundDN fmt x = x := by
  obtain ⟨m, e, hval, hm, he⟩ := hx
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval, roundDN_zero]
  · rw [hval]; unfold roundDN; dsimp only
    set ce := cexp fmt ((m : ℝ) * (fmt.β : ℝ) ^ e)
    have hce_le : ce ≤ e := cexp_le_of_repr fmt hm_ne hm he
    have ⟨n, hn⟩ : ∃ (n : ℤ), (m : ℝ) * (fmt.β : ℝ) ^ e / bpow fmt ce = (n : ℝ) :=
      ⟨m * (fmt.β : ℤ) ^ (e - ce).toNat, by
        unfold bpow; push_cast; rw [mul_div_assoc, ← zpow_sub₀ fmt.β_ne_zero, ← zpow_natCast]
        congr 2; exact (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hn, Int.floor_intCast, ← hn, div_mul_cancel₀ _ (bpow_ne_zero fmt ce)]

theorem roundUP_repr_fixed (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) : roundUP fmt x = x := by
  rw [show roundUP fmt x = -roundDN fmt (-x) from by rw [roundDN_neg]; ring]
  rw [roundDN_repr_fixed fmt (neg_isRepresentable hx)]; ring

theorem roundDN_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundDN fmt (roundDN fmt x) = roundDN fmt x :=
  roundDN_repr_fixed fmt (roundDN_isRepresentable fmt x)

theorem roundUP_idempotent (fmt : FloatFormat) (x : ℝ) :
    roundUP fmt (roundUP fmt x) = roundUP fmt x :=
  roundUP_repr_fixed fmt (roundUP_isRepresentable fmt x)

/-! ## Key lemma for monotonicity -/

/-- For representable r ≥ 0 with r ≥ y ≥ 0, we have roundUP(y) ≤ r.
    This is the "roundUP gives the smallest representable above" property. -/
theorem repr_ge_roundUP_nonneg (fmt : FloatFormat) {r y : ℝ}
    (hr : isRepresentable fmt r) (hr0 : 0 ≤ r) (hry : y ≤ r) (hy0 : 0 ≤ y) :
    roundUP fmt y ≤ r := by
  obtain ⟨m, f, hval, hm, hf⟩ := hr
  set e := cexp fmt y
  have hm0 : 0 ≤ m := by
    by_contra h; push Not at h
    linarith [show r < 0 from hval ▸ mul_neg_of_neg_of_pos (by exact_mod_cast h) (zpow_pos fmt.β_pos f)]
  -- Key: f ≥ e always holds (the f < e case is vacuous)
  have hfe : e ≤ f := by
    by_contra h; push Not at h
    -- f < e: then r < β^(f+p) ≤ β^(e+p-1) ≤ y (from cexp bounds), contradicting r ≥ y.
    have hfe1 : f ≤ e - 1 := Int.le_sub_one_of_lt h
    have he_gt : fmt.emin < e := lt_of_le_of_lt hf h
    -- y ≥ bpow fmt (e + ↑fmt.prec - 1) (from cexp, as in the roundTZ proof)
    -- r < bpow fmt (e + ↑fmt.prec - 1) (from m < β^p and f ≤ e-1)
    -- This contradicts y ≤ r.
    by_cases hy_eq : y = 0
    · subst hy_eq; rw [show e = fmt.emin from cexp_zero fmt] at he_gt; omega
    · have hy_pos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy_eq)
      have hlogβ := Real.log_pos fmt.β_one_lt
      have he_floor : (e : ℤ) = ⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1 := by
        have : e = max fmt.emin (⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) := by
          show cexp fmt y = _; unfold cexp; rw [if_neg hy_eq]
        cases max_choice fmt.emin (⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) with
        | inl h' => rw [this, h'] at he_gt; linarith
        | inr h' => rw [this]; exact h'
      have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
      -- y ≥ β^(e+p-1)
      have hbpow_le' : bpow fmt (e + ↑fmt.prec - 1) ≤ y := by
        have h1 : (↑(e + ↑fmt.prec - 1) : ℝ) ≤ Real.log |y| / Real.log ↑fmt.β := by
          calc (↑(e + ↑fmt.prec - 1) : ℝ)
              = (⌊Real.log |y| / Real.log ↑fmt.β⌋ : ℝ) := by rw [he_floor]; push_cast; ring
            _ ≤ _ := Int.floor_le _
        rw [abs_of_pos hy_pos] at h1
        calc bpow fmt (e + ↑fmt.prec - 1) = (fmt.β : ℝ) ^ (e + ↑fmt.prec - 1 : ℤ) := rfl
          _ ≤ y := by
            rw [← Real.log_le_log_iff (zpow_pos fmt.β_pos _) hy_pos, Real.log_zpow]
            exact_mod_cast (le_div_iff₀ hlogβ).mp h1
      -- r < β^(e+p-1) (from m < β^p and f ≤ e-1)
      have hm_real : (m : ℝ) < bpow fmt ↑fmt.prec := by
        unfold bpow; push_cast [zpow_natCast]; exact_mod_cast (abs_of_nonneg hm0 ▸ hm)
      have hf_le : bpow fmt f ≤ bpow fmt (e - 1) := by
        unfold bpow; gcongr; exact_mod_cast fmt.β_one_lt.le
      have hr_lt : r < bpow fmt (e + ↑fmt.prec - 1) := by
        rw [hval]; show (m : ℝ) * bpow fmt f < _
        calc (m : ℝ) * bpow fmt f < bpow fmt ↑fmt.prec * bpow fmt f :=
              mul_lt_mul_of_pos_right hm_real (bpow_pos fmt f)
          _ ≤ bpow fmt ↑fmt.prec * bpow fmt (e - 1) :=
              mul_le_mul_of_nonneg_left hf_le (bpow_pos fmt _).le
          _ = bpow fmt (e + ↑fmt.prec - 1) := by
              unfold bpow; rw [← zpow_add₀ fmt.β_ne_zero]; congr 1; omega
      linarith
  -- f ≥ e: r is an integer multiple of β^e
  set n := m * (fmt.β : ℤ) ^ (f - e).toNat
  have hr_eq : r = (n : ℝ) * bpow fmt e := by
    simp only [n]; rw [hval]; unfold bpow; push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (FloatFormat.β_ne_zero fmt)]
    congr 1; rw [Int.toNat_of_nonneg (Int.sub_nonneg.mpr hfe)]; ring_nf
  unfold roundUP; dsimp only
  rw [hr_eq]; apply mul_le_mul_of_nonneg_right _ (bpow_pos fmt e).le
  exact_mod_cast Int.ceil_le.mpr ((div_le_iff₀ (bpow_pos fmt e)).mpr (hr_eq.symm ▸ hry))

/-! ## Monotonicity -/

theorem roundUP_monotone (fmt : FloatFormat) : Monotone (roundUP fmt) := by
  intro x y hxy
  by_cases hx0 : 0 ≤ x
  · -- 0 ≤ x ≤ y: roundUP(y) is repr and ≥ y ≥ x ≥ 0
    exact repr_ge_roundUP_nonneg fmt (roundUP_isRepresentable fmt y)
      (le_trans hx0 (le_trans hxy (roundUP_ge fmt y)))
      (le_trans hxy (roundUP_ge fmt y)) hx0
  · push Not at hx0
    by_cases hy0 : 0 ≤ y
    · -- x < 0 ≤ y: roundUP(x) ≤ 0 ≤ roundUP(y)
      have h1 : roundUP fmt x ≤ 0 := by
        rw [show roundUP fmt x = -(roundDN fmt (-x)) from by rw [← roundUP_neg]; ring_nf]
        linarith [roundDN_eq_roundTZ_nonneg fmt (show 0 ≤ -x from by linarith),
                  roundTZ_nonneg fmt (show 0 ≤ -x from by linarith)]
      linarith [roundUP_ge fmt y]
    · -- x ≤ y < 0: use duality to nonneg case
      push Not at hy0
      -- roundUP(x) = -roundDN(-x) and roundUP(y) = -roundDN(-y)
      -- -roundDN(-x) ≤ -roundDN(-y) ⟺ roundDN(-y) ≤ roundDN(-x)
      -- -y ≤ -x, both > 0, roundDN = roundTZ on nonneg
      have h1 := roundUP_neg fmt (-x); simp only [neg_neg] at h1
      have h2 := roundUP_neg fmt (-y); simp only [neg_neg] at h2
      rw [h1, h2]
      have : roundDN fmt (-y) ≤ roundDN fmt (-x) := by
        rw [roundDN_eq_roundTZ_nonneg fmt (by linarith : 0 ≤ -y),
            roundDN_eq_roundTZ_nonneg fmt (by linarith : 0 ≤ -x)]
        exact roundTZ_monotone fmt (by linarith)
      linarith

theorem roundDN_monotone (fmt : FloatFormat) : Monotone (roundDN fmt) := by
  intro x y hxy
  have := roundUP_monotone fmt (show -y ≤ -x from by linarith)
  rw [roundUP_neg, roundUP_neg] at this; linarith

private theorem roundUP_le_roundDN_of_cexp_ne_nonneg (fmt : FloatFormat) {x y : ℝ}
    (hxy : x ≤ y) (hx0 : 0 ≤ x) (hce : cexp fmt x ≠ cexp fmt y) :
    roundUP fmt x ≤ roundDN fmt y := by
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hce_lt : cexp fmt x < cexp fmt y := lt_of_le_of_ne
    (cexp_le_cexp_of_abs_le fmt (by rwa [abs_of_nonneg hx0, abs_of_nonneg hy0])) hce
  set ex := cexp fmt x; set ey := cexp fmt y
  have hp : 1 ≤ (fmt.prec : ℤ) := by exact_mod_cast fmt.hprec
  have hy_ne : y ≠ 0 := by
    intro h; subst h; rw [show ey = fmt.emin from cexp_zero fmt] at hce_lt
    linarith [cexp_emin_le fmt x]
  have hy_pos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy_ne)
  set boundary := bpow fmt (ey + ↑fmt.prec - 1)
  -- x < boundary
  have hx_lt : x < boundary := by
    have hscaled := scaled_abs_lt fmt x
    rw [abs_div, abs_of_pos (bpow_pos fmt ex), abs_of_nonneg hx0] at hscaled
    have hx_lt_ep : x < bpow fmt (ex + ↑fmt.prec) := by
      rw [div_lt_iff₀ (bpow_pos fmt ex)] at hscaled
      have : (fmt.β : ℝ) ^ (fmt.prec : ℕ) * bpow fmt ex = bpow fmt (ex + ↑fmt.prec) := by
        unfold bpow; rw [← zpow_natCast (fmt.β : ℝ) fmt.prec, ← zpow_add₀ fmt.β_ne_zero]
        ring_nf
      linarith
    calc x < bpow fmt (ex + ↑fmt.prec) := hx_lt_ep
      _ ≤ boundary := by
          unfold bpow; exact zpow_le_zpow_right₀ fmt.β_one_lt.le (by omega)
  -- boundary is representable
  have hboundary_repr : isRepresentable fmt boundary := by
    refine ⟨(fmt.β : ℤ) ^ (fmt.prec - 1), ey, ?_, ?_, cexp_emin_le fmt y⟩
    · show boundary = ↑((fmt.β : ℤ) ^ (fmt.prec - 1)) * bpow fmt ey
      unfold boundary bpow; push_cast [zpow_natCast]
      rw [show (fmt.prec - 1 : ℕ) = (fmt.prec : ℕ) - 1 from rfl]
      rw [← zpow_natCast (fmt.β : ℝ), ← zpow_add₀ fmt.β_ne_zero]
      congr 1; omega
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast Nat.pow_lt_pow_right (by have := fmt.hβ; omega) (by have := fmt.hprec; omega)
  have h1 : roundUP fmt x ≤ boundary :=
    repr_ge_roundUP_nonneg fmt hboundary_repr (le_trans hx0 hx_lt.le) hx_lt.le hx0
  -- boundary ≤ y
  have h2 : boundary ≤ y := by
    have he_gt : fmt.emin < ey := lt_of_le_of_lt (cexp_emin_le fmt x) hce_lt
    have hlogβ := Real.log_pos fmt.β_one_lt
    have he_floor : (ey : ℤ) = ⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1 := by
      have : ey = max fmt.emin (⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) := by
        show cexp fmt y = _; unfold cexp; rw [if_neg hy_ne]
      cases max_choice fmt.emin (⌊Real.log |y| / Real.log ↑fmt.β⌋ - ↑fmt.prec + 1) with
      | inl h => rw [this, h] at he_gt; omega
      | inr h => rw [this]; exact h
    calc boundary = (fmt.β : ℝ) ^ (ey + ↑fmt.prec - 1 : ℤ) := rfl
      _ ≤ y := by
          rw [← Real.log_le_log_iff (zpow_pos fmt.β_pos _) hy_pos, Real.log_zpow]
          have : (↑(ey + ↑fmt.prec - 1) : ℝ) ≤ Real.log |y| / Real.log ↑fmt.β := by
            calc (↑(ey + ↑fmt.prec - 1) : ℝ)
                = (⌊Real.log |y| / Real.log ↑fmt.β⌋ : ℝ) := by rw [he_floor]; push_cast; ring
              _ ≤ _ := Int.floor_le _
          rw [abs_of_pos hy_pos] at this
          exact_mod_cast (le_div_iff₀ hlogβ).mp this
  have h3 : boundary ≤ roundDN fmt y := by
    rw [roundDN_eq_roundTZ_nonneg fmt hy0]
    exact repr_le_roundTZ_nonneg fmt hboundary_repr (bpow_pos fmt _).le h2
  linarith

theorem roundUP_le_roundDN_of_cexp_ne (fmt : FloatFormat) {x y : ℝ}
    (hxy : x ≤ y) (hce : cexp fmt x ≠ cexp fmt y) :
    roundUP fmt x ≤ roundDN fmt y := by
  by_cases hx0 : 0 ≤ x
  · exact roundUP_le_roundDN_of_cexp_ne_nonneg fmt hxy hx0 hce
  · push Not at hx0
    by_cases hy0 : 0 ≤ y
    · -- x < 0 ≤ y: roundUP x ≤ 0 ≤ roundDN y
      have hup_le : roundUP fmt x ≤ 0 := by
        have h := roundUP_neg fmt (-x); simp at h; rw [h]
        linarith [roundDN_le fmt (-x), roundDN_eq_roundTZ_nonneg fmt (by linarith : 0 ≤ -x),
                  roundTZ_nonneg fmt (by linarith : 0 ≤ -x)]
      have hdn_ge : 0 ≤ roundDN fmt y := by
        rw [roundDN_eq_roundTZ_nonneg fmt hy0]; exact roundTZ_nonneg fmt hy0
      linarith
    · -- x ≤ y < 0: negate
      push Not at hy0
      have hce_neg : cexp fmt (-y) ≠ cexp fmt (-x) := by rw [cexp_neg, cexp_neg]; exact hce.symm
      have h := roundUP_le_roundDN_of_cexp_ne_nonneg fmt
        (by linarith : -y ≤ -x) (by linarith : 0 ≤ -y) hce_neg
      rw [roundUP_neg, roundDN_neg] at h; linarith

/-! ## Error bounds -/

theorem roundDN_error_abs (fmt : FloatFormat) (x : ℝ) :
    |roundDN fmt x - x| < bpow fmt (cexp fmt x) := by
  unfold roundDN; dsimp only; set e := cexp fmt x
  have hb := bpow_pos fmt e
  have h1 : (⌊x / bpow fmt e⌋ : ℝ) ≤ x / bpow fmt e := Int.floor_le _
  have h2 : x / bpow fmt e < (⌊x / bpow fmt e⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have key : (⌊x / bpow fmt e⌋ : ℝ) * bpow fmt e - x =
      ((⌊x / bpow fmt e⌋ : ℝ) - x / bpow fmt e) * bpow fmt e := by
    rw [sub_mul, div_mul_cancel₀ x (bpow_ne_zero fmt e)]
  rw [key, abs_mul, abs_of_pos hb, abs_of_nonpos (by linarith)]
  calc -(↑⌊x / bpow fmt e⌋ - x / bpow fmt e) * bpow fmt e
      < 1 * bpow fmt e := by apply mul_lt_mul_of_pos_right _ hb; linarith
    _ = bpow fmt e := one_mul _

theorem roundUP_error_abs (fmt : FloatFormat) (x : ℝ) :
    |roundUP fmt x - x| < bpow fmt (cexp fmt x) := by
  have h := roundDN_error_abs fmt (-x)
  rw [roundDN_neg, cexp_neg] at h
  rwa [show -roundUP fmt x - -x = -(roundUP fmt x - x) from by ring, abs_neg] at h

theorem roundDN_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |x - roundDN fmt x| < bpow fmt (cexp fmt x) := by
  rw [show x - roundDN fmt x = -(roundDN fmt x - x) from by ring, abs_neg]
  exact roundDN_error_abs fmt x

theorem roundUP_sub_abs_le (fmt : FloatFormat) (x : ℝ) :
    |roundUP fmt x - x| < bpow fmt (cexp fmt x) :=
  roundUP_error_abs fmt x

/-! ## Relative error bounds -/

theorem roundDN_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundDN fmt x - x| ≤ machineEpsilon fmt * |x| :=
  le_trans (roundDN_error_abs fmt x).le (bpow_cexp_le_machineEpsilon_mul_abs fmt hx)

theorem roundUP_error_rel (fmt : FloatFormat) {x : ℝ}
    (hx : (fmt.β : ℝ) ^ (fmt.emin + (fmt.prec : ℤ) - 1) ≤ |x|) :
    |roundUP fmt x - x| ≤ machineEpsilon fmt * |x| :=
  le_trans (roundUP_error_abs fmt x).le (bpow_cexp_le_machineEpsilon_mul_abs fmt hx)

/-! ## RoundingFn instances -/

noncomputable def roundTowardPositiveFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundUP fmt
  rounds_to_repr := roundUP_isRepresentable fmt
  idempotent := roundUP_idempotent fmt
  monotone := roundUP_monotone fmt

noncomputable def roundTowardNegativeFn (fmt : FloatFormat) : RoundingFn fmt where
  round := roundDN fmt
  rounds_to_repr := roundDN_isRepresentable fmt
  idempotent := roundDN_idempotent fmt
  monotone := roundDN_monotone fmt

end Flean
