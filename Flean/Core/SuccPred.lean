import Flean.Core.Representable
import Flean.Core.ULP

/-!
# Flean.Core.SuccPred

Generic successor and predecessor on representable reals.

- `succFloat fmt x`: the smallest representable number strictly greater than x
  (when x is representable and non-negative).
- `predFloat fmt x`: the largest representable number strictly less than x.

For non-negative representable x: `succFloat x = x + ulp x`.
For negative representable x: `succFloat x = -(predFloat (-x))`.

Corresponds to Flocq's `succ` / `pred` in `Flocq.Core.Ulp`.
-/

namespace Flean

/-! ## Definitions -/

/-- Predecessor for positive representable numbers: x - ulp(x). -/
noncomputable def predPos (fmt : FloatFormat) (x : ℝ) : ℝ :=
  x - ulp fmt x

/-- Successor: for x ≥ 0, x + ulp(x); for x < 0, -(predPos(-x)). -/
noncomputable def succFloat (fmt : FloatFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then x + ulp fmt x
  else -(predPos fmt (-x))

/-- Predecessor: for x ≤ 0, x - ulp(x); for x > 0, predPos(x). -/
noncomputable def predFloat (fmt : FloatFormat) (x : ℝ) : ℝ :=
  if x ≤ 0 then x - ulp fmt x
  else predPos fmt x

/-! ## Basic lemmas -/

theorem predPos_eq (fmt : FloatFormat) (x : ℝ) :
    predPos fmt x = x - ulp fmt x := rfl

theorem succFloat_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    succFloat fmt x = x + ulp fmt x := by
  unfold succFloat; rw [if_pos hx]

theorem succFloat_neg (fmt : FloatFormat) {x : ℝ} (hx : x < 0) :
    succFloat fmt x = -(predPos fmt (-x)) := by
  unfold succFloat; rw [if_neg (not_le.mpr hx)]

theorem predFloat_nonpos (fmt : FloatFormat) {x : ℝ} (hx : x ≤ 0) :
    predFloat fmt x = x - ulp fmt x := by
  unfold predFloat; rw [if_pos hx]

theorem predFloat_pos (fmt : FloatFormat) {x : ℝ} (hx : 0 < x) :
    predFloat fmt x = predPos fmt x := by
  unfold predFloat; rw [if_neg (not_le.mpr hx)]

/-! ## succFloat > x -/

theorem succFloat_gt (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    x < succFloat fmt x := by
  rw [succFloat_nonneg fmt hx]
  linarith [ulp_pos fmt x]

/-! ## predFloat < x -/

theorem predFloat_lt (fmt : FloatFormat) {x : ℝ} (hx : x ≤ 0) :
    predFloat fmt x < x := by
  rw [predFloat_nonpos fmt hx]
  linarith [ulp_pos fmt x]

/-! ## Symmetry: succFloat x = -predFloat(-x) for x ≥ 0 -/

theorem succFloat_eq_neg_predFloat_neg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) :
    succFloat fmt x = -(predFloat fmt (-x)) := by
  rw [succFloat_nonneg fmt hx, predFloat_nonpos fmt (neg_nonpos.mpr hx)]
  unfold ulp; rw [cexp_neg]; ring

theorem predFloat_eq_neg_succFloat_neg (fmt : FloatFormat) {x : ℝ} (hx : x ≤ 0) :
    predFloat fmt x = -(succFloat fmt (-x)) := by
  rw [predFloat_nonpos fmt hx, succFloat_nonneg fmt (neg_nonneg.mpr hx)]
  unfold ulp; rw [cexp_neg]; ring

/-! ## Representability of succFloat for nonneg representable inputs -/

/-- succFloat of a nonneg representable number is representable.
    Key idea: if x = m * β^e with |m| < β^p and e = cexp(x),
    then x + ulp(x) = (m + 1) * β^e, and |m + 1| ≤ β^p.
    If |m + 1| = β^p, renormalize to β^(p-1) * β^(e+1). -/
theorem succFloat_isRepresentable (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) (hx0 : 0 ≤ x) :
    isRepresentable fmt (succFloat fmt x) := by
  rw [succFloat_nonneg fmt hx0]; unfold ulp
  -- x + bpow(cexp x) is representable: direct construction
  obtain ⟨m, e, hval, hm, he⟩ := hx
  have hm0 : 0 ≤ m := by
    by_contra h; push Not at h
    have : x < 0 := hval ▸ mul_neg_of_neg_of_pos (by exact_mod_cast h) (zpow_pos fmt.β_pos e)
    linarith
  by_cases hm_ne : m = 0
  · subst hm_ne; simp at hval; rw [hval, cexp_zero, zero_add]
    refine ⟨1, fmt.emin, by unfold bpow; simp, ?_, le_refl _⟩
    simp only [abs_one]
    have : 1 < (fmt.β : ℤ) ^ fmt.prec := by
      exact_mod_cast Nat.one_lt_pow (by have := fmt.hprec; omega) (by have := fmt.hβ; omega)
    exact this
  · -- m ≠ 0, x nonneg, so m > 0
    have hm_pos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm_ne)
    set ce := cexp fmt x with hce_def
    have hce_le : ce ≤ e := by
      show cexp fmt x ≤ e; rw [hval]; exact cexp_le_of_repr fmt hm_ne hm he
    have hce_emin : fmt.emin ≤ ce := cexp_emin_le fmt x
    -- x + bpow(ce) = (m * β^(e-ce) + 1) * bpow(ce)
    set k := (e - ce).toNat
    have hk : (k : ℤ) = e - ce := Int.toNat_of_nonneg (by omega)
    set n := m * (fmt.β : ℤ) ^ k + 1
    have hn_pos : 0 < n := by positivity
    -- Value equation
    have hval' : x + bpow fmt ce = (n : ℝ) * bpow fmt ce := by
      rw [hval]; simp only [n]; unfold bpow
      have hsplit : (fmt.β : ℝ) ^ e = (fmt.β : ℝ) ^ (k : ℕ) * (fmt.β : ℝ) ^ ce := by
        rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]; congr 1; omega
      rw [hsplit]; push_cast; ring
    -- Mantissa bound: n ≤ β^p
    have hscaled : m * (fmt.β : ℤ) ^ k < (fmt.β : ℤ) ^ fmt.prec := by
      -- From hval': x + bpow(ce) = n * bpow(ce), so x = (n-1) * bpow(ce) = (m*β^k) * bpow(ce)
      -- And scaled_abs_lt gives |x / bpow(ce)| < β^p
      have hmk_real : (m : ℝ) * (fmt.β : ℝ) ^ k = x / bpow fmt ce := by
        have hsplit : (fmt.β : ℝ) ^ e = (fmt.β : ℝ) ^ (k : ℕ) * (fmt.β : ℝ) ^ ce := by
          rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]; congr 1; omega
        rw [hval, hsplit]; unfold bpow
        field_simp [zpow_ne_zero _ fmt.β_ne_zero]
      have h := scaled_abs_lt fmt x
      rw [← hmk_real, abs_of_nonneg (mul_nonneg (by exact_mod_cast hm0)
        (pow_nonneg (Nat.cast_nonneg _) _))] at h
      exact_mod_cast h
    have hn_le : n ≤ (fmt.β : ℤ) ^ fmt.prec := by omega
    by_cases hn_eq : n = (fmt.β : ℤ) ^ fmt.prec
    · -- Renormalize: n * bpow(ce) = β^(p-1) * bpow(ce+1)
      have hval'' : x + bpow fmt ce = bpow fmt (ce + (fmt.prec : ℤ)) := by
        rw [hval']; unfold bpow; push_cast [hn_eq]
        rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]; congr 1; ring
      rw [hval'']
      refine ⟨(fmt.β : ℤ) ^ (fmt.prec - 1), ce + 1, ?_, ?_, by omega⟩
      · unfold bpow; push_cast
        rw [← zpow_natCast (fmt.β : ℝ) (fmt.prec - 1), ← zpow_add₀ fmt.β_ne_zero]
        congr 1; have hp := fmt.hprec; omega
      · rw [abs_of_nonneg (by positivity)]
        have hβ := fmt.hβ; have hp := fmt.hprec
        exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)
    · -- n < β^p, use witness (n, ce) directly
      have hn_lt : n < (fmt.β : ℤ) ^ fmt.prec := lt_of_le_of_ne hn_le hn_eq
      rw [hval']
      exact ⟨n, ce, rfl, by rwa [abs_of_nonneg (by omega)], hce_emin⟩

/-! ## succFloat is the smallest representable number > x -/

/-- No representable number lies strictly between x and succFloat(x),
    for nonneg representable x. -/
theorem succFloat_least (fmt : FloatFormat) {x z : ℝ}
    (hx : isRepresentable fmt x) (hz : isRepresentable fmt z)
    (hx0 : 0 ≤ x) (hxz : x < z) :
    succFloat fmt x ≤ z := by
  rw [succFloat_nonneg fmt hx0]; unfold ulp
  -- Both x and z are integer multiples of bpow(cexp x).
  -- Their positive difference must be ≥ bpow(cexp x).
  obtain ⟨mx, ex, hxval, hmx, hex⟩ := hx
  obtain ⟨mz, ez, hzval, hmz, hez⟩ := hz
  set ce := cexp fmt x with hce_def
  have hce_lex : ce ≤ ex := by
    by_cases hmx_ne : mx = 0
    · subst hmx_ne; simp at hxval; subst hxval; simp [hce_def, cexp_zero]; exact hex
    · rw [hce_def, hxval]; exact cexp_le_of_repr fmt hmx_ne hmx hex
  have hce_lez : ce ≤ ez := by
    by_cases hmz_ne : mz = 0
    · subst hmz_ne; simp at hzval; rw [hzval] at hxz; linarith [le_trans hx0 hxz.le]
    · have : cexp fmt z ≤ ez := hzval ▸ cexp_le_of_repr fmt hmz_ne hmz hez
      exact le_trans (cexp_le_cexp_of_abs_le fmt (by
        rw [abs_of_nonneg hx0, abs_of_nonneg (le_trans hx0 hxz.le)]; exact hxz.le)) this
  -- Express x and z as integer multiples of bpow(ce)
  set nx := mx * (fmt.β : ℤ) ^ (ex - ce).toNat
  set nz := mz * (fmt.β : ℤ) ^ (ez - ce).toNat
  have hx_eq : x = (nx : ℝ) * bpow fmt ce := by
    rw [hxval]; simp only [nx]; unfold bpow
    have : (fmt.β : ℝ) ^ ex = (fmt.β : ℝ) ^ ((ex - ce).toNat : ℕ) * (fmt.β : ℝ) ^ ce := by
      rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]; congr 1; omega
    rw [this]; push_cast; ring
  have hz_eq : z = (nz : ℝ) * bpow fmt ce := by
    rw [hzval]; simp only [nz]; unfold bpow
    have : (fmt.β : ℝ) ^ ez = (fmt.β : ℝ) ^ ((ez - ce).toNat : ℕ) * (fmt.β : ℝ) ^ ce := by
      rw [← zpow_natCast, ← zpow_add₀ fmt.β_ne_zero]; congr 1; omega
    rw [this]; push_cast; ring
  -- nz > nx since z > x and bpow(ce) > 0
  have hbp := bpow_pos fmt ce
  have hnz_gt : nx < nz := by
    have h1 : (nx : ℝ) * bpow fmt ce < (nz : ℝ) * bpow fmt ce := hx_eq ▸ hz_eq ▸ hxz
    have h2 : (nx : ℝ) < (nz : ℝ) := by nlinarith
    exact_mod_cast h2
  -- So nz ≥ nx + 1, hence z ≥ x + bpow(ce)
  have hnz_ge : nx + 1 ≤ nz := by omega
  linarith [show (nz : ℝ) * bpow fmt ce ≥ ((nx : ℝ) + 1) * bpow fmt ce from by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnz_ge) hbp.le]

/-! ## Rounding and succ/pred -/

/-- For any y with x < y ≤ succFloat(x), roundDN(y) = x (when x is nonneg representable). -/
theorem roundDN_eq_of_between_succ (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hx0 : 0 ≤ x)
    (hxy : x ≤ y) (hys : y < succFloat fmt x) :
    roundDN fmt y = x := by
  have hdn_repr := roundDN_isRepresentable fmt y
  have hdn_le : roundDN fmt y ≤ y := roundDN_le fmt y
  have hx_le_dn : x ≤ roundDN fmt y := (roundDN_repr_fixed fmt hx) ▸ roundDN_monotone fmt hxy
  rw [succFloat_nonneg fmt hx0] at hys
  -- roundDN(y) is repr, x ≤ roundDN(y) ≤ y < x + ulp(x)
  -- If roundDN(y) > x, then by succFloat_least, roundDN(y) ≥ x + ulp(x), contradiction.
  by_contra h
  have hdn_gt : x < roundDN fmt y := lt_of_le_of_ne hx_le_dn (Ne.symm h)
  have := succFloat_least fmt hx hdn_repr hx0 hdn_gt
  rw [succFloat_nonneg fmt hx0] at this
  linarith

/-- For any y with predFloat(x) < y ≤ x, roundUP(y) = x (when x is nonpos representable). -/
theorem roundUP_eq_of_between_pred (fmt : FloatFormat) {x y : ℝ}
    (hx : isRepresentable fmt x) (hx0 : x ≤ 0)
    (hpx : predFloat fmt x < y) (hyx : y ≤ x) :
    roundUP fmt y = x := by
  -- Negate: -x is nonneg repr, -x ≤ -y < -x + ulp(-x) = succFloat(-x)
  have hx_neg := neg_isRepresentable hx
  have hx0_neg : 0 ≤ -x := neg_nonneg.mpr hx0
  have hxy_neg : -x ≤ -y := neg_le_neg hyx
  have hys_neg : -y < succFloat fmt (-x) := by
    rw [succFloat_nonneg fmt hx0_neg]; unfold ulp; rw [cexp_neg]
    rw [predFloat_nonpos fmt hx0] at hpx; unfold ulp at hpx; linarith
  have h := roundDN_eq_of_between_succ fmt hx_neg hx0_neg hxy_neg hys_neg
  -- roundDN(-y) = -x, and roundDN(-y) = -roundUP(y)
  have h2 := roundDN_neg fmt y
  -- h2 : roundDN(-y) = -roundUP(y), h : roundDN(-y) = -x
  linarith

/-! ## Pred representability -/

/-- predFloat of a nonpos representable number is representable. -/
theorem predFloat_isRepresentable (fmt : FloatFormat) {x : ℝ}
    (hx : isRepresentable fmt x) (hx0 : x ≤ 0) :
    isRepresentable fmt (predFloat fmt x) := by
  rw [predFloat_eq_neg_succFloat_neg fmt hx0]
  exact neg_isRepresentable
    (succFloat_isRepresentable fmt (neg_isRepresentable hx) (neg_nonneg.mpr hx0))

/-- predFloat is the largest representable number < x, for nonpos representable x. -/
theorem predFloat_greatest (fmt : FloatFormat) {x z : ℝ}
    (hx : isRepresentable fmt x) (hz : isRepresentable fmt z)
    (hx0 : x ≤ 0) (hzx : z < x) :
    z ≤ predFloat fmt x := by
  rw [predFloat_eq_neg_succFloat_neg fmt hx0]
  linarith [succFloat_least fmt (neg_isRepresentable hx) (neg_isRepresentable hz)
    (neg_nonneg.mpr hx0) (neg_lt_neg hzx)]

end Flean
