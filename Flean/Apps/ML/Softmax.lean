import Flean.Apps.ML.StableLogSumExp
import Flean.Binary.Properties

/-!
# Flean.Apps.ML.Softmax

Softmax normalization built on the stable shifted-exponential setup from
`StableLogSumExp`.
-/

namespace Flean

/-- Exact softmax-style normalization over the shifted exponential blocks. -/
noncomputable def softmaxBlocks (m : ℝ) (xss : List (List ℝ)) : List (List ℝ) :=
  let s := shiftedExpBlockSum m xss
  (shiftedExpBlocks m xss).map (fun xs => xs.map (fun x => x / s))

/-- Rounded softmax-style normalization over the shifted exponential blocks. -/
noncomputable def roundedSoftmaxBlocks (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : List (List ℝ) :=
  let s := shiftedExpBlockSum m xss
  (shiftedExpBlocks m xss).map (fun xs => xs.map (fun x => roundNNE fmt (x / s)))

/-- Sum of pointwise normalization-rounding errors across all blocks. -/
noncomputable def roundedSoftmaxErrorSum (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  let s := shiftedExpBlockSum m xss
  ((shiftedExpBlocks m xss).map
    (fun xs => (xs.map (fun x => |x / s - roundNNE fmt (x / s)|)).sum)).sum

private theorem list_sum_div {xs : List ℝ} {s : ℝ} :
    (xs.map (fun x => x / s)).sum = xs.sum / s := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.sum_cons, ih]
      ring

private theorem list_list_sum_div {xss : List (List ℝ)} {s : ℝ} :
    (xss.map (fun xs => (xs.map (fun x => x / s)).sum)).sum = (xss.map List.sum).sum / s := by
  simpa [list_sum_div] using (list_sum_div (xs := xss.map List.sum) (s := s))

private theorem map_map_sum_eq_sum_map_sum {xss : List (List ℝ)} {f : ℝ → ℝ} :
    (List.map List.sum (List.map (fun xs => List.map f xs) xss)).sum =
      (xss.map (fun xs => (xs.map f).sum)).sum := by
  induction xss with
  | nil =>
      simp
  | cons xs xss ih =>
      simp
      simpa [Function.comp] using ih

theorem softmaxBlocks_sum_one {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) (hne : BlocksNonempty xss) :
    ((softmaxBlocks m xss).map List.sum).sum = 1 := by
  let s := shiftedExpBlockSum m xss
  have hs_pos : 0 < s := shiftedExpBlockSum_pos hdom hne
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  unfold softmaxBlocks
  dsimp [s]
  have hrewrite :
      (List.map List.sum
          (List.map (fun xs => List.map (fun x => x / s) xs) (shiftedExpBlocks m xss))).sum =
        ((shiftedExpBlocks m xss).map List.sum).sum / s := by
    simpa using (list_list_sum_div (xss := shiftedExpBlocks m xss) (s := s))
  rw [hrewrite]
  calc
    ((shiftedExpBlocks m xss).map List.sum).sum / s = s / s := by
          simp [s, shiftedExpBlockSum]
    _ = 1 := by field_simp [hs_ne]

theorem roundedSoftmaxBlocks_sum_error_bound {fmt : FloatFormat}
    {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) (hne : BlocksNonempty xss) :
    |1 - ((roundedSoftmaxBlocks fmt m xss).map List.sum).sum|
      ≤ roundedSoftmaxErrorSum fmt m xss := by
  let s := shiftedExpBlockSum m xss
  have hsoftmax : ((softmaxBlocks m xss).map List.sum).sum = 1 :=
    softmaxBlocks_sum_one hdom hne
  rw [← hsoftmax]
  have hsoftmax_rewrite :
      ((softmaxBlocks m xss).map List.sum).sum =
        ((shiftedExpBlocks m xss).map List.sum).sum / s := by
    unfold softmaxBlocks
    dsimp [s]
    rw [map_map_sum_eq_sum_map_sum]
    exact list_list_sum_div (xss := shiftedExpBlocks m xss) (s := s)
  rw [hsoftmax_rewrite]
  unfold roundedSoftmaxBlocks roundedSoftmaxErrorSum
  dsimp [s]
  have hrounded_rewrite :
      (List.map List.sum
          (List.map (fun xs => List.map (fun x => roundNNE fmt (x / s)) xs)
            (shiftedExpBlocks m xss))).sum =
        ((shiftedExpBlocks m xss).map
          (fun xs => (xs.map (fun x => roundNNE fmt (x / s))).sum)).sum := by
    simpa using
      (map_map_sum_eq_sum_map_sum
        (xss := shiftedExpBlocks m xss) (f := fun x => roundNNE fmt (x / s)))
  rw [hrounded_rewrite]
  rw [← list_list_sum_div (xss := shiftedExpBlocks m xss) (s := s)]
  calc
    |((shiftedExpBlocks m xss).map (fun xs => (xs.map (fun x => x / s)).sum)).sum -
        ((shiftedExpBlocks m xss).map
          (fun xs => (xs.map (fun x => roundNNE fmt (x / s))).sum)).sum|
        ≤ ((shiftedExpBlocks m xss).map
            (fun xs =>
              |(xs.map (fun x => x / s)).sum -
                (xs.map (fun x => roundNNE fmt (x / s))).sum|)).sum := by
              simpa using
                map_sum_sub_le_sum_map_abs_sub (shiftedExpBlocks m xss)
                  (fun xs => (xs.map (fun x => x / s)).sum)
                  (fun xs => (xs.map (fun x => roundNNE fmt (x / s))).sum)
    _ ≤ ((shiftedExpBlocks m xss).map
          (fun xs => (xs.map (fun x => |x / s -
            roundNNE fmt (x / s)|)).sum)).sum := by
          induction (shiftedExpBlocks m xss) with
          | nil =>
              simp
          | cons xs xss ih =>
              simp only [List.map_cons, List.sum_cons]
              have hhead := map_sum_sub_le_sum_map_abs_sub xs
                (fun x => x / s)
                (fun x => roundNNE fmt (x / s))
              exact add_le_add hhead ih

/-! ## Row-max softmax bound for tight FP8 `p_scale`

These lemmas replace FlashInfer's `StandardFP8Attention` choice
`p_scale = numeric_limits<DTypeKV>::max()` with a tighter provable bound derived
from the per-row logit spread `Δ` and length `L`. -/

/-- Sum of shifted exponentials on a single list of logits. -/
noncomputable def expShiftSum (m : ℝ) (xs : List ℝ) : ℝ :=
  (xs.map (fun x => Real.exp (x - m))).sum

theorem expShiftSum_nil (m : ℝ) : expShiftSum m [] = 0 := by
  simp [expShiftSum]

theorem expShiftSum_cons (m x : ℝ) (xs : List ℝ) :
    expShiftSum m (x :: xs) = Real.exp (x - m) + expShiftSum m xs := by
  simp [expShiftSum]

theorem expShiftSum_nonneg (m : ℝ) (xs : List ℝ) : 0 ≤ expShiftSum m xs := by
  induction xs with
  | nil => simp [expShiftSum_nil]
  | cons x xs ih =>
    rw [expShiftSum_cons]
    exact add_nonneg (Real.exp_pos _).le ih

private theorem expShiftSum_bound_no_max {m Δ : ℝ} {xs : List ℝ}
    (hbound : ∀ x ∈ xs, m - Δ ≤ x) :
    (xs.length : ℝ) * Real.exp (-Δ) ≤ expShiftSum m xs := by
  induction xs with
  | nil => simp [expShiftSum_nil]
  | cons y ys ih =>
    rw [expShiftSum_cons]
    have hy : m - Δ ≤ y := hbound y (List.mem_cons_self)
    have hexp_y : Real.exp (-Δ) ≤ Real.exp (y - m) := by
      apply Real.exp_le_exp.mpr; linarith
    have hbound_tail : ∀ x ∈ ys, m - Δ ≤ x := fun x hx =>
      hbound x (List.mem_cons_of_mem _ hx)
    have htail := ih hbound_tail
    simp only [List.length_cons]
    push_cast; linarith

/-- Spread-based lower bound on the shifted-exponential sum. If some entry equals `m`
    (so one term contributes `exp(0) = 1`) and every entry lies within `Δ` below `m`,
    the sum exceeds `1 + (L - 1) · exp(-Δ)`. This is the core inequality for the
    softmax row-max bound. -/
theorem expShiftSum_lower_bound {m Δ : ℝ} {xs : List ℝ}
    (hm_in : m ∈ xs)
    (hbound : ∀ x ∈ xs, m - Δ ≤ x) :
    (1 : ℝ) + ((xs.length : ℝ) - 1) * Real.exp (-Δ) ≤ expShiftSum m xs := by
  induction xs with
  | nil => exact absurd hm_in (List.not_mem_nil)
  | cons y ys ih =>
    rw [expShiftSum_cons]
    simp only [List.mem_cons] at hm_in
    by_cases hym : y = m
    · subst hym
      have hexp_y : Real.exp (y - y) = 1 := by simp
      rw [hexp_y]
      have hbound_tail : ∀ x ∈ ys, y - Δ ≤ x := fun x hx =>
        hbound x (List.mem_cons_of_mem _ hx)
      have htail := expShiftSum_bound_no_max (m := y) (Δ := Δ) (xs := ys) hbound_tail
      simp only [List.length_cons]
      push_cast; linarith
    · have hm_ys : m ∈ ys := hm_in.resolve_left (fun h => hym h.symm)
      have hbound_tail : ∀ x ∈ ys, m - Δ ≤ x := fun x hx =>
        hbound x (List.mem_cons_of_mem _ hx)
      have htail := ih hm_ys hbound_tail
      have hy : m - Δ ≤ y := hbound y (List.mem_cons_self)
      have hexp_y : Real.exp (-Δ) ≤ Real.exp (y - m) := by
        apply Real.exp_le_exp.mpr; linarith
      simp only [List.length_cons]
      push_cast; linarith

theorem expShiftSum_pos_of_mem {m : ℝ} {xs : List ℝ} (hm_in : m ∈ xs) :
    0 < expShiftSum m xs := by
  induction xs with
  | nil => exact absurd hm_in (List.not_mem_nil)
  | cons y ys _ =>
    rw [expShiftSum_cons]
    have : 0 < Real.exp (y - m) := Real.exp_pos _
    linarith [expShiftSum_nonneg m ys]

/-- Softmax row-max bound: under logit spread `Δ` and at least one maximizer, every
    softmax entry is bounded by `1 / (1 + (L - 1) · exp(-Δ))`. -/
theorem softmax_entry_le_spread_bound {m Δ : ℝ} {xs : List ℝ}
    (hm_in : m ∈ xs)
    (hdom : ∀ x ∈ xs, x ≤ m)
    (hbound : ∀ x ∈ xs, m - Δ ≤ x)
    {x : ℝ} (hx : x ∈ xs) :
    Real.exp (x - m) / expShiftSum m xs ≤
      1 / (1 + ((xs.length : ℝ) - 1) * Real.exp (-Δ)) := by
  have hnum_le : Real.exp (x - m) ≤ 1 := exp_shift_le_one_of_dominated (hdom x hx)
  have hnum_nn : 0 ≤ Real.exp (x - m) := (Real.exp_pos _).le
  have hdenom_bound := expShiftSum_lower_bound hm_in hbound
  have hsum_pos : 0 < expShiftSum m xs := expShiftSum_pos_of_mem hm_in
  have hone_le_bound : 1 ≤ (1 : ℝ) + ((xs.length : ℝ) - 1) * Real.exp (-Δ) := by
    have hlen_ge : 1 ≤ (xs.length : ℝ) := by
      have : 1 ≤ xs.length := by
        rcases xs with _ | _
        · exact absurd hm_in (List.not_mem_nil)
        · simp
      exact_mod_cast this
    have hexp_nn : 0 ≤ Real.exp (-Δ) := (Real.exp_pos _).le
    nlinarith
  have hbound_pos : 0 < (1 : ℝ) + ((xs.length : ℝ) - 1) * Real.exp (-Δ) := by linarith
  have hstep1 : Real.exp (x - m) / expShiftSum m xs ≤ 1 / expShiftSum m xs :=
    div_le_div_of_nonneg_right hnum_le hsum_pos.le
  have hstep2 : 1 / expShiftSum m xs ≤
      1 / (1 + ((xs.length : ℝ) - 1) * Real.exp (-Δ)) :=
    one_div_le_one_div_of_le hbound_pos hdenom_bound
  exact le_trans hstep1 hstep2

/-- Provable tight `p_scale` for FP8 attention, replacing FlashInfer's hardcoded
    `numeric_limits<DTypeKV>::max()` with a value that fully exploits the softmax
    row-max structure. -/
noncomputable def provable_p_scale (fmt : FloatFormat) (L : ℕ) (Δ : ℝ) : ℝ :=
  maxFinite fmt * (1 + ((L : ℝ) - 1) * Real.exp (-Δ))

private theorem maxFinite_pos (fmt : FloatFormat) : 0 < maxFinite fmt := by
  unfold maxFinite
  apply mul_pos (zpow_pos fmt.β_pos _)
  have hme : machineEpsilon fmt ≤ 1 := by
    unfold machineEpsilon
    have hβ_one_le : (1 : ℝ) ≤ (fmt.β : ℝ) := fmt.β_one_lt.le
    have hexp : (1 : ℤ) - (fmt.prec : ℤ) ≤ 0 := by
      have : (1 : ℤ) ≤ fmt.prec := by exact_mod_cast fmt.hprec
      omega
    exact zpow_le_one_of_nonpos₀ hβ_one_le hexp
  linarith

/-- Tight no-overflow certificate: `softmax_entry · provable_p_scale ≤ maxFinite`.
    This is the replacement guarantee for FlashInfer's `p_scale` being hardcoded to
    `numeric_limits<DTypeKV>::max()`, derived solely from the per-row logit spread. -/
theorem softmax_entry_times_provable_p_scale_le_maxFinite
    {fmt : FloatFormat} {m Δ : ℝ} {xs : List ℝ}
    (hm_in : m ∈ xs)
    (hdom : ∀ x ∈ xs, x ≤ m)
    (hbound : ∀ x ∈ xs, m - Δ ≤ x)
    {x : ℝ} (hx : x ∈ xs) :
    Real.exp (x - m) / expShiftSum m xs * provable_p_scale fmt xs.length Δ
      ≤ maxFinite fmt := by
  have hsoftmax_le := softmax_entry_le_spread_bound hm_in hdom hbound hx
  have hmax_pos : 0 < maxFinite fmt := maxFinite_pos fmt
  have hlen_ge : 1 ≤ (xs.length : ℝ) := by
    have : 1 ≤ xs.length := by
      rcases xs with _ | _
      · exact absurd hm_in (List.not_mem_nil)
      · simp
    exact_mod_cast this
  have hexp_nn : 0 ≤ Real.exp (-Δ) := (Real.exp_pos _).le
  have hden_pos : 0 < (1 : ℝ) + ((xs.length : ℝ) - 1) * Real.exp (-Δ) := by nlinarith
  have hden_ne : (1 : ℝ) + ((xs.length : ℝ) - 1) * Real.exp (-Δ) ≠ 0 := ne_of_gt hden_pos
  unfold provable_p_scale
  calc Real.exp (x - m) / expShiftSum m xs *
        (maxFinite fmt * (1 + ((xs.length : ℝ) - 1) * Real.exp (-Δ)))
      ≤ (1 / (1 + ((xs.length : ℝ) - 1) * Real.exp (-Δ))) *
          (maxFinite fmt * (1 + ((xs.length : ℝ) - 1) * Real.exp (-Δ))) := by
        apply mul_le_mul_of_nonneg_right hsoftmax_le
        exact mul_nonneg hmax_pos.le hden_pos.le
    _ = maxFinite fmt := by field_simp

/-! ## Softmax Lipschitz bound (foundation for K-cache error analysis)

The single-entry softmax on a list: `softmaxEntry m xs x = exp(x - m) / ∑ exp(xᵢ - m)`.
This is the target of the tight Lipschitz bound needed to propagate K-cache
quantization error through the attention score pathway. The L∞ sensitivity
of softmax with respect to its logit input is bounded by `‖Δ‖∞`, giving the
linear (non-exp) dependence central to the anisotropy theorem.
-/

/-- Single-entry softmax over the shifted exponential family. -/
noncomputable def softmaxEntry (m : ℝ) (xs : List ℝ) (x : ℝ) : ℝ :=
  Real.exp (x - m) / expShiftSum m xs

/-- If `x ∈ xs`, then `exp(x - m)` is one of the terms in `expShiftSum m xs`,
    so it is bounded by the full sum. -/
private theorem exp_shift_mem_le_expShiftSum {m x : ℝ} {xs : List ℝ} (hx : x ∈ xs) :
    Real.exp (x - m) ≤ expShiftSum m xs := by
  induction xs with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons y ys ih =>
    rw [expShiftSum_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · linarith [expShiftSum_nonneg m ys]
    · have h1 : Real.exp (x - m) ≤ expShiftSum m ys := ih hmem
      have h2 : 0 ≤ Real.exp (y - m) := (Real.exp_pos _).le
      linarith

/-- Upper bound on `expShiftSum` over a perturbed list: each perturbation
    `δᵢ` inflates its term by at most `Real.exp ε`. -/
private theorem expShiftSum_zipWith_le_mul_exp
    {m ε : ℝ} {xs deltas : List ℝ}
    (hlen : xs.length = deltas.length)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε) :
    expShiftSum m (xs.zipWith (· + ·) deltas) ≤ Real.exp ε * expShiftSum m xs := by
  induction xs generalizing deltas with
  | nil =>
    simp [expShiftSum_nil, List.zipWith]
  | cons y ys ih =>
    cases deltas with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.zipWith_cons_cons, expShiftSum_cons]
      have hlen' : ys.length = ds.length := by
        simpa [List.length_cons] using hlen
      have hbound_tail : ∀ b ∈ ds, |b| ≤ ε := fun b hb =>
        hbound b (List.mem_cons_of_mem _ hb)
      have htail := ih hlen' hbound_tail
      have hd : |d| ≤ ε := hbound d (List.mem_cons_self)
      have hd_le : d ≤ ε := le_of_abs_le hd
      have hexp_d : Real.exp d ≤ Real.exp ε := Real.exp_le_exp.mpr hd_le
      have hhead : Real.exp (y + d - m) = Real.exp (y - m) * Real.exp d := by
        rw [← Real.exp_add]; ring_nf
      have hhead_le : Real.exp (y + d - m) ≤ Real.exp ε * Real.exp (y - m) := by
        rw [hhead]
        have hy_nn : 0 ≤ Real.exp (y - m) := (Real.exp_pos _).le
        calc Real.exp (y - m) * Real.exp d
            ≤ Real.exp (y - m) * Real.exp ε :=
              mul_le_mul_of_nonneg_left hexp_d hy_nn
          _ = Real.exp ε * Real.exp (y - m) := by ring
      have hsum_nn : 0 ≤ expShiftSum m ys := expShiftSum_nonneg m ys
      have hexp_nn : 0 ≤ Real.exp ε := (Real.exp_pos _).le
      nlinarith [htail, hhead_le]

/-- Lower bound on `expShiftSum` over a perturbed list: each perturbation
    `δᵢ` deflates its term by at most `Real.exp (-ε)`. -/
private theorem expShiftSum_zipWith_ge_mul_exp
    {m ε : ℝ} {xs deltas : List ℝ}
    (hlen : xs.length = deltas.length)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε) :
    Real.exp (-ε) * expShiftSum m xs ≤ expShiftSum m (xs.zipWith (· + ·) deltas) := by
  induction xs generalizing deltas with
  | nil =>
    simp [expShiftSum_nil, List.zipWith]
  | cons y ys ih =>
    cases deltas with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.zipWith_cons_cons, expShiftSum_cons]
      have hlen' : ys.length = ds.length := by
        simpa [List.length_cons] using hlen
      have hbound_tail : ∀ b ∈ ds, |b| ≤ ε := fun b hb =>
        hbound b (List.mem_cons_of_mem _ hb)
      have htail := ih hlen' hbound_tail
      have hd : |d| ≤ ε := hbound d (List.mem_cons_self)
      have hd_ge : -ε ≤ d := neg_le_of_abs_le hd
      have hexp_d : Real.exp (-ε) ≤ Real.exp d := Real.exp_le_exp.mpr hd_ge
      have hhead : Real.exp (y + d - m) = Real.exp (y - m) * Real.exp d := by
        rw [← Real.exp_add]; ring_nf
      have hhead_ge : Real.exp (-ε) * Real.exp (y - m) ≤ Real.exp (y + d - m) := by
        rw [hhead]
        have hy_nn : 0 ≤ Real.exp (y - m) := (Real.exp_pos _).le
        calc Real.exp (-ε) * Real.exp (y - m)
            = Real.exp (y - m) * Real.exp (-ε) := by ring
          _ ≤ Real.exp (y - m) * Real.exp d :=
              mul_le_mul_of_nonneg_left hexp_d hy_nn
      have hsum_nn : 0 ≤ expShiftSum m ys := expShiftSum_nonneg m ys
      have hexp_nn : 0 ≤ Real.exp (-ε) := (Real.exp_pos _).le
      nlinarith [htail, hhead_ge]

/-- For `ε ≥ 0`, `Real.exp ε - 1 ≤ ε · Real.exp ε`. Equivalently,
    `1 - ε ≤ Real.exp (-ε)`, which is `Real.add_one_le_exp (-ε)`. -/
private theorem exp_sub_one_le_mul_exp {ε : ℝ} (hε : 0 ≤ ε) :
    Real.exp ε - 1 ≤ ε * Real.exp ε := by
  have h := Real.add_one_le_exp (-ε)
  -- h : -ε + 1 ≤ Real.exp (-ε)
  have hexp_pos : 0 < Real.exp ε := Real.exp_pos _
  have hprod : Real.exp ε * Real.exp (-ε) = 1 := by
    rw [← Real.exp_add]; simp
  -- Multiply h by Real.exp ε (positive) to get:
  -- (-ε + 1) * Real.exp ε ≤ Real.exp ε * Real.exp (-ε) = 1.
  have hmul : (-ε + 1) * Real.exp ε ≤ Real.exp ε * Real.exp (-ε) := by
    have := mul_le_mul_of_nonneg_left h hexp_pos.le
    -- this : Real.exp ε * (-ε + 1) ≤ Real.exp ε * Real.exp (-ε)
    linarith [this, mul_comm (Real.exp ε) (-ε + 1)]
  rw [hprod] at hmul
  -- hmul : (-ε + 1) * Real.exp ε ≤ 1
  nlinarith [hmul]

/-- Target: softmax entry is Lipschitz in the logit with constant at most 2
    under `L∞` perturbation. Used to bound the effect of K-cache quantization
    on attention scores via composition with `Q · δK` bound. -/
theorem softmaxEntry_lipschitz
    (m : ℝ) (xs deltas : List ℝ)
    (hlen : xs.length = deltas.length)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε)
    (hmax : ∀ y ∈ xs, y ≤ m)
    {x : ℝ} (hx : x ∈ xs) :
    |softmaxEntry m xs x -
      softmaxEntry m (xs.zipWith (· + ·) deltas) x| ≤
      2 * ε * Real.exp (2 * ε) := by
  -- m ∈ xs? We only have hmax (x ≤ m for x ∈ xs) and hx : x ∈ xs. We use hx to
  -- get positivity of the original sum; for the perturbed sum we use the lower
  -- bound via `Real.exp (-ε) · S`.
  set S : ℝ := expShiftSum m xs with hS_def
  set S' : ℝ := expShiftSum m (xs.zipWith (· + ·) deltas) with hS'_def
  set e : ℝ := Real.exp (x - m) with he_def
  have he_pos : 0 < e := Real.exp_pos _
  have he_nn : 0 ≤ e := he_pos.le
  -- Positivity of S from x ∈ xs.
  have hS_pos : 0 < S := by
    have hterm : 0 < Real.exp (x - m) := Real.exp_pos _
    have hterm_le : Real.exp (x - m) ≤ expShiftSum m xs :=
      exp_shift_mem_le_expShiftSum hx
    linarith
  -- Bounds on S' via helper lemmas.
  have hexp_ε_pos : 0 < Real.exp ε := Real.exp_pos _
  have hexp_negε_pos : 0 < Real.exp (-ε) := Real.exp_pos _
  have hS'_upper : S' ≤ Real.exp ε * S :=
    expShiftSum_zipWith_le_mul_exp hlen hbound
  have hS'_lower : Real.exp (-ε) * S ≤ S' :=
    expShiftSum_zipWith_ge_mul_exp hlen hbound
  have hS'_pos : 0 < S' := by
    have : 0 < Real.exp (-ε) * S := mul_pos hexp_negε_pos hS_pos
    linarith
  -- Step: e ≤ S (term membership).
  have he_le_S : e ≤ S := exp_shift_mem_le_expShiftSum hx
  -- Rewrite the absolute difference as `e * |S' - S| / (S * S')`.
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hS'_ne : S' ≠ 0 := ne_of_gt hS'_pos
  have hdiff_eq : softmaxEntry m xs x - softmaxEntry m (xs.zipWith (· + ·) deltas) x
      = e * (S' - S) / (S * S') := by
    unfold softmaxEntry
    show e / S - e / S' = e * (S' - S) / (S * S')
    field_simp
  rw [hdiff_eq]
  rw [abs_div, abs_mul]
  have habs_e : |e| = e := abs_of_nonneg he_nn
  rw [habs_e]
  have hSS'_pos : 0 < S * S' := mul_pos hS_pos hS'_pos
  have habs_SS' : |S * S'| = S * S' := abs_of_pos hSS'_pos
  rw [habs_SS']
  -- |S' - S| ≤ (exp ε - 1) * S since both Real.exp ε * S - S and S - Real.exp (-ε) * S
  -- are bounded by (exp ε - 1) * S (using 1 - exp(-ε) ≤ exp ε - 1 for ε ≥ 0).
  have hexpε_ge_one : 1 ≤ Real.exp ε := by
    have := Real.add_one_le_exp ε
    linarith
  have hexpnegε_le_one : Real.exp (-ε) ≤ 1 := by
    rw [Real.exp_neg, inv_le_one_iff₀]
    exact Or.inr hexpε_ge_one
  have hone_sub_le : 1 - Real.exp (-ε) ≤ Real.exp ε - 1 := by
    -- Equivalent to Real.exp ε + Real.exp (-ε) ≥ 2, which follows from AM-GM:
    -- Real.exp ε * Real.exp (-ε) = 1, so a + 1/a ≥ 2.
    have hprod : Real.exp ε * Real.exp (-ε) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [sq_nonneg (Real.exp ε - 1), hexp_ε_pos, hexpε_ge_one]
  have hS'_minus_S_upper : S' - S ≤ (Real.exp ε - 1) * S := by
    have : S' ≤ Real.exp ε * S := hS'_upper
    nlinarith
  have hS_minus_S'_upper : S - S' ≤ (Real.exp ε - 1) * S := by
    have h1 : S - S' ≤ S - Real.exp (-ε) * S := by linarith
    have h2 : S - Real.exp (-ε) * S = (1 - Real.exp (-ε)) * S := by ring
    have h3 : (1 - Real.exp (-ε)) * S ≤ (Real.exp ε - 1) * S := by
      have hS_nn : 0 ≤ S := hS_pos.le
      exact mul_le_mul_of_nonneg_right hone_sub_le hS_nn
    linarith
  have habs_diff : |S' - S| ≤ (Real.exp ε - 1) * S := by
    rw [abs_le]
    refine ⟨?_, hS'_minus_S_upper⟩
    linarith
  -- Now bound e * |S' - S| / (S * S') ≤ e * ((exp ε - 1) * S) / (S * S')
  --    = e * (exp ε - 1) / S'
  --    ≤ (exp ε - 1) (since e ≤ S ≤ S'/exp(-ε), want e/S' ≤ exp ε, but easier:
  --      e/S ≤ 1 and S/S' ≤ exp ε so e/S' ≤ exp ε).
  -- We directly bound:
  --   e * |S' - S| ≤ e * (exp ε - 1) * S
  -- and
  --   S * S' ≥ S * (exp(-ε) * S) = exp(-ε) * S^2
  -- so the ratio ≤ (exp ε - 1) * exp ε * (e / S) ≤ (exp ε - 1) * exp ε.
  have hnum_bound : e * |S' - S| ≤ e * ((Real.exp ε - 1) * S) :=
    mul_le_mul_of_nonneg_left habs_diff he_nn
  -- We want: e * |S' - S| / (S * S') ≤ (Real.exp ε - 1) * Real.exp ε
  have hratio_bound : e * |S' - S| / (S * S') ≤ (Real.exp ε - 1) * Real.exp ε := by
    have hSS'_ne : S * S' ≠ 0 := ne_of_gt hSS'_pos
    rw [div_le_iff₀ hSS'_pos]
    -- Need: e * |S' - S| ≤ (Real.exp ε - 1) * Real.exp ε * (S * S')
    calc e * |S' - S|
        ≤ e * ((Real.exp ε - 1) * S) := hnum_bound
      _ ≤ S * ((Real.exp ε - 1) * S) := by
            have hcoef_nn : 0 ≤ (Real.exp ε - 1) * S := by
              have : 0 ≤ Real.exp ε - 1 := by linarith
              exact mul_nonneg this hS_pos.le
            exact mul_le_mul_of_nonneg_right he_le_S hcoef_nn
      _ = (Real.exp ε - 1) * (S * S) := by ring
      _ ≤ (Real.exp ε - 1) * (Real.exp ε * (S * S')) := by
            have hexp_sub_nn : 0 ≤ Real.exp ε - 1 := by linarith
            have hSS_le : S * S ≤ Real.exp ε * (S * S') := by
              -- S ≤ exp ε * S' / exp(-ε)... simpler: S * S ≤ S * (exp ε * S')
              -- since S ≤ exp ε * S' (from exp(-ε) * S ≤ S' ⇒ S ≤ S'/exp(-ε) = exp ε * S')
              have hS_le_expε_S' : S ≤ Real.exp ε * S' := by
                have h1 : Real.exp (-ε) * S ≤ S' := hS'_lower
                have h2 : Real.exp ε * (Real.exp (-ε) * S) ≤ Real.exp ε * S' :=
                  mul_le_mul_of_nonneg_left h1 hexp_ε_pos.le
                have h3 : Real.exp ε * (Real.exp (-ε) * S) = S := by
                  have hprod : Real.exp ε * Real.exp (-ε) = 1 := by
                    rw [← Real.exp_add]; simp
                  calc Real.exp ε * (Real.exp (-ε) * S)
                      = (Real.exp ε * Real.exp (-ε)) * S := by ring
                    _ = 1 * S := by rw [hprod]
                    _ = S := one_mul S
                linarith
              calc S * S ≤ (Real.exp ε * S') * S := by
                    exact mul_le_mul_of_nonneg_right hS_le_expε_S' hS_pos.le
                _ = Real.exp ε * (S * S') := by ring
            exact mul_le_mul_of_nonneg_left hSS_le hexp_sub_nn
      _ = (Real.exp ε - 1) * Real.exp ε * (S * S') := by ring
  -- Now chain with (exp ε - 1) * exp ε ≤ ε * exp ε * exp ε = ε * exp (2ε) ≤ 2ε * exp(2ε).
  have hexp_sub_bound : Real.exp ε - 1 ≤ ε * Real.exp ε := exp_sub_one_le_mul_exp hε
  have hexp_2ε : Real.exp ε * Real.exp ε = Real.exp (2 * ε) := by
    rw [← Real.exp_add]; ring_nf
  have hfinal : (Real.exp ε - 1) * Real.exp ε ≤ 2 * ε * Real.exp (2 * ε) := by
    have hstep1 : (Real.exp ε - 1) * Real.exp ε ≤ (ε * Real.exp ε) * Real.exp ε :=
      mul_le_mul_of_nonneg_right hexp_sub_bound hexp_ε_pos.le
    have hstep2 : (ε * Real.exp ε) * Real.exp ε = ε * Real.exp (2 * ε) := by
      rw [mul_assoc, hexp_2ε]
    have hstep3 : ε * Real.exp (2 * ε) ≤ 2 * ε * Real.exp (2 * ε) := by
      have h2ε_nn : 0 ≤ Real.exp (2 * ε) := (Real.exp_pos _).le
      nlinarith
    linarith
  linarith

/-- If every element of `xs` maps to a value `≤ C` (with `C ≥ 0`), then the
    total `(xs.map f).sum` is bounded by `xs.length · C`. -/
private theorem sum_map_le_length_mul {xs : List ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ∈ xs, f x ≤ C) :
    (xs.map f).sum ≤ (xs.length : ℝ) * C := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy : f y ≤ C := hbound y (List.mem_cons_self)
    have hys : ∀ x ∈ ys, f x ≤ C := fun x hx =>
      hbound x (List.mem_cons_of_mem _ hx)
    have htail := ih hys
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    have : f y + (ys.map f).sum ≤ C + (ys.length : ℝ) * C := add_le_add hy htail
    linarith

/-- L1 aggregate of `softmaxEntry_lipschitz`: summed over all entries, the
    total variation of softmax under logit perturbation is bounded linearly in
    the list length times the per-entry bound. -/
theorem softmax_l1_lipschitz
    (m : ℝ) (xs deltas : List ℝ)
    (hlen : xs.length = deltas.length)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε)
    (hmax : ∀ y ∈ xs, y ≤ m) :
    (xs.map (fun x =>
        |softmaxEntry m xs x -
         softmaxEntry m (xs.zipWith (· + ·) deltas) x|)).sum
      ≤ (xs.length : ℝ) * (2 * ε * Real.exp (2 * ε)) := by
  have hC_nn : 0 ≤ 2 * ε * Real.exp (2 * ε) := by
    have h1 : 0 ≤ 2 * ε := by linarith
    have h2 : 0 ≤ Real.exp (2 * ε) := (Real.exp_pos _).le
    exact mul_nonneg h1 h2
  have hentry : ∀ x ∈ xs,
      |softmaxEntry m xs x -
        softmaxEntry m (xs.zipWith (· + ·) deltas) x|
        ≤ 2 * ε * Real.exp (2 * ε) := fun x hx =>
    softmaxEntry_lipschitz m xs deltas hlen hε hbound hmax hx
  exact sum_map_le_length_mul hC_nn hentry

/-! ## Attention K-sensitivity (Cauchy-Schwarz composed with softmax Lipschitz)

The attention score `Q · K` is 1-Lipschitz in `K` with constant `‖Q‖₂` by
Cauchy-Schwarz. Composing with `softmaxEntry_lipschitz` gives that the softmax
output perturbation under K-cache quantization is bounded linearly (not
exp-amplified) in `‖Q‖₂ · ‖δK‖₂`, matching the V-Lipschitz result and
formalizing the anisotropy between score-path (K-cache) and numerator-path
(P-side) quantization margin. -/

/-- Dot product of two real lists (truncated at the shorter length). -/
noncomputable def attentionScore (Q K : List ℝ) : ℝ :=
  ((Q.zip K).map (fun p => p.1 * p.2)).sum

/-- Euclidean (L2) norm of a real list. -/
noncomputable def vecL2 (xs : List ℝ) : ℝ :=
  Real.sqrt ((xs.map (fun x => x ^ 2)).sum)

theorem vecL2_nonneg (xs : List ℝ) : 0 ≤ vecL2 xs := Real.sqrt_nonneg _

private theorem sum_sq_nonneg (xs : List ℝ) : 0 ≤ (xs.map (fun x => x ^ 2)).sum :=
  List.sum_nonneg fun _ hx => by
    rcases List.mem_map.mp hx with ⟨y, _, rfl⟩; exact sq_nonneg y

/-- Discriminant identity: for lists of equal length,
    `Σ (qᵢ − t·kᵢ)² = Σqᵢ² − 2t·Σqᵢkᵢ + t²·Σkᵢ²`. -/
private theorem sum_sq_sub_mul (Q K : List ℝ) (t : ℝ)
    (hlen : Q.length = K.length) :
    ((Q.zip K).map (fun p => (p.1 - t * p.2) ^ 2)).sum =
      (Q.map (fun x => x ^ 2)).sum -
        2 * t * ((Q.zip K).map (fun p => p.1 * p.2)).sum +
        t ^ 2 * (K.map (fun x => x ^ 2)).sum := by
  induction Q generalizing K with
  | nil =>
    cases K with
    | nil => simp
    | cons k ks => simp at hlen
  | cons q qs ih =>
    cases K with
    | nil => simp at hlen
    | cons k ks =>
      have hlen' : qs.length = ks.length := by
        simpa [List.length_cons] using hlen
      have htail := ih ks hlen'
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [htail]
      ring

/-- If the sum of squares of a real list is zero, every element is zero. -/
private theorem eq_zero_of_sum_sq_eq_zero {xs : List ℝ}
    (h : (xs.map (fun x => x ^ 2)).sum = 0) : ∀ x ∈ xs, x = 0 := by
  intro x hx
  have hx_sq_mem : x ^ 2 ∈ xs.map (fun x => x ^ 2) := List.mem_map.mpr ⟨x, hx, rfl⟩
  have hnn : ∀ y ∈ xs.map (fun x => x ^ 2), 0 ≤ y := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨z, _, rfl⟩
    exact sq_nonneg z
  have : x ^ 2 = 0 :=
    le_antisymm (h ▸ List.single_le_sum hnn _ hx_sq_mem)
      (sq_nonneg x)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- If every `kᵢ = 0`, then `attentionScore Q K = 0`. -/
private theorem attentionScore_eq_zero_of_K_zero (Q K : List ℝ)
    (hK : ∀ k ∈ K, k = 0) : attentionScore Q K = 0 := by
  unfold attentionScore
  apply List.sum_eq_zero
  intro p hp
  rcases List.mem_map.mp hp with ⟨⟨q, k⟩, hpair, rfl⟩
  have hk_mem : k ∈ K := (List.of_mem_zip hpair).2
  simp [hK k hk_mem]

/-- `(Σ qᵢkᵢ)² ≤ (Σ qᵢ²) · (Σ kᵢ²)` for equal-length real lists. -/
private theorem attentionScore_sq_le (Q K : List ℝ)
    (hlen : Q.length = K.length) :
    (attentionScore Q K) ^ 2 ≤
      (Q.map (fun x => x ^ 2)).sum * (K.map (fun x => x ^ 2)).sum := by
  set A : ℝ := (Q.map (fun x => x ^ 2)).sum with hA_def
  set B : ℝ := (K.map (fun x => x ^ 2)).sum with hB_def
  set C : ℝ := attentionScore Q K with hC_def
  have hA_nn : 0 ≤ A := sum_sq_nonneg Q
  have hB_nn : 0 ≤ B := sum_sq_nonneg K
  -- For every t : ℝ, A - 2tC + t²B ≥ 0.
  have hC_unfold : C = ((Q.zip K).map (fun p => p.1 * p.2)).sum := rfl
  have hpoly : ∀ t : ℝ, 0 ≤ A - 2 * t * C + t ^ 2 * B := by
    intro t
    have hsum_nn :
        0 ≤ ((Q.zip K).map (fun p => (p.1 - t * p.2) ^ 2)).sum :=
      List.sum_nonneg fun y hy => by
        rcases List.mem_map.mp hy with ⟨p, _, rfl⟩; exact sq_nonneg _
    have hident := sum_sq_sub_mul Q K t hlen
    rw [← hA_def, ← hB_def, ← hC_unfold] at hident
    linarith [hsum_nn, hident]
  rcases eq_or_lt_of_le hB_nn with hB0 | hBpos
  · -- B = 0 ⇒ all kᵢ = 0 ⇒ C = 0.
    have hBzero : B = 0 := hB0.symm
    have hall_k : ∀ k ∈ K, k = 0 := eq_zero_of_sum_sq_eq_zero hBzero
    have hC0 : C = 0 := attentionScore_eq_zero_of_K_zero Q K hall_k
    rw [hC0, hBzero]
    simp
  · -- B > 0: plug t = C / B.
    have hB_ne : B ≠ 0 := ne_of_gt hBpos
    have hpoly_cB := hpoly (C / B)
    -- hpoly_cB : 0 ≤ A - 2*(C/B)*C + (C/B)^2 * B
    have hsimp : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp
      ring
    rw [hsimp] at hpoly_cB
    -- hpoly_cB : 0 ≤ A - C^2 / B, so C^2 ≤ A*B (using B > 0).
    have h1 : C ^ 2 / B ≤ A := by linarith
    have := (div_le_iff₀ hBpos).mp h1
    linarith

/-- Cauchy-Schwarz on lists: `|Q · K| ≤ ‖Q‖₂ · ‖K‖₂`. -/
theorem attentionScore_cauchy_schwarz (Q K : List ℝ)
    (hlen : Q.length = K.length) :
    |attentionScore Q K| ≤ vecL2 Q * vecL2 K := by
  set A : ℝ := (Q.map (fun x => x ^ 2)).sum with hA_def
  set B : ℝ := (K.map (fun x => x ^ 2)).sum with hB_def
  have hA_nn : 0 ≤ A := sum_sq_nonneg Q
  have hB_nn : 0 ≤ B := sum_sq_nonneg K
  have hC_sq : (attentionScore Q K) ^ 2 ≤ A * B :=
    attentionScore_sq_le Q K hlen
  -- |C| = √(C²) ≤ √(A·B) = √A · √B.
  have habs_sq : |attentionScore Q K| = Real.sqrt ((attentionScore Q K) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs_sq]
  have hAB_nn : 0 ≤ A * B := mul_nonneg hA_nn hB_nn
  calc Real.sqrt ((attentionScore Q K) ^ 2)
      ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hC_sq
    _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA_nn _
    _ = vecL2 Q * vecL2 K := rfl

/-- Attention K-sensitivity: a K-cache perturbation with per-key L2 bound `εK`
    induces softmax output perturbation at most `2·(‖Q‖₂·εK)·exp(2·(‖Q‖₂·εK))`.
    Composes Cauchy-Schwarz on `Q · δK` with `softmaxEntry_lipschitz`.

    This is the formal counterpart of the V-cache 1-Lipschitz bound: error
    propagates linearly (without exp-scale amplification), matching the
    empirical observation that KV-cache quantization margin is an order of
    magnitude less sensitive to scale than the P-side margin. -/
theorem attention_K_sensitivity
    (Q : List ℝ) (Ks δKs : List (List ℝ)) (m : ℝ)
    (hlen : Ks.length = δKs.length)
    (hdimδ : ∀ dK ∈ δKs, Q.length = dK.length)
    {εK : ℝ} (hεK : 0 ≤ εK)
    (hbound : ∀ dK ∈ δKs, vecL2 dK ≤ εK)
    (hmax : ∀ s ∈ Ks.map (attentionScore Q), s ≤ m)
    {K : List ℝ} (hK : K ∈ Ks) :
    |softmaxEntry m (Ks.map (attentionScore Q)) (attentionScore Q K) -
      softmaxEntry m
        ((Ks.map (attentionScore Q)).zipWith (· + ·)
          (δKs.map (attentionScore Q)))
        (attentionScore Q K)| ≤
      2 * (vecL2 Q * εK) * Real.exp (2 * (vecL2 Q * εK)) := by
  -- Apply softmaxEntry_lipschitz with xs := Ks.map (attentionScore Q),
  -- deltas := δKs.map (attentionScore Q), ε := vecL2 Q * εK.
  set xs : List ℝ := Ks.map (attentionScore Q) with hxs_def
  set deltas : List ℝ := δKs.map (attentionScore Q) with hdeltas_def
  set ε : ℝ := vecL2 Q * εK with hε_def
  have hlen' : xs.length = deltas.length := by
    simp [hxs_def, hdeltas_def, List.length_map, hlen]
  have hQ_nn : 0 ≤ vecL2 Q := vecL2_nonneg Q
  have hε_nn : 0 ≤ ε := mul_nonneg hQ_nn hεK
  have hbound' : ∀ d ∈ deltas, |d| ≤ ε := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨dK, hdK_mem, rfl⟩
    have hQ_dK_len : Q.length = dK.length := hdimδ dK hdK_mem
    -- |attentionScore Q dK| ≤ vecL2 Q * vecL2 dK ≤ vecL2 Q * εK = ε.
    have hCS := attentionScore_cauchy_schwarz Q dK hQ_dK_len
    have hbd : vecL2 dK ≤ εK := hbound dK hdK_mem
    have hmul : vecL2 Q * vecL2 dK ≤ vecL2 Q * εK :=
      mul_le_mul_of_nonneg_left hbd hQ_nn
    exact le_trans hCS hmul
  have hx_mem : attentionScore Q K ∈ xs :=
    List.mem_map.mpr ⟨K, hK, rfl⟩
  exact softmaxEntry_lipschitz m xs deltas hlen' hε_nn hbound' hmax hx_mem

/-! ## Attention anisotropy: V-cache perturbations propagate linearly

Unlike softmax-numerator (P-side) quantization where a wrong `max_offset`
can cause exp-scale amplification of the error (see `roundedShiftedExp_*`
underflow lemmas), V-cache quantization error propagates through the
attention output with Lipschitz constant 1. If the attention weights form
a probability distribution and `V` is perturbed by at most `ε` in `L∞`,
the attention output `Σᵢ pᵢ · Vᵢ` changes by at most `ε`. This is the
formal counterpart of the empirical observation that KV-cache quantization
margin is an order of magnitude less sensitive to scale choice than the
P-side margin.
-/

/-- Inner product of a weight list and a value list. -/
noncomputable def weightedSum (ps xs : List ℝ) : ℝ :=
  ((ps.zip xs).map (fun p => p.1 * p.2)).sum

@[simp] theorem weightedSum_nil_left (xs : List ℝ) : weightedSum [] xs = 0 := by
  simp [weightedSum]

@[simp] theorem weightedSum_nil_right (ps : List ℝ) : weightedSum ps [] = 0 := by
  cases ps <;> simp [weightedSum]

theorem weightedSum_cons (p x : ℝ) (ps xs : List ℝ) :
    weightedSum (p :: ps) (x :: xs) = p * x + weightedSum ps xs := by
  simp [weightedSum]

/-- Helper: `|∑ pᵢ · δᵢ| ≤ (∑ pᵢ) · ε` when `pᵢ ≥ 0` and `|δᵢ| ≤ ε`. -/
private theorem weightedSum_abs_bound
    {ps deltas : List ℝ}
    (hnn : ∀ p ∈ ps, 0 ≤ p)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε) :
    |weightedSum ps deltas| ≤ ps.sum * ε := by
  induction ps generalizing deltas with
  | nil => simp [weightedSum]
  | cons p ps ih =>
    cases deltas with
    | nil =>
      have hp_nn : 0 ≤ p := hnn p (List.mem_cons_self)
      have hps_nn : ∀ q ∈ ps, 0 ≤ q := fun q hq => hnn q (List.mem_cons_of_mem _ hq)
      have hsum_nn : 0 ≤ (p :: ps).sum :=
        List.sum_nonneg fun x hx => by
          rcases List.mem_cons.mp hx with h | h
          · exact h ▸ hp_nn
          · exact hps_nn x h
      simp [weightedSum_nil_right]
      exact mul_nonneg hsum_nn hε
    | cons d ds =>
      have hp_nn : 0 ≤ p := hnn p (List.mem_cons_self)
      have hps_nn : ∀ q ∈ ps, 0 ≤ q := fun q hq => hnn q (List.mem_cons_of_mem _ hq)
      have hds_bound : ∀ d' ∈ ds, |d'| ≤ ε := fun d' hd' =>
        hbound d' (List.mem_cons_of_mem _ hd')
      have hd_bound : |d| ≤ ε := hbound d (List.mem_cons_self)
      have htail := ih hps_nn hds_bound
      rw [weightedSum_cons]
      calc |p * d + weightedSum ps ds|
          ≤ |p * d| + |weightedSum ps ds| := abs_add_le _ _
        _ = p * |d| + |weightedSum ps ds| := by rw [abs_mul, abs_of_nonneg hp_nn]
        _ ≤ p * ε + ps.sum * ε := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hd_bound hp_nn
            · exact htail
        _ = (p + ps.sum) * ε := by ring
        _ = (p :: ps).sum * ε := by rw [List.sum_cons]

/-- V-cache perturbation sensitivity: the attention output is 1-Lipschitz in
    V under `L∞` perturbation. If the attention weights `ps` form a probability
    distribution (nonneg, sum = 1) and every `V`-perturbation magnitude is
    bounded by `ε`, then `|∑ pᵢ · δᵢ| ≤ ε`. No exponential amplification.

    Contrast with the P-side: quantizing the softmax numerator with a too-small
    `max_offset` can zero out tail entries entirely (see `roundedExp_eq_zero_iff`
    in StableLogSumExp), changing the normalized softmax by an `O(1)` factor
    rather than `O(ε)`. -/
theorem attention_V_lipschitz
    {ps deltas : List ℝ}
    (hnn : ∀ p ∈ ps, 0 ≤ p)
    (hsum : ps.sum = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ d ∈ deltas, |d| ≤ ε) :
    |weightedSum ps deltas| ≤ ε := by
  have h := weightedSum_abs_bound hnn hε hbound
  rw [hsum, one_mul] at h
  exact h

/-! ## Online LSE: block-wise merging equivalent to a static reference max

These lemmas establish that FA-3 / FlashInfer's online softmax recurrence
(incremental `(m, l)` update when a new block arrives) computes the same
`(max, shifted-sum)` pair as the static-shift formulation used in `StableLogSumExp`.
-/

/-- Rescaling: multiplying `expShiftSum m₁ xs` by `exp(m₁ - m₂)` reshifts the sum's
    reference from `m₁` to `m₂`. -/
theorem expShiftSum_rescale (m₁ m₂ : ℝ) (xs : List ℝ) :
    expShiftSum m₁ xs * Real.exp (m₁ - m₂) = expShiftSum m₂ xs := by
  induction xs with
  | nil => simp [expShiftSum_nil]
  | cons y ys ih =>
    rw [expShiftSum_cons, expShiftSum_cons]
    have hy : Real.exp (y - m₁) * Real.exp (m₁ - m₂) = Real.exp (y - m₂) := by
      rw [← Real.exp_add]; congr 1; ring
    have hdist : (Real.exp (y - m₁) + expShiftSum m₁ ys) * Real.exp (m₁ - m₂) =
        Real.exp (y - m₁) * Real.exp (m₁ - m₂) +
          expShiftSum m₁ ys * Real.exp (m₁ - m₂) := by ring
    rw [hdist, hy, ih]

/-- `expShiftSum` is additive over list concatenation. -/
theorem expShiftSum_append (m : ℝ) (xs ys : List ℝ) :
    expShiftSum m (xs ++ ys) = expShiftSum m xs + expShiftSum m ys := by
  unfold expShiftSum
  rw [List.map_append, List.sum_append]

/-- Scalar merge identity: the online LSE update combines two per-block
    shifted sums at a new common max, exactly matching the shifted sum of the
    concatenated input evaluated at that max. -/
theorem onlineLSE_merge_scalar (m₁ m₂ : ℝ) (xs₁ xs₂ : List ℝ) :
    expShiftSum m₁ xs₁ * Real.exp (m₁ - max m₁ m₂) +
        expShiftSum m₂ xs₂ * Real.exp (m₂ - max m₁ m₂) =
      expShiftSum (max m₁ m₂) (xs₁ ++ xs₂) := by
  rw [expShiftSum_append, expShiftSum_rescale, expShiftSum_rescale]

/-- Online LSE merge step: given two blocks' `(max, shifted-sum)` pairs, produce
    the combined pair. Matches the structure of FA-3's `softmax.update` and
    FlashInfer's `OnlineSoftmax::update`. -/
noncomputable def onlineLSEMerge (s₁ s₂ : ℝ × ℝ) : ℝ × ℝ :=
  let m := max s₁.1 s₂.1
  (m, s₁.2 * Real.exp (s₁.1 - m) + s₂.2 * Real.exp (s₂.1 - m))

/-- Online ↔ static equivalence: merging per-block states via `onlineLSEMerge`
    equals taking the joint max and evaluating `expShiftSum` over the concatenated
    block. This is the invariance licensing the online recurrence. -/
theorem onlineLSEMerge_correct (m₁ m₂ : ℝ) (xs₁ xs₂ : List ℝ) :
    onlineLSEMerge (m₁, expShiftSum m₁ xs₁) (m₂, expShiftSum m₂ xs₂) =
      (max m₁ m₂, expShiftSum (max m₁ m₂) (xs₁ ++ xs₂)) := by
  simp only [onlineLSEMerge, onlineLSE_merge_scalar]

/-! ## n-block fold: direct counterpart of FA-3's online softmax loop -/

/-- Fold the online merge over a list of per-block `(m, l)` pairs. Matches the
    structure of FA-3's consumer mainloop iterating over KV tiles. -/
noncomputable def onlineLSEFold (init : ℝ × ℝ) (states : List (ℝ × ℝ)) : ℝ × ℝ :=
  states.foldl onlineLSEMerge init

/-- Joint max across a seed `m₀` and a list of `(block_max, block_content)` pairs. -/
def blocksMax (m₀ : ℝ) (blocks : List (ℝ × List ℝ)) : ℝ :=
  blocks.foldl (fun m p => max m p.1) m₀

/-- Concatenated block contents, seeded with `xs₀`. -/
def blocksFlatten (xs₀ : List ℝ) (blocks : List (ℝ × List ℝ)) : List ℝ :=
  xs₀ ++ (blocks.map Prod.snd).flatten

theorem blocksMax_nil (m₀ : ℝ) : blocksMax m₀ [] = m₀ := rfl

theorem blocksMax_cons (m₀ : ℝ) (p : ℝ × List ℝ) (ps : List (ℝ × List ℝ)) :
    blocksMax m₀ (p :: ps) = blocksMax (max m₀ p.1) ps := by
  simp [blocksMax]

theorem blocksFlatten_nil (xs₀ : List ℝ) : blocksFlatten xs₀ [] = xs₀ := by
  simp [blocksFlatten]

theorem blocksFlatten_cons (xs₀ : List ℝ) (p : ℝ × List ℝ) (ps : List (ℝ × List ℝ)) :
    blocksFlatten xs₀ (p :: ps) = blocksFlatten (xs₀ ++ p.2) ps := by
  simp [blocksFlatten]

/-- Online ↔ static equivalence for arbitrarily many blocks. Folding the per-block
    `(m_i, expShiftSum m_i xs_i)` states through `onlineLSEMerge` yields the joint
    max and the static shifted-exp-sum over the concatenated blocks. This is the
    Lean statement that directly licenses FA-3's online softmax outer loop. -/
theorem onlineLSEFold_eq_static
    (m₀ : ℝ) (xs₀ : List ℝ) (blocks : List (ℝ × List ℝ)) :
    onlineLSEFold (m₀, expShiftSum m₀ xs₀)
        (blocks.map (fun p => (p.1, expShiftSum p.1 p.2))) =
      (blocksMax m₀ blocks,
        expShiftSum (blocksMax m₀ blocks) (blocksFlatten xs₀ blocks)) := by
  induction blocks generalizing m₀ xs₀ with
  | nil => simp [onlineLSEFold, blocksMax_nil, blocksFlatten_nil]
  | cons p ps ih =>
    simp only [onlineLSEFold, List.map_cons, List.foldl_cons]
    rw [onlineLSEMerge_correct, blocksMax_cons, blocksFlatten_cons]
    exact ih (max m₀ p.1) (xs₀ ++ p.2)

/-! ## FP8 concrete-constant corollaries (for paper citation) -/

theorem maxFinite_binarySpec8_e4m3 :
    maxFinite binarySpec8_e4m3.toFormat = 240 := by
  unfold maxFinite machineEpsilon BinarySpec.toFormat binarySpec8_e4m3 BinarySpec.bias
  norm_num

theorem maxFinite_binarySpec8_e5m2 :
    maxFinite binarySpec8_e5m2.toFormat = 57344 := by
  unfold maxFinite machineEpsilon BinarySpec.toFormat binarySpec8_e5m2 BinarySpec.bias
  norm_num

theorem log_minNormal_binarySpec8_e4m3 :
    Real.log (minNormal binarySpec8_e4m3.toFormat) = -9 * Real.log 2 := by
  rw [minNormal_binarySpec8_e4m3, Real.log_zpow]
  push_cast; ring

theorem log_minNormal_binarySpec8_e5m2 :
    Real.log (minNormal binarySpec8_e5m2.toFormat) = -16 * Real.log 2 := by
  rw [minNormal_binarySpec8_e5m2, Real.log_zpow]
  push_cast; ring

/-- Concrete `provable_p_scale` for FP8 E4M3: `240 · (1 + (L-1)·exp(-Δ))`. -/
theorem provable_p_scale_binarySpec8_e4m3 (L : ℕ) (Δ : ℝ) :
    provable_p_scale binarySpec8_e4m3.toFormat L Δ =
      240 * (1 + ((L : ℝ) - 1) * Real.exp (-Δ)) := by
  rw [provable_p_scale, maxFinite_binarySpec8_e4m3]

/-- Concrete `provable_p_scale` for FP8 E5M2: `57344 · (1 + (L-1)·exp(-Δ))`. -/
theorem provable_p_scale_binarySpec8_e5m2 (L : ℕ) (Δ : ℝ) :
    provable_p_scale binarySpec8_e5m2.toFormat L Δ =
      57344 * (1 + ((L : ℝ) - 1) * Real.exp (-Δ)) := by
  rw [provable_p_scale, maxFinite_binarySpec8_e5m2]

/-- FP8 E4M3 block-level no-underflow: if `k - Δ ≥ -9 · log 2 ≈ -6.24`, no entry
    rounds to zero under a shift `m` + pre-exp offset `k`. -/
theorem roundedShiftedExp_no_underflow_binarySpec8_e4m3
    {m k Δ : ℝ} {xs : List ℝ}
    (hbound : ∀ x ∈ xs, m - Δ ≤ x)
    (hsafe : -9 * Real.log 2 ≤ k - Δ) :
    ∀ x ∈ xs, roundedExp binarySpec8_e4m3.toFormat (x - m + k) ≠ 0 :=
  roundedShiftedExp_no_underflow_of_safe_offset (fmt := binarySpec8_e4m3.toFormat) hbound
    (by rw [log_minNormal_binarySpec8_e4m3]; exact hsafe)

/-- FP8 E5M2 block-level no-underflow: if `k - Δ ≥ -16 · log 2 ≈ -11.09`, no entry
    rounds to zero under a shift `m` + pre-exp offset `k`. -/
theorem roundedShiftedExp_no_underflow_binarySpec8_e5m2
    {m k Δ : ℝ} {xs : List ℝ}
    (hbound : ∀ x ∈ xs, m - Δ ≤ x)
    (hsafe : -16 * Real.log 2 ≤ k - Δ) :
    ∀ x ∈ xs, roundedExp binarySpec8_e5m2.toFormat (x - m + k) ≠ 0 :=
  roundedShiftedExp_no_underflow_of_safe_offset (fmt := binarySpec8_e5m2.toFormat) hbound
    (by rw [log_minNormal_binarySpec8_e5m2]; exact hsafe)

end Flean
