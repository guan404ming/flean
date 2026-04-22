import Flean.Apps.ML.StableLogSumExp

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

end Flean
