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

/-- Target: softmax entry is Lipschitz in the logit with constant at most 2
    under `L∞` perturbation. Used to bound the effect of K-cache quantization
    on attention scores via composition with `Q · δK` bound.

    Proof plan (TODO): shift both logit lists to the same reference, expand
    `exp(xᵢ + δᵢ) = exp(xᵢ) · exp(δᵢ)` with `exp(δᵢ) ∈ [exp(-ε), exp(ε)]`, then
    bound the ratio `(softmax perturbed)/(softmax original)` by
    `exp(2ε)` (numerator up, denominator down). Use `exp(2ε) - 1 ≤ 2ε · exp(2ε)`
    and `softmaxEntry ≤ 1` to conclude. -/
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
  sorry

/- TODO: `attention_K_sensitivity` — to be stated once Q/K matrix
   abstractions and Cauchy-Schwarz composition are wired in. Combining
   `softmaxEntry_lipschitz` with Cauchy-Schwarz on `Q · δK`, the attention
   score perturbation is bounded by `‖Q‖₂ · ‖δK‖₂`, giving the attention
   output a linear (not exp-amplified) dependence on K-cache quantization
   error, matching the V-Lipschitz result. -/

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
