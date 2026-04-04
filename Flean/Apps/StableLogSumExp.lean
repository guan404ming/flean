import Mathlib.Data.List.MinMax
import Flean.Apps.KahanSum

/-!
# Flean.Apps.StableLogSumExp

Stable `log-sum-exp` skeleton built on verified chunked reduction.

This file does not attempt to verify polynomial / table implementations of
`exp` and `log`. Instead, it proves the reduction skeleton that a CPP paper
would want first:

1. choose a shift `m` dominating all inputs
2. prove every shifted exponent satisfies `0 < exp(x - m) ≤ 1`
3. reduce these positive terms with verified chunked Kahan reduction
4. conclude that the `log` argument is strictly positive and the chunked
   implementation computes the exact reduction target under the assumed input
   contract for the reduction layer

This is the natural bridge from the compensated-reduction story to a future
full `softmax/log-sum-exp` verification.
-/

namespace Flean

/-- Blockwise collection of shifted exponentials. -/
noncomputable def shiftedExpBlocks (m : ℝ) (xss : List (List ℝ)) : List (List ℝ) :=
  xss.map (fun xs => xs.map (fun x => Real.exp (x - m)))

/-- Exact target reduced by stable blockwise `log-sum-exp`. -/
noncomputable def shiftedExpBlockSum (m : ℝ) (xss : List (List ℝ)) : ℝ :=
  ((shiftedExpBlocks m xss).map List.sum).sum

/-- Stable blockwise `log-sum-exp` powered by chunked Kahan reduction. -/
noncomputable def stableLogSumExpBlocks (fmt : FloatFormat) (m : ℝ) (xss : List (List ℝ)) : ℝ :=
  m + Real.log (kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)))

/-- `m` dominates every element in the block collection. -/
def BlocksDominatedBy (m : ℝ) (xss : List (List ℝ)) : Prop :=
  ∀ xs ∈ xss, ∀ x ∈ xs, x ≤ m

/-- The block collection contains at least one actual element. -/
def BlocksNonempty (xss : List (List ℝ)) : Prop :=
  ∃ xs ∈ xss, xs ≠ []

theorem exp_shift_nonneg_of_dominated {m x : ℝ} (hxm : x ≤ m) :
    x - m ≤ 0 := by linarith

theorem exp_shift_pos_of_dominated {m x : ℝ} (_hxm : x ≤ m) :
    0 < Real.exp (x - m) := by
  exact Real.exp_pos (x - m)

theorem exp_shift_le_one_of_dominated {m x : ℝ} (hxm : x ≤ m) :
    Real.exp (x - m) ≤ 1 := by
  have hnonpos : x - m ≤ 0 := by linarith
  calc
    Real.exp (x - m) ≤ Real.exp 0 := by
      exact Real.exp_le_exp.mpr hnonpos
    _ = 1 := by simp

theorem shiftedExpBlocks_terms_pos {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) :
    ∀ xs ∈ shiftedExpBlocks m xss, ∀ y ∈ xs, 0 < y := by
  intro xs hxs y hy
  rcases List.mem_map.mp hxs with ⟨raw, hraw, rfl⟩
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact exp_shift_pos_of_dominated (hdom raw hraw x hx)

theorem shiftedExpBlocks_terms_le_one {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) :
    ∀ xs ∈ shiftedExpBlocks m xss, ∀ y ∈ xs, y ≤ 1 := by
  intro xs hxs y hy
  rcases List.mem_map.mp hxs with ⟨raw, hraw, rfl⟩
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact exp_shift_le_one_of_dominated (hdom raw hraw x hx)

private theorem list_sum_pos_of_exists_pos {xs : List ℝ}
    (hne : xs ≠ []) (hpos : ∀ x ∈ xs, 0 < x) :
    0 < xs.sum := by
  induction xs with
  | nil =>
      contradiction
  | cons x xs ih =>
      cases xs with
      | nil =>
          simpa using hpos x (by simp)
      | cons y ys =>
          have hx : 0 < x := hpos x (by simp)
          have htail : 0 < (y :: ys).sum := by
            apply ih
            · simp
            · intro z hz
              exact hpos z (by simp [hz])
          simpa [List.sum_cons] using add_pos hx htail

private theorem list_sum_nonneg {xs : List ℝ}
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hnonneg x (by simp)
      have htail : 0 ≤ xs.sum := by
        apply ih
        intro y hy
        exact hnonneg y (by simp [hy])
      simpa [List.sum_cons] using add_nonneg hx htail

private theorem list_sum_pos_of_mem_pos {xs : List ℝ}
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    ∀ {a : ℝ}, a ∈ xs → 0 < a → 0 < xs.sum := by
  induction xs with
  | nil =>
      intro a hmem
      cases hmem
  | cons y ys ih =>
      intro a hmem hapos
      simp at hmem
      rcases hmem with rfl | hmem
      · have htail : 0 ≤ ys.sum := by
          apply list_sum_nonneg
          intro z hz
          exact hnonneg z (by simp [hz])
        simpa [List.sum_cons] using add_pos_of_pos_of_nonneg hapos htail
      · have hy : 0 ≤ y := hnonneg y (by simp)
        have htail : 0 < ys.sum := by
          apply ih
          · intro z hz
            exact hnonneg z (by simp [hz])
          · exact hmem
          · exact hapos
        simpa [List.sum_cons] using add_pos_of_nonneg_of_pos hy htail

theorem shiftedExpBlockSum_pos {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) (hne : BlocksNonempty xss) :
    0 < shiftedExpBlockSum m xss := by
  rcases hne with ⟨xs, hxs, hxs_ne⟩
  have hsum_pos : 0 < (xs.map (fun x => Real.exp (x - m))).sum := by
    apply list_sum_pos_of_exists_pos
    · cases hmap : xs.map (fun x => Real.exp (x - m)) with
      | nil =>
          cases xs with
          | nil => contradiction
          | cons x xs => simp at hmap
      | cons y ys => simp
    · intro y hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact exp_shift_pos_of_dominated (hdom xs hxs x hx)
  have hmem :
      (xs.map (fun x => Real.exp (x - m))).sum ∈ (shiftedExpBlocks m xss).map List.sum := by
    apply List.mem_map.mpr
    exact ⟨xs.map (fun x => Real.exp (x - m)), by
      apply List.mem_map.mpr
      exact ⟨xs, hxs, rfl⟩, rfl⟩
  have hall_nonneg : ∀ z ∈ (shiftedExpBlocks m xss).map List.sum, 0 ≤ z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨ys, hys, rfl⟩
    apply list_sum_nonneg
    intro y hy
    exact le_of_lt ((shiftedExpBlocks_terms_pos hdom) ys hys y hy)
  exact list_sum_pos_of_mem_pos hall_nonneg hmem hsum_pos

theorem chunkedKahan_shiftedExp_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss)) :
    kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)) = shiftedExpBlockSum m xss := by
  simpa [shiftedExpBlockSum] using chunkedKahanSum_exact (fmt := fmt) hβ hin

theorem stableLogSumExpBlocks_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss))
    (_hdom : BlocksDominatedBy m xss)
    (_hne : BlocksNonempty xss) :
    stableLogSumExpBlocks fmt m xss = m + Real.log (shiftedExpBlockSum m xss) := by
  have hexact := chunkedKahan_shiftedExp_exact (fmt := fmt) hβ hin
  unfold stableLogSumExpBlocks
  rw [hexact]

theorem stableLogSumExpBlocks_log_arg_pos {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss))
    (hdom : BlocksDominatedBy m xss)
    (hne : BlocksNonempty xss) :
    0 < kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)) := by
  rw [chunkedKahan_shiftedExp_exact (fmt := fmt) hβ hin]
  exact shiftedExpBlockSum_pos hdom hne

end Flean
